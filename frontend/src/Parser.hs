module Parser where

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import CompilerShared
import Control.Monad
import Control.Monad.Loops ( iterateUntilM, whileM_, whileM, untilM )
import Control.Monad.Trans
import Control.Monad.Trans.State.Lazy
import Data.Either
import Data.Functor
import Debug.Trace
import Lexer
import System.IO

type ParameterList = [(DataType, String)]

loadAndParse :: String -> IO Program
loadAndParse file = do
    handle <- openFile file ReadMode
    contents <- hGetContents handle
    case parseProg contents of
        Right prog -> return prog
        Left msg -> error ("Bad program nat! msg=" ++ msg)

getTypeEnv :: ParseAction TypeEnv
getTypeEnv = typeEnv <$> get
getLexerState :: ParseAction LexerState
getLexerState = lexerState <$> get
getSymbolMap :: ParseAction SymbolMap
getSymbolMap = symbolMap <$> get

pushSymbolEnv :: ParseAction ()
pushSymbolEnv = do
    ParseState lexer typeEnv funcs structs syms <- get
    put $ ParseState lexer typeEnv funcs structs (M.empty:syms)

popSymbolEnv :: ParseAction ()
popSymbolEnv = do
    ParseState lexer typeEnv funcs structs syms <- get
    put $ ParseState lexer typeEnv funcs structs (tail syms)

insertSymbol :: String -> SymbolType -> ParseAction ()
insertSymbol symName sym = do
    when (S.member symName baseTypes) (raiseFailure $ "Can't declare reserved typename " ++ symName)
    ParseState lexer typeEnv funcs structs syms <- get
    put $ ParseState lexer typeEnv funcs structs (M.insert symName sym (head syms) : tail syms)

-- Lexes a new token, adding it to the LexerState
-- Returns the newly lexed token
lexNewToken :: ParseAction Token
lexNewToken = do
    ParseState (cacheTok, progStr) typeEnv funcs structs syms <- get
    let (newTok, restProg) = lexStringSingle typeEnv progStr
    put $ ParseState (cacheTok ++ [newTok], restProg) typeEnv funcs structs syms
    return newTok

scanToken :: ParseAction Token
scanToken = do
    ParseState (cacheTok, progStr) typeEnv funcs structs syms <- get
    case cacheTok of
        headTok:restTok -> do
            put $ ParseState (restTok, progStr) typeEnv funcs structs syms
            return headTok
        _               -> do
            lexNewToken
            state popToken

eatToken :: ParseAction ()
eatToken = void scanToken

peekToken :: ParseAction Token
peekToken = do
    ParseState (cacheTok, progStr) _ _ _ _ <- get
    case cacheTok of
        headTok:restTok -> do
            return headTok
        _               -> lexNewToken

peekTwoToken :: ParseAction (Token, Token)
peekTwoToken = do
    ParseState (cacheTok, progStr) _ _ _ _ <- get
    case cacheTok of
        tok1:tok2:restTok -> return (tok1, tok2)
        [tok1]            -> do
            tok2 <- lexNewToken
            return (tok1, tok2)
        _                 -> do
            tok1 <- lexNewToken
            tok2 <- lexNewToken
            return (tok1, tok2)

-- Helper to unwrap the String part of certain tokens
-- error should never be hit, as below helpers should avoid invalid calls
extractInner :: Token -> String
extractInner (Identifier s)  = s
extractInner (Operator s)    = s
extractInner (Control s)     = s
extractInner (Punctuation s) = s
extractInner _               = error "Invalid call"

-- Generic helpers to validate a token given a predicate (and extract)
extractStrIfValid :: (Token -> Bool) -> Token -> ParseAction String
extractStrIfValid check token =
    if check token
      then return (extractInner token)
      else raiseFailure "Failed to extract valid token"
checkTokenPredicate :: (Token -> Bool) -> Token -> ParseAction ()
checkTokenPredicate check token = unless (check token) (raiseFailure "Token validation failed")

-- Helpers to validate several tokens, raises error if validation fails
extractIdentifierIfValid :: Token -> ParseAction String
extractIdentifierIfValid = extractStrIfValid isIdentifier
extractOperatorIfValid :: Token -> ParseAction String
extractOperatorIfValid = extractStrIfValid isOperator
extractConstantIfValid :: Token -> ParseAction ConstantType
extractConstantIfValid (Constant val) = return val
extractConstantIfValid _              = raiseFailure "Expected constant token"
validatePunctuation :: String -> Token -> ParseAction ()
validatePunctuation val = checkTokenPredicate (punctuationMatches val)
validateControl :: String -> Token -> ParseAction ()
validateControl val = checkTokenPredicate (controlMatches val)
validateOperator :: String -> Token -> ParseAction ()
validateOperator val = checkTokenPredicate (operatorMatches val)
validateKeyword :: String -> Token -> ParseAction ()
validateKeyword val = checkTokenPredicate (keywordMatches val)

-- Helpers to consume a specific token (and extract contents for id/type)
scanIdentifier :: ParseAction String
scanIdentifier = scanToken >>= extractIdentifierIfValid
scanOperator :: ParseAction String
scanOperator = scanToken >>= extractOperatorIfValid
scanConstant :: ParseAction ConstantType
scanConstant = scanToken >>= extractConstantIfValid
eatPunctuation :: String -> ParseAction ()
eatPunctuation val = scanToken >>= validatePunctuation val
eatControl :: String -> ParseAction ()
eatControl val = scanToken >>= validateControl val
eatOperator :: String -> ParseAction ()
eatOperator val = scanToken >>= validateOperator val
eatKeyword :: String -> ParseAction ()
eatKeyword val = scanToken >>= validateKeyword val


shouldContinueParse :: ParseAction Bool
shouldContinueParse = do
    headToken <- peekToken
    return $ headToken /= Eof

parseProg :: String -> Either String Program
parseProg progStr =
    fmap (\finalState -> (funcList finalState, structList finalState)) (execStateT whatToExecute (initialState progStr))
  where
    whatToExecute = whileM_ shouldContinueParse parseTopLevel

parseTopLevel :: ParseAction ()
parseTopLevel = do
    token <- peekToken
    case token of 
        Keyword "struct" -> parseAndInsertStruct
        Identifier _ -> parseAndInsertFunction
        _ -> raiseFailure "Unexpected top level token"
  where
    parseAndInsertFunction :: ParseAction ()
    parseAndInsertFunction = do
        func <- parseFunction
        ParseState lexer env funcs structs syms <- get
        put $ ParseState lexer env (funcs ++ [func]) structs syms
    parseAndInsertStruct :: ParseAction ()
    parseAndInsertStruct = do
        struct@(StructDefinition (name, _)) <- parseStruct
        ParseState lexer env funcs structs syms <- get
        put $ ParseState lexer (S.insert name env) funcs (structs ++ [struct]) syms

parseStruct :: ParseAction StructDefinition
parseStruct = do
    syms <- getSymbolMap
    eatKeyword "struct"
    id <- scanIdentifier
    insertSymbol id TypeSym
    eatPunctuation "{"
    structMembers <- whileM (isTypeName syms <$> peekToken) parseStructMember
    eatPunctuation "}"
    return $ StructDefinition (id, structMembers)
  where
    parseStructMember :: ParseAction (DataType, String)
    parseStructMember = do
        (memberTypeName, memberPtrList) <- parseType
        id <- scanIdentifier
        arrayList <- parseArraySpec
        eatPunctuation ";"
        return ((memberTypeName, arrayList ++ memberPtrList), id)

-- Return a parsed function as a SyntaxNode
parseFunction :: ParseAction FunctionDefinition 
parseFunction = do
    typeName <- parseType
    id <- scanIdentifier
    insertSymbol id FuncSym 
    pushSymbolEnv
    eatPunctuation "("
    paramList <- parseParamList
    eatPunctuation ")"
    blockNode <- parseBlock
    popSymbolEnv
    return $ FunctionDefinition typeName id paramList blockNode


parseParamList :: ParseAction ParameterList
parseParamList = do
    typeToken <- peekToken
    syms <- getSymbolMap
    if isTypeName syms typeToken
    then doActualParseParamList
      else return []
  where
    -- Parses the full param list, given there is at least one parameter
    doActualParseParamList :: ParseAction ParameterList
    doActualParseParamList = do
        typeName <- parseType
        id <- scanIdentifier
        ((typeName, id):) <$> whileM (punctuationMatches "," <$> peekToken) parseCommaParam
      where
        -- Parses a single ", typename identifier"
        parseCommaParam :: ParseAction (DataType, String)
        parseCommaParam = do
            eatToken
            typeName <- parseType
            id <- scanIdentifier
            return (typeName, id)

-- block = '{' stmt* '}'
parseBlock :: ParseAction SyntaxNode
parseBlock = do
    eatPunctuation "{"
    pushSymbolEnv
    statementList <- whileM (peekToken <&> not . punctuationMatches "}") parseStatement 
    popSymbolEnv
    eatPunctuation "}"
    return $ sequenceStatements statementList
  where
    -- foldl ensures that sequence nodes are built in forward order
    sequenceStatements :: [SyntaxNode] -> SyntaxNode
    sequenceStatements = L.foldl' SeqNode EmptyNode

isTypeName :: SymbolMap -> Token -> Bool
isTypeName smap (Identifier id) = getIdentifierType id smap == TypeSym
isTypeName _ _                  = False
-- For use to determine statement option, based on the START list for each
isBlock :: Token -> Bool
isBlock = punctuationMatches "{"
isExpression :: Token -> Bool
isExpression tok = any ($ tok) [isIdentifier, isConstant, punctuationMatches "(",
                                operatorMatches "!", operatorMatches "&", operatorMatches "*",
                                operatorMatches "-"]
isLvalue :: Token -> Bool
isLvalue tok = any ($ tok) [isIdentifier, isConstant, punctuationMatches "(", punctuationMatches "*" ]
isConditional :: Token -> Bool
isConditional = controlMatches "if"
isWhileLoop :: Token -> Bool
isWhileLoop = controlMatches "while"
isForLoop :: Token -> Bool
isForLoop = controlMatches "for"
isReturn :: Token -> Bool
isReturn = controlMatches "return"
isEmpty :: Token -> Bool
isEmpty = punctuationMatches ";"
isContinue :: Token -> Bool 
isContinue = controlMatches "continue"
isBreak :: Token -> Bool 
isBreak = controlMatches "break"

parseStatement :: ParseAction SyntaxNode
parseStatement = do
    tok <- peekToken
    smap <- getSymbolMap
    env <- getTypeEnv
    if isTypeName smap tok
        then parseDeclaration
        else parseStatementLookahead env tok
  where
    parseStatementLookahead :: TypeEnv -> Token -> ParseAction SyntaxNode
    parseStatementLookahead env lookahead
        | isBlock lookahead       = parseBlock
        | isExpression lookahead  = do
            node <- parseExpression
            eatPunctuation ";"
            return node
        | isConditional lookahead = parseCondition
        | isWhileLoop lookahead   = parseWhileLoop
        | isForLoop lookahead     = parseForLoop
        | isReturn lookahead      = do
            node <- parseReturn
            eatPunctuation ";"
            return node
        | isEmpty lookahead       = do
            eatPunctuation ";"
            return EmptyNode
        | isContinue lookahead    = do
            eatControl "continue"
            eatPunctuation ";"
            return ContinueNode
        | isBreak lookahead       = do
            eatControl "break"
            eatPunctuation ";"
            return BreakNode
        | otherwise               = raiseFailure "Unexpected token when parsing statement"

parseCondition :: ParseAction SyntaxNode
parseCondition = do
    eatControl "if"
    eatPunctuation "("
    expressionNode <- parseExpression
    eatPunctuation ")"
    block <- parseBlock
    maybeElse <- peekToken
    if controlMatches "else" maybeElse
        then do
            eatControl "else"
            elseBlock <- parseBlock
            return $ IfElseNode expressionNode block elseBlock
        else return $ IfNode expressionNode block

parseWhileLoop :: ParseAction SyntaxNode
parseWhileLoop = do
    eatControl "while"
    eatPunctuation "("
    expressionNode <- parseExpression
    eatPunctuation ")"
    block <- parseBlock
    return (WhileNode expressionNode block)

parseForInit :: ParseAction SyntaxNode
parseForInit = getSymbolMap >>= \syms -> peekToken >>= parseForInitLookahead syms
  where
    parseForInitLookahead :: SymbolMap -> Token -> ParseAction SyntaxNode
    parseForInitLookahead syms lookahead
        | isTypeName syms lookahead        = parseDeclaration
        | isExpression lookahead           = parseExpression
        | punctuationMatches ";" lookahead = return EmptyNode
        | otherwise                        = raiseFailure "Unexpected token in for loop init"

parseForExpr :: ParseAction SyntaxNode
parseForExpr = peekToken >>= parseForExprLookahead
  where
    parseForExprLookahead :: Token -> ParseAction SyntaxNode
    parseForExprLookahead lookahead
        | isExpression lookahead           = parseExpression
        | punctuationMatches ";" lookahead ||
          punctuationMatches ")" lookahead = return EmptyNode
        | otherwise                        = raiseFailure "Unexpected token in for loop expression"

parseForLoop :: ParseAction SyntaxNode
parseForLoop = do
    pushSymbolEnv
    eatControl "for"
    eatPunctuation "("
    forInit <- parseForInit
    eatPunctuation ";"
    forCond <- parseForExpr
    eatPunctuation ";"
    forExpr <- parseForExpr
    eatPunctuation ")"
    block <- parseBlock
    popSymbolEnv
    return $ ForNode forInit forCond forExpr block

parseDeclaration :: ParseAction SyntaxNode
parseDeclaration = do
    (typeName, ptrList) <- parseType
    id <- scanIdentifier
    arrayList <- parseArraySpec
    nextTok <- peekToken
    case nextTok of
        Operator "=" -> do 
            eatToken
            expressionNode <- parseExpression
            insertSymbol id VarSym
            return (DefinitionNode (typeName, arrayList ++ ptrList) id expressionNode)
        _            -> do 
            insertSymbol id VarSym
            return (DeclarationNode (typeName, arrayList ++ ptrList) id)

parseReturn :: ParseAction SyntaxNode
parseReturn = do
    eatControl "return"
    expressionNode <- parseExpression
    return $ ReturnNode expressionNode

parseExpression :: ParseAction SyntaxNode
parseExpression = parseAssignment
    
assignOpsList :: S.Set String
assignOpsList = S.fromList ["=", "+=", "-=", "*=", "/=", "%="]

isAssignmentOperator :: Token -> Bool
isAssignmentOperator (Operator op) = S.member op assignOpsList
isAssignmentOperator _             = False

scanAssignmentOperator :: ParseAction ()
scanAssignmentOperator = scanToken >>= \x -> unless (isAssignmentOperator x) (raiseFailure "Expected assignment token operator")

parseAssignment :: ParseAction SyntaxNode
parseAssignment = do
    startState <- get
    let dryRun = runStateT (parseLvalue >> scanAssignmentOperator) startState
    if isRight dryRun
      then do
        lhs <- parseLvalue
        assignOp <- scanToken
        subExpr <- parseAssignment
        return $ AssignmentNode lhs (getAssignOp assignOp) subExpr
      else parseLogicOr
  where
    getAssignOp (Operator o)
        | o == "="  = NoOp
        | o == "+=" = PlusEq
        | o == "-=" = MinusEq
        | o == "*=" = MulEq
        | o == "/=" = DivEq
        | o == "%=" = ModEq
        | otherwise = error "getAssignOp should never receive an invalid assign operator"
    getAssignOp _ = error "getAssignOp should never receive an invalid assign operator"

parseLvalue :: ParseAction SyntaxNode
parseLvalue = do
    token <- peekToken
    if operatorMatches "*" token
    then do
        eatToken
        indirectionNode <- parseLvalue
        return (UnaryOpNode Dereference indirectionNode)
    else
        parseIndirection

type BinaryNodeCombinator = SyntaxNode -> SyntaxNode -> SyntaxNode

parseOpPrecedence
    :: ParseAction SyntaxNode -- Subexpr parser action
    -> [(String, BinaryNodeCombinator)] -- (Operator, combinator) pairs
    -> ParseAction SyntaxNode -- Root node
parseOpPrecedence parseAction opCombine = do
    init <- parseAction
    equalPrecedenceList <- whileM shouldContinue execMatched
    return $ L.foldl' (\a (node, combine) -> combine a node) init equalPrecedenceList
  where
    checks = map (\(op, combine) -> (operatorMatches op, combine)) opCombine
    shouldContinue :: ParseAction Bool
    shouldContinue = do
        nextTok <- peekToken
        return $ any (($ nextTok) . fst) checks
    execMatched :: ParseAction (SyntaxNode, BinaryNodeCombinator)
    execMatched = do
        nextTok <- scanToken
        let combineFn = snd $ head $ filter (($ nextTok) . fst) checks
        nextExpr <- parseAction
        return (nextExpr, combineFn) 

parseLogicOr :: ParseAction SyntaxNode
parseLogicOr = parseOpPrecedence parseLogicAnd [("||", BinaryOpNode Or)]

parseLogicAnd :: ParseAction SyntaxNode
parseLogicAnd = parseOpPrecedence parseEqComp [("&&", BinaryOpNode And)]

parseEqComp :: ParseAction SyntaxNode
parseEqComp = parseOpPrecedence parseOrdComp [("==", BinaryOpNode Equal),
                                              ("!=", BinaryOpNode NotEqual)]

parseOrdComp :: ParseAction SyntaxNode
parseOrdComp = parseOpPrecedence parseAddition [(">", BinaryOpNode GreaterThan),
                                                ("<", BinaryOpNode LessThan),
                                                (">=", BinaryOpNode GreaterThanOrEqual),
                                                ("<=", BinaryOpNode LessThanOrEqual)]

parseAddition :: ParseAction SyntaxNode
parseAddition = parseOpPrecedence parseMultiplication [("+", BinaryOpNode Addition),
                                                       ("-", BinaryOpNode Subtraction)]

parseMultiplication :: ParseAction SyntaxNode
parseMultiplication = parseOpPrecedence parseUnary [("*", BinaryOpNode Multiplication),
                                                    ("/", BinaryOpNode Division),
                                                    ("%", BinaryOpNode Mod)]

parseUnary :: ParseAction SyntaxNode
parseUnary = do
    maybeOp <- peekToken
    if | operatorMatches "-" maybeOp -> do
             eatToken
             UnaryOpNode Negate <$> parseUnary
       | operatorMatches "!" maybeOp -> do
             eatToken
             UnaryOpNode Not <$> parseUnary
       | operatorMatches "&" maybeOp -> do
             eatToken
             UnaryOpNode Reference <$> parseUnary
       | operatorMatches "*" maybeOp -> do
             eatToken
             UnaryOpNode Dereference <$> parseUnary
       | otherwise -> parseIndirection

parseIndirection :: ParseAction SyntaxNode
parseIndirection = do
    (lookahead, lookahead2) <- peekTwoToken
    if isIdentifier lookahead && punctuationMatches "(" lookahead2
      then parseCall >>= tryParseArray >>= tryParseMemberAccess
      else parseBaseExpr >>= tryParseArray >>= tryParseMemberAccess
  where
    parseCall :: ParseAction SyntaxNode
    parseCall = do
        id <- scanIdentifier
        eatPunctuation "("
        argList <- parseArgList
        eatPunctuation ")"
        return $ FunctionCallNode id argList
    tryParseArray :: SyntaxNode -> ParseAction SyntaxNode
    tryParseArray node = do
        arrayIdxs <- whileM (punctuationMatches "[" <$> peekToken) parseArrayIndex 
        return $ L.foldl' ArrayIndexNode node arrayIdxs
      where
        -- Parses a single ", typename identifier"
        parseArrayIndex :: ParseAction SyntaxNode
        parseArrayIndex = do
            eatPunctuation "["
            arrayIdx <- parseExpression
            eatPunctuation "]"
            return arrayIdx
    tryParseMemberAccess :: SyntaxNode -> ParseAction SyntaxNode
    tryParseMemberAccess node = do
        memberAccesses <- whileM (continueParsingMembers <$> peekToken) parseMemberAccess 
        return $ L.foldl' foldMemberAccess node memberAccesses
      where
        foldMemberAccess :: SyntaxNode -> (SyntaxNode, Bool) -> SyntaxNode
        foldMemberAccess x (node, isPtr) = MemberAccessNode isPtr x node
        continueParsingMembers :: Token -> Bool
        continueParsingMembers token = operatorMatches "." token || operatorMatches "->" token
        -- Parses a single ". identifier ('[' expression ']')*"
        parseMemberAccess :: ParseAction (SyntaxNode, Bool)
        parseMemberAccess = do
            lookahead <- peekToken
            if | operatorMatches "." lookahead  -> do
                     eatOperator "."
                     idNode <- scanIdentifier <&> IdentifierNode
                     tryParseArray idNode >>= \rhs -> return (rhs, False)
               | operatorMatches "->" lookahead -> do
                     eatOperator "->"
                     idNode <- scanIdentifier <&> IdentifierNode
                     tryParseArray idNode >>= \rhs -> return (rhs, True)
               | otherwise                      -> raiseFailure "Unexpected token when parsing member access"

parseBaseExpr :: ParseAction SyntaxNode
parseBaseExpr = do
    lookahead <- peekToken
    if | isIdentifier lookahead           -> parseId
       | isConstant lookahead             -> parseConstant
       | punctuationMatches "(" lookahead -> parseParenthesis
       | otherwise                        -> raiseFailure "Unexpected type in base expression"
  where
    parseId :: ParseAction SyntaxNode
    parseId = IdentifierNode <$> scanIdentifier
    parseConstant :: ParseAction SyntaxNode
    parseConstant = LiteralNode <$> scanConstant 
    parseParenthesis :: ParseAction SyntaxNode
    parseParenthesis = do
        eatPunctuation "("
        expr <- parseExpression
        eatPunctuation ")"
        return expr

type ArgumentList = [SyntaxNode]
parseArgList :: ParseAction ArgumentList
parseArgList = do
    maybeExpr <- peekToken
    if isExpression maybeExpr
        then doActualParseArgList
        else return []
  where
    doActualParseArgList :: ParseAction ArgumentList
    doActualParseArgList = do
        firstArg <- parseExpression
        (firstArg:) <$> whileM (punctuationMatches "," <$> peekToken) parseCommaArg
      where
        parseCommaArg :: ParseAction SyntaxNode
        parseCommaArg = do
            eatToken
            parseExpression

parseArraySpec :: ParseAction [Int]
parseArraySpec = do
    whileM (punctuationMatches "[" <$> peekToken) parseArrayDecl
  where
    parseArrayDecl :: ParseAction Int
    parseArrayDecl = do
        eatPunctuation "["
        constant <- scanConstant
        case constant of
            IntConstant v -> do
                eatPunctuation "]"
                when (v <= 0) (raiseFailure "Array sizes must be greater than 0")
                return (fromIntegral v)
            _             -> raiseFailure "Non-integer type used in array index"

parseType :: ParseAction DataType
parseType = do
    typeName <- scanIdentifier
    ptrLevels <- whileM (operatorMatches "*" <$> peekToken) (eatToken $> 0)
    return (typeName, ptrLevels)
  

{-
prog = toplevel
toplevel = function | structdecl
function = type identifier '(' paramlist ')' block
structdecl = 'struct' identifier '{' member* '}'
member = type identifier arrayspec ';'
paramlist = type identifier (',' type identifier)* | ε
block = '{' stmt* '}'
stmt = declaration ';' | block | expression ';' | conditional | forloop | whileloop | ret ';' | 'continue' ';' | 'break' ';'
declaration = type identifier arrayspec optassign
optassign = '=' expression | ε
whileloop = 'while' '(' expression ')' block
forinit = declaration | assignment | ε
forexpr = expression | ε
forloop = 'for' '(' forinit ';' forexpr ';' forexpr ')' block
conditional = 'if' '(' expression ')' block elseconditional
elseconditional = 'else' block | ε
ret = 'return' expression
expression = assignment
assignment = lvalue '=' assignment  | lvalue '+=' assignment |
             lvalue '-=' assignment | lvalue '*=' assignment |
             lvalue '/=' assignment | lvalue '%=' assignment | logicor
lvalue = '*' lvalue | indirection
logicor = logicand ('||' logicand)*
logicand = eqcomp ('&&' eqcomp)*
eqcomp = ordcomp ('==' ordcomp)* | ordcomp ('!=' orcomp)*
ordcomp = addition ('<' addition)* | addition ('>' addition)* | addition ('<=' addition)* | addition ('>=' addition)*
addition = multiplication ('+' multiplication)* | multiplication ('-' multiplication)*
multiplication = unary ('*' unary)* | unary ('/' unary)* | unary ('%' unary)*
unary = '-' unary | '!' unary | '&' unary | '*' unary | '(' type ')' | indirection
indirection = identifier '(' arglist ')' ('[' expression ']')* memberaccess*
            | baseexpr ('[' expression ']')* memberaccess* 
memberaccess = '.' identifier ('[' expression ']')*
baseexpr = identifier | constant | '(' expression ')'
arglist = expression (',' expression)* | ε
type = identifier qualifier
qualifier = '*'*
arrayspec = '[' constant ']'*
constant = 'true' | 'false' | number
number = -?[0-9]+\.[0-9]*
identifier = [A-Za-z][A-Za-z0-9_]*
-}
