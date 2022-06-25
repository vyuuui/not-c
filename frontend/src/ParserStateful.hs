module ParserStateful where

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import CompilerShared
import Control.Monad
import Control.Monad.Loops ( iterateUntilM, whileM_, whileM, untilM )
import Control.Monad.Trans
import Control.Monad.Trans.State.Lazy
import Data.Maybe
import Debug.Trace
import Lexer
import System.IO

type Program = ([FunctionDefinition], [StructDefinition])
type ParameterList = [(DataType, String)]

loadAndParse :: String -> IO Program
loadAndParse file = do
    handle <- openFile file ReadMode
    contents <- hGetContents handle
    case parseProg contents of
        Just prog -> return prog
        Nothing -> error "Bad program nat!"

raiseFailure :: ParseAction a
raiseFailure = lift Nothing

-- Lexes a new token, adding it to the LexerState
-- Returns the newly lexed token
lexNewToken :: ParseAction Token
lexNewToken = do
    ParseState (cacheTok, progStr) typeEnv funcs structs <- get
    let (newTok, restProg) = lexStringSingle typeEnv progStr
    put $ ParseState (cacheTok ++ [newTok], restProg) typeEnv funcs structs
    return newTok

scanToken :: ParseAction Token
scanToken = do
    ParseState (cacheTok, progStr) typeEnv funcs structs <- get
    case cacheTok of
        headTok:restTok -> do
            put $ ParseState (restTok, progStr) typeEnv funcs structs
            return headTok
        _               -> do
            lexNewToken
            state popToken

eatToken :: ParseAction ()
eatToken = void scanToken

peekToken :: ParseAction Token
peekToken = do
    ParseState (cacheTok, progStr) _ _ _ <- get
    case cacheTok of
        headTok:restTok -> do
            return headTok
        _               -> lexNewToken

peekTwoToken :: ParseAction (Token, Token)
peekTwoToken = do
    ParseState (cacheTok, progStr) _ _ _ <- get
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
extractInner (TypeName s)    = s
extractInner (Operator s)    = s
extractInner (Control s)     = s
extractInner (Punctuation s) = s
extractInner _               = error "Invalid call"

-- Generic helpers to validate a token given a predicate (and extract)
extractStrIfValid :: (Token -> Bool) -> Token -> ParseAction String
extractStrIfValid check token =
    if check token
      then return (extractInner token)
      else raiseFailure
checkTokenPredicate :: (Token -> Bool) -> Token -> ParseAction ()
checkTokenPredicate check token = unless (check token) raiseFailure

-- Helpers to validate several tokens, raises error if validation fails
extractTypeNameIfValid :: Token -> ParseAction String
extractTypeNameIfValid = extractStrIfValid isTypeName
extractIdentifierIfValid :: Token -> ParseAction String
extractIdentifierIfValid = extractStrIfValid isIdentifier
extractOperatorIfValid :: Token -> ParseAction String
extractOperatorIfValid = extractStrIfValid isOperator
extractConstantIfValid :: Token -> ParseAction ConstantType
extractConstantIfValid (Constant val) = return val
extractConstantIfValid _              = raiseFailure
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
scanTypeName :: ParseAction String
scanTypeName = scanToken >>= extractTypeNameIfValid
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

parseProg :: String -> Maybe Program
parseProg progStr =
    fmap (\finalState -> (funcList finalState, structList finalState)) (execStateT whatToExecute (initialState progStr))
  where
    whatToExecute = whileM_ shouldContinueParse parseTopLevel

parseTopLevel :: ParseAction ()
parseTopLevel = do
    token <- peekToken
    case token of 
        Keyword "struct" -> parseAndInsertStruct
        TypeName _ -> parseAndInsertFunction
        _ -> raiseFailure
  where
    parseAndInsertFunction :: ParseAction ()
    parseAndInsertFunction = do
        func <- parseFunction
        ParseState lexer env funcs structs <- get
        put $ ParseState lexer env (funcs ++ [func]) structs
    parseAndInsertStruct :: ParseAction ()
    parseAndInsertStruct = do
        struct@(StructDefinition (name, _)) <- parseStruct
        ParseState lexer env funcs structs <- get
        put $ ParseState lexer (S.insert name env) funcs (structs ++ [struct])

parseStruct :: ParseAction StructDefinition
parseStruct = do
    eatKeyword "struct"
    id <- scanIdentifier
    eatPunctuation "{"
    structMembers <- whileM (isTypeName <$> peekToken) parseStructMember
    eatPunctuation "}"
    return $ StructDefinition (id, structMembers)
  where
    parseStructMember :: ParseAction (DataType, String)
    parseStructMember = do
        memberType <- parseType
        id <- scanIdentifier
        eatPunctuation ";"
        return (memberType, id)

-- Return a parsed function as a SyntaxNode
parseFunction :: ParseAction FunctionDefinition 
parseFunction = do
    typeName <- parseType
    id <- scanIdentifier
    eatPunctuation "("
    paramList <- parseParamList
    eatPunctuation ")"
    blockNode <- parseBlock
    return $ FunctionDefinition typeName id paramList blockNode


parseParamList :: ParseAction ParameterList
parseParamList = do
    typeToken <- peekToken
    if isTypeName typeToken
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
    statementList <- whileM (peekToken >>= return . not . punctuationMatches "}") parseStatement 
    eatPunctuation "}"
    return $ sequenceStatements statementList
  where
    -- foldl ensures that sequence nodes are built in forward order
    sequenceStatements :: [SyntaxNode] -> SyntaxNode
    sequenceStatements = L.foldl' SeqNode EmptyNode

-- For use to determine statement option, based on the START list for each
isDecl :: Token -> Bool
isDecl = isTypeName
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
parseStatement = peekToken >>= parseStatementLookahead
  where
    parseStatementLookahead :: Token -> ParseAction SyntaxNode
    parseStatementLookahead lookahead
        | isDecl lookahead        = do
            node <- parseDeclaration
            eatPunctuation ";"
            return node
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
        | isBreak lookahead    = do
            eatControl "break"
            eatPunctuation ";"
            return BreakNode
        | otherwise               = raiseFailure

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
parseForInit = peekToken >>= parseForInitLookahead
  where
    parseForInitLookahead :: Token -> ParseAction SyntaxNode
    parseForInitLookahead lookahead
        | isDecl lookahead                 = parseDeclaration
        | isExpression lookahead           = parseExpression
        | punctuationMatches ";" lookahead = return EmptyNode
        | otherwise                        = raiseFailure

parseForExpr :: ParseAction SyntaxNode
parseForExpr = peekToken >>= parseForExprLookahead
  where
    parseForExprLookahead :: Token -> ParseAction SyntaxNode
    parseForExprLookahead lookahead
        | isExpression lookahead           = parseExpression
        | punctuationMatches ";" lookahead ||
          punctuationMatches ")" lookahead = return EmptyNode
        | otherwise                        = raiseFailure

parseForLoop :: ParseAction SyntaxNode
parseForLoop = do
    eatControl "for"
    eatPunctuation "("
    forInit <- parseForInit
    eatPunctuation ";"
    forCond <- parseForExpr
    eatPunctuation ";"
    forExpr <- parseForExpr
    eatPunctuation ")"
    block <- parseBlock
    return $ ForNode forInit forCond forExpr block

parseDeclaration :: ParseAction SyntaxNode
parseDeclaration = do
    typeName <- parseType
    id <- scanIdentifier
    nextTok <- peekToken
    case nextTok of
        Operator "=" -> do 
            eatToken
            expressionNode <- parseExpression
            return (DefinitionNode typeName id expressionNode)
        _ -> return (DeclarationNode typeName id)

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
scanAssignmentOperator = scanToken >>= \x -> unless (isAssignmentOperator x) raiseFailure

parseAssignment :: ParseAction SyntaxNode
parseAssignment = do
    startState <- get
    let dryRun = runStateT (parseLvalue >> scanAssignmentOperator) startState
    if isJust dryRun
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
    case () of _ 
                | operatorMatches "-" maybeOp -> do
                  eatToken
                  subUnary <- parseUnary
                  return $ UnaryOpNode Negate subUnary
                | operatorMatches "!" maybeOp -> do
                  eatToken
                  subUnary <- parseUnary
                  return $ UnaryOpNode Not subUnary
                | operatorMatches "&" maybeOp -> do
                  eatToken
                  subUnary <- parseUnary
                  return $ UnaryOpNode Reference subUnary
                | operatorMatches "*" maybeOp -> do
                  eatToken
                  subUnary <- parseUnary
                  return $ UnaryOpNode Dereference subUnary
                | otherwise -> parseIndirection

parseIndirection :: ParseAction SyntaxNode
parseIndirection = do
    (lookahead, lookahead2) <- peekTwoToken
    if isIdentifier lookahead && punctuationMatches "(" lookahead2
      then parseCall >>= tryParseArray
      else parseBaseExpr >>= tryParseArray
  where
    parseCall = do
        id <- scanIdentifier
        eatPunctuation "("
        argList <- parseArgList
        eatPunctuation ")"
        return $ FunctionCallNode id argList
    tryParseArray node = do
        arrayIdxs <- whileM (punctuationMatches "[" <$> peekToken) parseArrayIndex 
        return $ foldl buildArrayIdxs node arrayIdxs
      where
        -- Parses a single ", typename identifier"
        parseArrayIndex :: ParseAction SyntaxNode
        parseArrayIndex = do
            eatPunctuation "["
            arrayIdx <- parseExpression
            eatPunctuation "]"
            return arrayIdx
        buildArrayIdxs :: SyntaxNode -> SyntaxNode -> SyntaxNode
        buildArrayIdxs = ArrayIndexNode
    
parseBaseExpr :: ParseAction SyntaxNode
parseBaseExpr = do
    lookahead <- peekToken
    case () of _
                | isIdentifier lookahead           -> parseId
                | isConstant lookahead             -> parseConstant
                | punctuationMatches "(" lookahead -> parseParenthesis
                | otherwise                        -> raiseFailure
  where
    parseId = do
        id <- scanIdentifier
        return $ IdentifierNode id
    parseConstant = do 
        const <- scanConstant
        return $ LiteralNode const
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

parseType :: ParseAction DataType
parseType = do
    basicType <- scanTypeName
    ptrLevels <- whileM (operatorMatches "*" <$> peekToken) (eatToken >> return 0)
    arrLevels <- whileM (punctuationMatches "[" <$> peekToken) parseArrayDecl
    return (basicType, reverse $ ptrLevels ++ arrLevels)
  where
    parseArrayDecl :: ParseAction Int
    parseArrayDecl = do
        eatPunctuation "["
        constant <- scanConstant
        case constant of
            IntConstant v -> do
                eatPunctuation "]"
                return (fromIntegral v)
            _             -> raiseFailure

{-
prog = toplevel
toplevel = function | structdecl
function = type identifier '(' paramlist ')' block
structdecl = 'struct' identifier '{' member* '}'
member = type identifier ';'
paramlist = type identifier (',' type identifier)* | ε
block = '{' stmt* '}'
stmt = declaration ';' | block | expression ';' | conditional | forloop | whileloop | ret ';' | 'continue' ';' | 'break' ';'
declaration = type identifier optassign
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
indirection = identifier '(' arglist ')' ('[' expression ']')* | baseexpr ('[' expression ']')*
baseexpr = identifier | constant | '(' expression ')'
arglist = expression (',' expression)* | ε
type = basictype qualifier
qualifier = '*'* '[' constant ']'*
basictype = 'void' | 'char' | 'short' | 'int' | 'long' | 'float' | 'double' | 'bool'
constant = 'true' | 'false' | number
number = -?[0-9]+\.[0-9]*
identifier = [A-Za-z][A-Za-z0-9_]*
-}