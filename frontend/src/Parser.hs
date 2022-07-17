module Parser where

import CompilerShared
import CompilerShow
import Control.Arrow
import Control.Monad
import Control.Monad.Loops ( iterateUntilM, whileM_, whileM, untilM )
import Control.Monad.Trans
import Control.Monad.Trans.State.Lazy
import Data.Either
import Data.Functor
import Debug.Trace
import Lexer
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

-- Raise a failure from the current node's start lex position to the last lexed position
raiseFailureHere :: String -> ParseAction a
raiseFailureHere why = join $ raiseFailurePrecise why <$> (currentNodeLexStart <$> get) <*> getPrevLexPosition <*> getLexPosition

getTypeEnv :: ParseAction TypeEnv
getTypeEnv = typeEnv <$> get
getLexerState :: ParseAction LexerState
getLexerState = lexerState <$> get
getSymbolMap :: ParseAction SymbolMap
getSymbolMap = symbolMap <$> get

pushSymbolEnv, popSymbolEnv :: ParseAction ()
pushSymbolEnv = do
    ParseState lexer typeEnv funcs structs syms lp <- get
    put $ ParseState lexer typeEnv funcs structs (M.empty:syms) lp
popSymbolEnv = do
    ParseState lexer typeEnv funcs structs syms lp <- get
    put $ ParseState lexer typeEnv funcs structs (tail syms) lp

getLexPosition, getPrevLexPosition :: ParseAction Int
getLexPosition = do
    (t, rest, (clt, plt)) <- getLexerState
    return clt
getPrevLexPosition = do
    (t, rest, (clt, plt)) <- getLexerState
    return plt

setCurrentLexStart :: Int -> ParseAction ()
setCurrentLexStart pos = do
    ParseState lexer typeEnv funcs structs syms _ <- get
    put $ ParseState lexer typeEnv funcs structs syms pos

insertSymbol :: String -> SymbolType -> ParseAction ()
insertSymbol symName sym = do
    when (S.member symName baseTypes) (raiseFailureHere $ "Can't declare reserved typename " ++ symName)
    ParseState lexer typeEnv funcs structs syms lp <- get
    put $ ParseState lexer typeEnv funcs structs (M.insert symName sym (head syms) : tail syms) lp

-- Lexes a new token, adding it to the LexerState
-- Returns the newly lexed token
lexNewToken :: ParseAction Token
lexNewToken = do
    ParseState (cacheTok, progStr, clt) typeEnv funcs structs syms lp <- get
    let (newTok, numParsed, restProg) = lexStringSingle typeEnv progStr
    put $ ParseState (cacheTok ++ [(newTok, numParsed)], restProg, clt) typeEnv funcs structs syms lp
    return newTok

scanToken :: ParseAction Token
scanToken = do
    ParseState (cacheTok, progStr, clt) typeEnv funcs structs syms _ <- get
    when (null cacheTok) (void lexNewToken)
    state popToken

eatToken :: ParseAction ()
eatToken = void scanToken

peekToken :: ParseAction Token
peekToken = do
    (cacheTok, _, _) <- getLexerState
    if null cacheTok
    then lexNewToken
    else return $ fst (head cacheTok)

peekTwoToken :: ParseAction (Token, Token)
peekTwoToken = do
    (cacheTok, _, _) <- getLexerState
    case cacheTok of
        tok1:tok2:restTok -> return (fst tok1, fst tok2)
        [tok1]            -> do
            tok2 <- lexNewToken
            return (fst tok1, tok2)
        _                 -> do
            tok1 <- lexNewToken
            tok2 <- lexNewToken
            return (tok1, tok2)

-- Generic helpers to validate a token given a predicate (and extract)
extractStrIfValid :: (Token -> Bool) -> String -> Token -> ParseAction String
extractStrIfValid check tokenClass token =
    if check token
      then return (extractInner token)
      else raiseFailureHere $ "Tried to extract " ++ tokenClass ++ ", but got " ++ show token
  where
    extractInner :: Token -> String
    extractInner (Identifier s)  = s
    extractInner (Operator s)    = s
    extractInner (Control s)     = s
    extractInner (Punctuation s) = s
    extractInner _               = ""

checkTokenPredicate :: (Token -> Bool) -> String -> Token -> ParseAction ()
checkTokenPredicate check expected token =
    unless
      (check token)
      (raiseFailureHere $ "Expected \"" ++ expected ++ "\" but got " ++ show token)

-- Helpers to validate several tokens, raises error if validation fails
extractIdentifierIfValid :: Token -> ParseAction String
extractIdentifierIfValid = extractStrIfValid isIdentifier "identifier"
extractOperatorIfValid :: Token -> ParseAction String
extractOperatorIfValid = extractStrIfValid isOperator "operator"
extractConstantIfValid :: Token -> ParseAction ConstantType
extractConstantIfValid (Constant val) = return val
extractConstantIfValid val              = raiseFailureHere $ "Expected constant but got " ++ show val
validatePunctuation :: String -> Token -> ParseAction ()
validatePunctuation val = checkTokenPredicate (punctuationMatches val) val
validateControl :: String -> Token -> ParseAction ()
validateControl val = checkTokenPredicate (controlMatches val) val
validateOperator :: String -> Token -> ParseAction ()
validateOperator val = checkTokenPredicate (operatorMatches val) val
validateKeyword :: String -> Token -> ParseAction ()
validateKeyword val = checkTokenPredicate (keywordMatches val) val

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



parseProg :: String -> Either FailureInfo Program
parseProg progStr =
    fmap (\finalState -> (funcList finalState, structList finalState)) (execStateT whatToExecute (initialState progStr))
  where
    whatToExecute = whileM_ (not . isEof <$> peekToken) parseTopLevel

parseTopLevel :: ParseAction ()
parseTopLevel = do
    token <- peekToken
    case token of 
        Keyword "struct" -> parseAndInsertStruct
        Identifier _ -> parseAndInsertFunction
        _ -> eatToken >> raiseFailureHere ("Unexpected top level token " ++ show token)
  where
    parseAndInsertFunction :: ParseAction ()
    parseAndInsertFunction = do
        func <- parseFunction
        ParseState lexer env funcs structs syms lp <- get
        put $ ParseState lexer env (funcs ++ [func]) structs syms lp
    parseAndInsertStruct :: ParseAction ()
    parseAndInsertStruct = do
        lp <- getLexPosition
        setCurrentLexStart lp
        struct@(name, _) <- parseStruct
        lp <- getLexPosition
        setCurrentLexStart lp
        ParseState lexer env funcs structs syms lp <- get
        put $ ParseState lexer (S.insert name env) funcs (structs ++ [struct]) syms lp

parseStruct :: ParseAction StructDefinition
parseStruct = do
    syms <- getSymbolMap
    eatKeyword "struct"
    id <- scanIdentifier
    insertSymbol id TypeSym
    eatPunctuation "{"
    structMembers <- whileM (isTypeName syms <$> peekToken) parseStructMember
    eatPunctuation "}"
    return (id, structMembers)
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
    (typeBegin, typeName) <- seqPair (getLexPosition, parseType)
    (idBegin, id, idEnd) <- seqTrip (getLexPosition, scanIdentifier, getLexPosition)
    insertSymbol id FuncSym 
    pushSymbolEnv
    eatPunctuation "("
    (paramList, paramLocs) <- parseParamList
    eatPunctuation ")"
    blockNode <- doAnnotateSyntax parseBlock
    popSymbolEnv
    let fAnnot = FunctionAnnotation
         { returnTypeLoc = SourceLoc typeBegin idBegin
         , funcNameLoc = SourceLoc idBegin idEnd
         , paramsLoc = paramLocs
         }
    return $ FunctionDefinition typeName id paramList blockNode fAnnot


parseParamList :: ParseAction (DeclList, [SourceLoc])
parseParamList = do
    typeToken <- peekToken
    syms <- getSymbolMap
    if isTypeName syms typeToken
      then doActualParseParamList
      else return ([], [])
  where
    -- Parses the full param list, given there is at least one parameter
    doActualParseParamList :: ParseAction (DeclList, [SourceLoc])
    doActualParseParamList = do
        paramBeg <- getLexPosition
        typeName <- parseType
        id <- scanIdentifier
        paramEnd <- getLexPosition
        let loc = SourceLoc paramBeg paramEnd
        -- Prepend the first parameter (type, id, loc) onto the remaining parameters
        unzip . (((typeName, id), loc):) <$> whileM (punctuationMatches "," <$> peekToken) parseCommaParam
      where
        -- Parses a single ", typename identifier"
        parseCommaParam :: ParseAction ((DataType, String), SourceLoc)
        parseCommaParam = do
            eatToken
            paramBeg <- getLexPosition
            typeName <- parseType
            id <- scanIdentifier
            paramEnd <- getLexPosition
            let loc = SourceLoc paramBeg paramEnd
            return ((typeName, id), loc)

-- block = '{' stmt* '}'
parseBlock :: ParseAction (SyntaxNodeF SyntaxNode)
parseBlock = do
    eatPunctuation "{"
    pushSymbolEnv
    statementList <- whileM (peekToken <&> not . punctuationMatches "}") (doAnnotateSyntax parseStatement)
    popSymbolEnv
    eatPunctuation "}"
    return $ BlockNode $ sequenceStatements statementList
  where
    -- foldl ensures that sequence nodes are built in forward order
    sequenceStatements :: [SyntaxNode] -> SyntaxNode
    sequenceStatements = L.foldl' (\a x -> copyAnnot x $ SeqNode a x) (annotSyntaxEmpty EmptyNode)

isTypeName :: SymbolMap -> Token -> Bool
isTypeName smap (Identifier id) = getIdentifierType id smap == TypeSym
isTypeName _ _                  = False
-- For use to determine statement option, based on the START list for each
isBlock, isExpression, isLvalue, isConditional, isWhileLoop, isForLoop, isReturn, isEmpty, isContinue, isBreak, isPrint :: Token -> Bool
isBlock = punctuationMatches "{"
isExpression tok = any ($ tok) [isIdentifier, isConstant, punctuationMatches "(",
                                operatorMatches "!", operatorMatches "&", operatorMatches "*",
                                operatorMatches "-", operatorMatches "++", operatorMatches "--"]
isLvalue tok = any ($ tok) [isIdentifier, isConstant, punctuationMatches "(", punctuationMatches "*" ]
isConditional = controlMatches "if"
isWhileLoop = controlMatches "while"
isForLoop = controlMatches "for"
isReturn = controlMatches "return"
isEmpty = punctuationMatches ";"
isContinue = controlMatches "continue"
isBreak = controlMatches "break"
isPrint = keywordMatches "print"

parseStatement :: ParseAction (SyntaxNodeF SyntaxNode)
parseStatement = do
    tok <- peekToken
    smap <- getSymbolMap
    env <- getTypeEnv
    if isTypeName smap tok
      then parseDeclaration >>= \x -> eatPunctuation ";" >> return x
      else parseStatementLookahead env tok
  where
    parseStatementLookahead :: TypeEnv -> Token -> ParseAction (SyntaxNodeF SyntaxNode)
    parseStatementLookahead env lookahead
        | isBlock lookahead       = parseBlock
        | isExpression lookahead  = do
            node <- parseWrapExpression
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
        | isPrint lookahead       = do
            eatKeyword "print"
            expressionNode <- doAnnotateSyntax parseWrapExpression
            eatPunctuation ";"
            return $ PrintNode expressionNode
        | otherwise               = raiseFailureHere $ "Unexpected token " ++ show lookahead ++ " when parsing statement"

doAnnotateSyntax :: ParseAction (SyntaxNodeF SyntaxNode) -> ParseAction SyntaxNode
doAnnotateSyntax action = do
    startPos <- getLexPosition
    setCurrentLexStart startPos
    rawNode <- action
    endPos <- getLexPosition
    return $ annotSyntax startPos endPos rawNode

doAnnotateExpr :: ParseAction (ExprF Expr) -> ParseAction Expr
doAnnotateExpr action = do
    startPos <- getLexPosition
    setCurrentLexStart startPos
    rawNode <- action
    endPos <- getLexPosition
    return $ annotExprLoc (SourceLoc startPos endPos) rawNode

parseCondition :: ParseAction (SyntaxNodeF SyntaxNode)
parseCondition = do
    eatControl "if"
    eatPunctuation "("
    expressionNode <- doAnnotateSyntax parseWrapExpression
    eatPunctuation ")"
    block <- doAnnotateSyntax parseBlock
    (maybeElse, maybeIf) <- peekTwoToken
    if | controlMatches "else" maybeElse && controlMatches "if" maybeIf -> do
           eatControl "else"
           elseBlock <- doAnnotateSyntax parseCondition
           return $ IfElseNode expressionNode block elseBlock
       | controlMatches "else" maybeElse -> do
           eatControl "else"
           elseBlock <- doAnnotateSyntax parseBlock
           return $ IfElseNode expressionNode block elseBlock
       | otherwise -> return $ IfNode expressionNode block

parseWhileLoop :: ParseAction (SyntaxNodeF SyntaxNode)
parseWhileLoop = do
    eatControl "while"
    eatPunctuation "("
    expressionNode <- doAnnotateSyntax parseWrapExpression
    eatPunctuation ")"
    block <- doAnnotateSyntax parseBlock
    return $ WhileNode expressionNode block

parseForInit :: ParseAction (SyntaxNodeF SyntaxNode)
parseForInit = getSymbolMap >>= \syms -> peekToken >>= parseForInitLookahead syms
  where
    parseForInitLookahead :: SymbolMap -> Token -> ParseAction (SyntaxNodeF SyntaxNode)
    parseForInitLookahead syms lookahead
        | isTypeName syms lookahead        = parseDeclaration
        | isExpression lookahead           = parseWrapExpression
        | punctuationMatches ";" lookahead = return EmptyNode
        | otherwise                        = raiseFailureHere "Unexpected token in for loop init"

parseForExpr :: ParseAction (SyntaxNodeF SyntaxNode)
parseForExpr = peekToken >>= parseForExprLookahead
  where
    parseForExprLookahead :: Token -> ParseAction (SyntaxNodeF SyntaxNode)
    parseForExprLookahead lookahead
        | isExpression lookahead           = parseWrapExpression
        | punctuationMatches ";" lookahead ||
          punctuationMatches ")" lookahead = return EmptyNode
        | otherwise                        = raiseFailureHere "Unexpected token in for loop expression"

parseForLoop :: ParseAction (SyntaxNodeF SyntaxNode)
parseForLoop = do
    pushSymbolEnv
    eatControl "for"
    eatPunctuation "("
    forInit <- doAnnotateSyntax parseForInit
    eatPunctuation ";"
    forCond <- doAnnotateSyntax parseForExpr
    eatPunctuation ";"
    forExpr <- doAnnotateSyntax parseForExpr
    eatPunctuation ")"
    block <- doAnnotateSyntax parseBlock
    popSymbolEnv
    return $ ForNode forInit forCond forExpr block

parseDeclaration :: ParseAction (SyntaxNodeF SyntaxNode)
parseDeclaration = do
    (typeName, ptrList) <- parseType
    id <- scanIdentifier
    arrayList <- parseArraySpec
    nextTok <- peekToken
    case nextTok of
        Operator "=" -> do 
            eatToken
            expressionNode <- doAnnotateSyntax parseWrapExpression
            insertSymbol id VarSym
            return $ DefinitionNode (typeName, arrayList ++ ptrList) id expressionNode
        _            -> do 
            insertSymbol id VarSym
            return $ DeclarationNode (typeName, arrayList ++ ptrList) id

parseReturn :: ParseAction (SyntaxNodeF SyntaxNode)
parseReturn = do
    eatControl "return"
    lookahead <- peekToken
    if punctuationMatches ";" lookahead
      then return $ ReturnNode $ annotSyntaxEmpty EmptyNode
      else ReturnNode <$> doAnnotateSyntax parseWrapExpression

parseWrapExpression :: ParseAction (SyntaxNodeF SyntaxNode)
parseWrapExpression = ExprNode <$> doAnnotateExpr parseExpression

parseExpression :: ParseAction (ExprF Expr)
parseExpression = parseAssignment
    
assignOpsList :: S.Set String
assignOpsList = S.fromList ["=", "+=", "-=", "*=", "/=", "%="]

isAssignmentOperator :: Token -> Bool
isAssignmentOperator (Operator op) = S.member op assignOpsList
isAssignmentOperator _             = False

scanAssignmentOperator :: ParseAction ()
scanAssignmentOperator = scanToken >>= \x -> unless (isAssignmentOperator x) (raiseFailureHere "Expected assignment token operator")

parseAssignment :: ParseAction (ExprF Expr)
parseAssignment = do
    startState <- get
    let dryRun = runStateT (parseLvalue >> scanAssignmentOperator) startState
    if isRight dryRun
      then do
        lhs <- doAnnotateExpr parseLvalue
        assignOp <- scanToken
        AssignmentNode (getAssignOp assignOp) lhs <$> doAnnotateExpr parseAssignment
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

parseLvalue :: ParseAction (ExprF Expr)
parseLvalue = do
    token <- peekToken
    if operatorMatches "*" token
    then do
        eatToken
        UnaryOpNode Dereference <$> doAnnotateExpr parseLvalue
    else
        parseIndirection

type BinaryNodeCombinator = Expr -> Expr -> ExprF Expr

parseOpPrecedence
    :: ParseAction (ExprF Expr) -- Subexpr parser action
    -> [(String, BinaryNodeCombinator)] -- (Operator, combinator) pairs
    -> ParseAction (ExprF Expr) -- Root node
parseOpPrecedence parseAction opCombine = do
    init <- doAnnotateExpr parseAction
    equalPrecedenceList <- whileM shouldContinue execMatched
    let rootNode = L.foldl' (\a (node, combine) -> annotExprLoc (getBounds a node) (combine a node)) init equalPrecedenceList
    -- Sorry for this future me
    return $ getExprF rootNode
  where
    checks = map (first operatorMatches) opCombine
    shouldContinue :: ParseAction Bool
    shouldContinue = do
        nextTok <- peekToken
        return $ any (($ nextTok) . fst) checks
    execMatched :: ParseAction (Expr, BinaryNodeCombinator)
    execMatched = do
        nextTok <- scanToken
        let combineFn = snd $ head $ filter (($ nextTok) . fst) checks
        nextExpr <- doAnnotateExpr parseAction
        return (nextExpr, combineFn) 

getBounds :: Expr -> Expr -> SourceLoc
getBounds left right = SourceLoc (srcBegin $ sourceLocOf left) (srcEnd $ sourceLocOf right)

parseLogicOr :: ParseAction (ExprF Expr)
parseLogicOr = parseOpPrecedence parseLogicAnd [("||", BinaryOpNode Or)]

parseLogicAnd :: ParseAction (ExprF Expr)
parseLogicAnd = parseOpPrecedence parseEqComp [("&&", BinaryOpNode And)]

parseEqComp :: ParseAction (ExprF Expr)
parseEqComp = parseOpPrecedence parseOrdComp [("==", BinaryOpNode Equal),
                                              ("!=", BinaryOpNode NotEqual)]

parseOrdComp :: ParseAction (ExprF Expr)
parseOrdComp = parseOpPrecedence parseAddition [(">", BinaryOpNode GreaterThan),
                                                ("<", BinaryOpNode LessThan),
                                                (">=", BinaryOpNode GreaterThanOrEqual),
                                                ("<=", BinaryOpNode LessThanOrEqual)]

parseAddition :: ParseAction (ExprF Expr)
parseAddition = parseOpPrecedence parseMultiplication [("+", BinaryOpNode Addition),
                                                       ("-", BinaryOpNode Subtraction)]

parseMultiplication :: ParseAction (ExprF Expr)
parseMultiplication = parseOpPrecedence parseUnary [("*", BinaryOpNode Multiplication),
                                                    ("/", BinaryOpNode Division),
                                                    ("%", BinaryOpNode Modulus)]

parseUnary :: ParseAction (ExprF Expr)
parseUnary = do
    maybeOp <- peekToken
    if | operatorMatches "-" maybeOp -> do
             eatToken
             UnaryOpNode Negate <$> doAnnotateExpr parseUnary
       | operatorMatches "!" maybeOp -> do
             eatToken
             UnaryOpNode Not <$> doAnnotateExpr parseUnary
       | operatorMatches "&" maybeOp -> do
             eatToken
             UnaryOpNode Reference <$> doAnnotateExpr parseUnary
       | operatorMatches "*" maybeOp -> do
             eatToken
             UnaryOpNode Dereference <$> doAnnotateExpr parseUnary
       | operatorMatches "++" maybeOp -> do
             eatToken
             UnaryOpNode PrefixInc <$> doAnnotateExpr parseUnary
       | operatorMatches "--" maybeOp -> do
             eatToken
             UnaryOpNode PrefixDec <$> doAnnotateExpr parseUnary
       | otherwise -> parseIndirection

parseIndirection :: ParseAction (ExprF Expr)
parseIndirection = do
    (lookahead, lookahead2) <- peekTwoToken
    rootExpr <- if isIdentifier lookahead && punctuationMatches "(" lookahead2
                  then doAnnotateExpr parseCall
                  else doAnnotateExpr parseBaseExpr
    parseIndirectionTrail rootExpr
  where
    parseCall :: ParseAction (ExprF Expr)
    parseCall = do
        id <- scanIdentifier
        eatPunctuation "("
        argList <- parseArgList
        eatPunctuation ")"
        return $ FunctionCallNode id argList

parseIndirectionTrail :: Expr -> ParseAction (ExprF Expr)
parseIndirectionTrail root = do
    lookahead <- peekToken
    if | operatorMatches "++" lookahead -> parsePost PostInc
       | operatorMatches "--" lookahead ->  parsePost PostDec
       | operatorMatches "." lookahead -> parseMemberAccess False
       | operatorMatches "->" lookahead -> parseMemberAccess True
       | punctuationMatches "[" lookahead ->  parseSubscript
       | otherwise -> return $ getExprF root
  where
    parsePost :: PostfixOp -> ParseAction (ExprF Expr)
    parsePost op = do
        eatToken
        doAnnotateExpr (return $ PostfixOpNode op root) >>= parseIndirectionTrail 
    parseMemberAccess :: Bool -> ParseAction (ExprF Expr)
    parseMemberAccess isPtr = do
        eatToken
        member <- doAnnotateExpr $ StructMemberNode <$> scanIdentifier
        doAnnotateExpr (return $ MemberAccessNode isPtr root member) >>= parseIndirectionTrail
    parseSubscript :: ParseAction (ExprF Expr)
    parseSubscript = do
        eatToken
        trace "Parsing subscript" return ()
        idx <- doAnnotateExpr parseExpression
        eatPunctuation "]"
        doAnnotateExpr (return $ ArrayIndexNode root idx) >>= parseIndirectionTrail

parseBaseExpr :: ParseAction (ExprF Expr)
parseBaseExpr = do
    lookahead <- peekToken
    if | isIdentifier lookahead           -> parseId
       | isConstant lookahead             -> parseConstant
       | punctuationMatches "(" lookahead -> parseParenthesis
       | otherwise                        -> raiseFailureHere "Unexpected token in base expression"
  where
    parseId :: ParseAction (ExprF Expr)
    parseId = IdentifierNode <$> scanIdentifier
    parseConstant :: ParseAction (ExprF Expr)
    parseConstant = LiteralNode <$> scanConstant 
    parseParenthesis :: ParseAction (ExprF Expr)
    parseParenthesis = do
        eatPunctuation "("
        expr <- doAnnotateExpr parseExpression
        eatPunctuation ")"
        return $ ParenthesisNode expr

type ArgumentList = [Expr]
parseArgList :: ParseAction ArgumentList
parseArgList = do
    maybeExpr <- peekToken
    if isExpression maybeExpr
        then doActualParseArgList
        else return []
  where
    doActualParseArgList :: ParseAction ArgumentList
    doActualParseArgList = do
        firstArg <- doAnnotateExpr parseExpression
        (firstArg:) <$> whileM (punctuationMatches "," <$> peekToken) parseCommaArg
      where
        parseCommaArg :: ParseAction Expr
        parseCommaArg = do
            eatToken
            doAnnotateExpr parseExpression

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
                when (v <= 0) (raiseFailureHere "Array sizes must be greater than 0")
                return (fromIntegral v)
            _             -> raiseFailureHere "Non-constant/integral size used in array declaration"

parseType :: ParseAction DataType
parseType = do
    typeName <- scanIdentifier
    ptrLevels <- whileM (operatorMatches "*" <$> peekToken) (eatToken $> 0)
    return (typeName, ptrLevels)
  
-- print x;
{-
prog = toplevel
toplevel = function | structdecl
function = type identifier '(' paramlist ')' block
structdecl = 'struct' identifier '{' member* '}'
member = type identifier arrayspec ';'
paramlist = type identifier (',' type identifier)* | ε
block = '{' stmt* '}'
stmt = declaration ';' | block | expression ';' | conditional |
       forloop | whileloop | ret ';' | 'continue' ';' | 'break' ';' | print expression ';'
declaration = type identifier arrayspec optassign
optassign = '=' expression | ε
whileloop = 'while' '(' expression ')' block
forinit = declaration | assignment | ε
forexpr = expression | ε
forloop = 'for' '(' forinit ';' forexpr ';' forexpr ')' block
conditional = 'if' '(' expression ')' block elseconditional
elseconditional = 'else' 'if' block elseconditional | 'else' block | ε
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
unary = '-' unary | '!' unary | '&' unary | '*' unary | '(' type ')' |
        '++' unary | '--' unary | indirection
indirection = identifier '(' arglist ')' indirection_rest |
              baseexpr indirection_rest 
indirection_trail = '++' indirection_trail |
                    '--' indirection_trail |
                    '.' identifier indirection_trail |
                    '[' expression ']' indirection_trail |
                    ε
baseexpr = identifier | constant | '(' expression ')'
arglist = expression (',' expression)* | ε
type = identifier qualifier
qualifier = '*'*
arrayspec = '[' constant ']'*
constant = 'true' | 'false' | number
number = -?[0-9]+\.[0-9]*
identifier = [A-Za-z][A-Za-z0-9_]*
-}
