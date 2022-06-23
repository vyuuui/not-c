module ParserStateful where


import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import Data.Maybe
import Control.Monad
import Control.Monad.Loops ( iterateUntilM, whileM_, whileM, untilM )
import Control.Monad.Trans
import Control.Monad.Trans.State.Lazy
import Lexer
import System.IO
import Debug.Trace

type DataType = (String, [Int])
type Program = [SyntaxNode]
type ParseState = StateT ([Token], [SyntaxNode]) Maybe
type ParameterList = [(DataType, String)]

data SyntaxNode
    = FunctionDefinitionNode DataType String [(DataType, String)] SyntaxNode
    | EmptyNode
    -- Two sequential operations
    | SeqNode SyntaxNode SyntaxNode
    -- Control
    | WhileNode SyntaxNode SyntaxNode
    | ForNode SyntaxNode SyntaxNode SyntaxNode SyntaxNode
    | IfNode SyntaxNode SyntaxNode 
    | IfElseNode SyntaxNode SyntaxNode SyntaxNode
    | ReturnNode SyntaxNode
    | ContinueNode
    | BreakNode
    -- Decl
    | DeclarationNode DataType String
    | DefinitionNode DataType String SyntaxNode
    -- Expression
    | IdentifierNode String
    | LiteralNode ConstantType
    | FunctionCallNode String [SyntaxNode]
    | ArrayIndexNode SyntaxNode SyntaxNode
    | ParenthesisNode SyntaxNode
    | BinaryOpNode BinaryOp SyntaxNode SyntaxNode
    | UnaryOpNode UnaryOp SyntaxNode
    | AssignmentNode SyntaxNode AssignmentOp SyntaxNode
    deriving Show

data BinaryOp
    = Addition
    | Multiplication
    | Subtraction
    | Division
    | Mod
    | Equal
    | NotEqual
    | LessThan
    | GreaterThan
    | GreaterThanOrEqual
    | LessThanOrEqual
    | Or
    | And
    deriving (Show, Eq)

data AssignmentOp
    = NoOp
    | PlusEq
    | MinusEq
    | MulEq
    | DivEq
    | ModEq
    deriving (Show, Eq)

data UnaryOp
    = Negate
    | Not
    | Reference
    | Dereference
    deriving (Show, Eq)



loadAndParse :: String -> IO Program
loadAndParse file = do
    handle <- openFile file ReadMode
    contents <- hGetContents handle
    let tokens = lexString contents
    case parseProg tokens of
        Just prog -> return prog
        Nothing -> error "Bad program nat!"

raiseFailure :: ParseState a
raiseFailure = lift Nothing

scanToken :: ParseState Token
scanToken = do
    (tokList, funcList) <- get
    if null tokList
      then raiseFailure
      else do
        put (tail tokList, funcList)
        return $ head tokList

eatToken :: ParseState ()
eatToken = do
    (tokList, funcList) <- get
    if null tokList
      then raiseFailure
      else do
        put (tail tokList, funcList)
        return ()

peekToken :: ParseState Token
peekToken = do
    (tokList, funcList) <- get
    if null tokList
      then raiseFailure
      else return $ head tokList

peekTwoToken :: ParseState (Token, Token)
peekTwoToken = do
    (tokList, funcList) <- get
    case tokList of
        tok1:tok2:rest -> return (tok1, tok2)
        _              -> raiseFailure

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
extractStrIfValid :: (Token -> Bool) -> Token -> ParseState String
extractStrIfValid check token =
    if check token
      then return (extractInner token)
      else raiseFailure
checkTokenPredicate :: (Token -> Bool) -> Token -> ParseState ()
checkTokenPredicate check token = unless (check token) raiseFailure

-- Helpers to validate several tokens, raises error if validation fails
extractTypeNameIfValid :: Token -> ParseState String
extractTypeNameIfValid = extractStrIfValid isTypeName
extractIdentifierIfValid :: Token -> ParseState String
extractIdentifierIfValid = extractStrIfValid isIdentifier
extractOperatorIfValid :: Token -> ParseState String
extractOperatorIfValid = extractStrIfValid isOperator
extractConstantIfValid :: Token -> ParseState ConstantType
extractConstantIfValid (Constant val) = return val
extractConstantIfValid _              = raiseFailure
validatePunctuation :: String -> Token -> ParseState ()
validatePunctuation val = checkTokenPredicate (punctuationMatches val)
validateControl :: String -> Token -> ParseState ()
validateControl val = checkTokenPredicate (controlMatches val)
validateOperator :: String -> Token -> ParseState ()
validateOperator val = checkTokenPredicate (operatorMatches val)

-- Helpers to consume a specific token (and extract contents for id/type)
scanIdentifier :: ParseState String
scanIdentifier = scanToken >>= extractIdentifierIfValid
scanTypeName :: ParseState String
scanTypeName = scanToken >>= extractTypeNameIfValid
scanOperator :: ParseState String
scanOperator = scanToken >>= extractOperatorIfValid
scanConstant :: ParseState ConstantType
scanConstant = scanToken >>= extractConstantIfValid
eatPunctuation :: String -> ParseState ()
eatPunctuation val = scanToken >>= validatePunctuation val
eatControl :: String -> ParseState ()
eatControl val = scanToken >>= validateControl val
eatOperator :: String -> ParseState ()
eatOperator val = scanToken >>= validateOperator val


shouldContinueParse :: ParseState Bool
shouldContinueParse = do
    headToken <- peekToken
    return $ headToken /= Eof

-- Parse a function
-- once it is parsed, insert it into the state
parseAndInsertFunction :: ParseState ()
parseAndInsertFunction = do
    func <- parseFunction
    (tokList, funcList) <- get
    put (tokList, funcList ++ [func])

parseProg :: [Token] -> Maybe Program
parseProg initialList =
    fmap snd (execStateT whatToExecute initialState)
  where
    initialState = (initialList, [])
    whatToExecute = whileM_ shouldContinueParse parseAndInsertFunction

-- Return a parsed function as a SyntaxNode
parseFunction :: ParseState SyntaxNode
parseFunction = do
    typeName <- parseType
    id <- scanIdentifier
    eatPunctuation "("
    paramList <- parseParamList
    eatPunctuation ")"
    blockNode <- parseBlock
    return $ FunctionDefinitionNode typeName id paramList blockNode


parseParamList :: ParseState ParameterList
parseParamList = do
    typeToken <- peekToken
    if isTypeName typeToken
      then doActualParseParamList
      else return []
  where
    -- Parses the full param list, given there is at least one parameter
    doActualParseParamList :: ParseState ParameterList
    doActualParseParamList = do
        typeName <- parseType
        id <- scanIdentifier
        ((typeName, id):) <$> whileM (punctuationMatches "," <$> peekToken) parseCommaParam
      where
        -- Parses a single ", typename identifier"
        parseCommaParam :: ParseState (DataType, String)
        parseCommaParam = do
            eatToken
            typeName <- parseType
            id <- scanIdentifier
            return (typeName, id)

-- block = '{' stmt* '}'
parseBlock :: ParseState SyntaxNode
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

parseStatement :: ParseState SyntaxNode
parseStatement = peekToken >>= parseStatementLookahead
  where
    parseStatementLookahead :: Token -> ParseState SyntaxNode
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

parseCondition :: ParseState SyntaxNode
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

parseWhileLoop :: ParseState SyntaxNode
parseWhileLoop = do
    eatControl "while"
    eatPunctuation "("
    expressionNode <- parseExpression
    eatPunctuation ")"
    block <- parseBlock
    return (WhileNode expressionNode block)

parseForInit :: ParseState SyntaxNode
parseForInit = peekToken >>= parseForInitLookahead
  where
    parseForInitLookahead :: Token -> ParseState SyntaxNode
    parseForInitLookahead lookahead
        | isDecl lookahead                 = parseDeclaration
        | isExpression lookahead           = parseExpression
        | punctuationMatches ";" lookahead = return EmptyNode
        | otherwise                        = raiseFailure

parseForExpr :: ParseState SyntaxNode
parseForExpr = peekToken >>= parseForExprLookahead
  where
    parseForExprLookahead :: Token -> ParseState SyntaxNode
    parseForExprLookahead lookahead
        | isExpression lookahead           = parseExpression
        | punctuationMatches ";" lookahead ||
          punctuationMatches ")" lookahead = return EmptyNode
        | otherwise                        = raiseFailure

parseForLoop :: ParseState SyntaxNode
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

parseDeclaration :: ParseState SyntaxNode
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

parseReturn :: ParseState SyntaxNode
parseReturn = do
    eatControl "return"
    expressionNode <- parseExpression
    return $ ReturnNode expressionNode

parseExpression :: ParseState SyntaxNode
parseExpression = parseAssignment
    
assignOpsList :: S.Set String
assignOpsList = S.fromList ["=", "+=", "-=", "*=", "/=", "%="]

isAssignmentOperator :: Token -> Bool
isAssignmentOperator (Operator op) = S.member op assignOpsList
isAssignmentOperator _             = False

scanAssignmentOperator :: ParseState ()
scanAssignmentOperator = scanToken >>= \x -> unless (isAssignmentOperator x) raiseFailure

parseAssignment :: ParseState SyntaxNode
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

parseLvalue :: ParseState SyntaxNode
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
    :: ParseState SyntaxNode -- Subexpr parser action
    -> [(String, BinaryNodeCombinator)] -- (Operator, combinator) pairs
    -> ParseState SyntaxNode -- Root node
parseOpPrecedence parseAction opCombine = do
    init <- parseAction
    equalPrecedenceList <- whileM shouldContinue execMatched
    return $ L.foldl' (\a (node, combine) -> combine a node) init equalPrecedenceList
  where
    checks = map (\(op, combine) -> (operatorMatches op, combine)) opCombine
    shouldContinue :: ParseState Bool
    shouldContinue = do
        nextTok <- peekToken
        return $ any (($ nextTok) . fst) checks
    execMatched :: ParseState (SyntaxNode, BinaryNodeCombinator)
    execMatched = do
        nextTok <- scanToken
        let combineFn = snd $ head $ filter (($ nextTok) . fst) checks
        nextExpr <- parseAction
        return (nextExpr, combineFn) 

parseLogicOr :: ParseState SyntaxNode
parseLogicOr = parseOpPrecedence parseLogicAnd [("||", BinaryOpNode Or)]

parseLogicAnd :: ParseState SyntaxNode
parseLogicAnd = parseOpPrecedence parseEqComp [("&&", BinaryOpNode And)]

parseEqComp :: ParseState SyntaxNode
parseEqComp = parseOpPrecedence parseOrdComp [("==", BinaryOpNode Equal),
                                              ("!=", BinaryOpNode NotEqual)]

parseOrdComp :: ParseState SyntaxNode
parseOrdComp = parseOpPrecedence parseAddition [(">", BinaryOpNode GreaterThan),
                                                ("<", BinaryOpNode LessThan),
                                                (">=", BinaryOpNode GreaterThanOrEqual),
                                                ("<=", BinaryOpNode LessThanOrEqual)]

parseAddition :: ParseState SyntaxNode
parseAddition = parseOpPrecedence parseMultiplication [("+", BinaryOpNode Addition),
                                                       ("-", BinaryOpNode Subtraction)]

parseMultiplication :: ParseState SyntaxNode
parseMultiplication = parseOpPrecedence parseUnary [("*", BinaryOpNode Multiplication),
                                                    ("/", BinaryOpNode Division),
                                                    ("%", BinaryOpNode Mod)]

parseUnary :: ParseState SyntaxNode
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

parseIndirection :: ParseState SyntaxNode
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
        parseArrayIndex :: ParseState SyntaxNode
        parseArrayIndex = do
            eatPunctuation "["
            arrayIdx <- parseExpression
            eatPunctuation "]"
            return arrayIdx
        buildArrayIdxs :: SyntaxNode -> SyntaxNode -> SyntaxNode
        buildArrayIdxs = ArrayIndexNode
    
parseBaseExpr :: ParseState SyntaxNode
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
parseArgList :: ParseState ArgumentList
parseArgList = do
    maybeExpr <- peekToken
    if isExpression maybeExpr
        then doActualParseArgList
        else return []
  where
    doActualParseArgList :: ParseState ArgumentList
    doActualParseArgList = do
        firstArg <- parseExpression
        (firstArg:) <$> whileM (punctuationMatches "," <$> peekToken) parseCommaArg
      where
        parseCommaArg :: ParseState SyntaxNode
        parseCommaArg = do
            eatToken
            parseExpression

parseType :: ParseState DataType
parseType = do
    basicType <- scanTypeName
    ptrLevels <- whileM (operatorMatches "*" <$> peekToken) (eatToken >> return 0)
    arrLevels <- whileM (punctuationMatches "[" <$> peekToken) parseArrayDecl
    return (basicType, reverse $ ptrLevels ++ arrLevels)
  where
    parseArrayDecl :: ParseState Int
    parseArrayDecl = do
        eatPunctuation "["
        constant <- scanConstant
        case constant of
            IntConstant v -> do
                eatPunctuation "]"
                return (fromIntegral v)
            _             -> raiseFailure

{-
prog = function+
function = type identifier '(' paramlist ')' block
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
unary = '-' unary | '!' unary | '&' unary | '*' unary | indirection
indirection = identifier '(' arglist ')' ('[' expression ']')* | baseexpr ('[' expression ']')*
baseexpr = identifier | constant | '(' expression ')'
arglist = expression (',' expression)* | ε

while (i > 3) {
    i++;
    continue;
}


type = basictype qualifier
qualifier = '*'* '[' constant ']'*
basictype = 'void' | 'char' | 'short' | 'int' | 'long' | 'float' | 'double' | 'bool'
constant = 'true' | 'false' | number
number = -?[0-9]+\.[0-9]*
identifier = [A-Za-z][A-Za-z0-9_]*
-}