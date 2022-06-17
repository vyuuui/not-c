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

data SyntaxNode
    = FunctionDefinitionNode String String [(String, String)] SyntaxNode
    | EmptyNode
    -- Two sequential operations
    | SeqNode SyntaxNode SyntaxNode
    -- Control
    | WhileNode SyntaxNode SyntaxNode
    | IfNode SyntaxNode SyntaxNode 
    | IfElseNode SyntaxNode SyntaxNode SyntaxNode
    | ReturnNode SyntaxNode
    -- Decl
    | DeclarationNode String String
    | DefinitionNode String String SyntaxNode
    -- Expression
    | IdentifierNode String
    | LiteralNode ConstantType
    | FunctionCallNode String [SyntaxNode]
    | ParenthesisNode SyntaxNode
    | BinaryOpNode BinaryOp SyntaxNode SyntaxNode
    | UnaryOpNode UnaryOp SyntaxNode
    | AssignmentNode String AssignmentOp SyntaxNode
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
    deriving (Show, Eq)

type Program = [SyntaxNode]

type ParseState = StateT ([Token], [SyntaxNode]) Maybe

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
    typeName <- scanTypeName
    id <- scanIdentifier
    eatPunctuation "("
    paramList <- parseParamList
    eatPunctuation ")"
    blockNode <- parseBlock
    return $ FunctionDefinitionNode typeName id paramList blockNode

type ParameterList = [(String, String)]

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
        typeName <- scanTypeName
        id <- scanIdentifier
        ((typeName, id):) <$> whileM (punctuationMatches "," <$> peekToken) parseCommaParam
      where
        -- Parses a single ", typename identifier"
        parseCommaParam :: ParseState (String, String)
        parseCommaParam = do
            eatToken
            typeName <- scanTypeName
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
isExpression tok = any ($ tok) [isIdentifier, isConstant, punctuationMatches "("]
isConditional :: Token -> Bool
isConditional = controlMatches "if"
isLoop :: Token -> Bool
isLoop = controlMatches "while"
isReturn :: Token -> Bool
isReturn = controlMatches "return"
isEmpty :: Token -> Bool
isEmpty = punctuationMatches ";"

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
        | isLoop lookahead        = parseLoop
        | isReturn lookahead      = do
            node <- parseReturn
            eatPunctuation ";"
            return node
        | isEmpty lookahead       = do
            eatPunctuation ";"
            return EmptyNode
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

parseLoop :: ParseState SyntaxNode
parseLoop = do
    eatControl "while"
    eatPunctuation "("
    expressionNode <- parseExpression
    eatPunctuation ")"
    block <- parseBlock
    return (WhileNode expressionNode block)
    

parseDeclaration :: ParseState SyntaxNode
parseDeclaration = do
    typeName <- scanTypeName
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

parseAssignment :: ParseState SyntaxNode
parseAssignment = do
    (maybeId, maybeAssign) <- peekTwoToken
    if isIdentifier maybeId && isAssignmentOperator maybeAssign
      then do
        id <- scanIdentifier
        assignOp <- scanToken
        subExpr <- parseAssignment
        return $ AssignmentNode id (getAssignOp assignOp) subExpr
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
    
    
parseLogicOr :: ParseState SyntaxNode
parseLogicOr = do
    node <- parseLogicAnd
    token <- peekToken
    if operatorMatches "||" token
    then do
        eatToken
        rightNode <- parseLogicAnd
        return (BinaryOpNode Or node rightNode)
    else
        return node

parseLogicAnd :: ParseState SyntaxNode
parseLogicAnd = do
    node <- parseEqComp
    token <- peekToken
    if operatorMatches "&&" token
    then do
        eatToken
        rightNode <- parseEqComp
        return (BinaryOpNode And node rightNode)
    else
        return node

parseEqComp :: ParseState SyntaxNode
parseEqComp = do
    node <- parseOrdComp
    token <- peekToken
    case () of _
                | operatorMatches "==" token -> do 
                    eatToken
                    rightNode <- parseOrdComp
                    return (BinaryOpNode Equal node rightNode)
                | operatorMatches "!=" token -> do 
                    eatToken
                    rightNode <- parseOrdComp
                    return (BinaryOpNode NotEqual node rightNode)
                | otherwise                    -> return node

parseOrdComp :: ParseState SyntaxNode
parseOrdComp = do
    node <- parseAddition
    token <- peekToken
    case () of _
                | operatorMatches ">" token -> do 
                    eatToken
                    rightNode <- parseAddition
                    return (BinaryOpNode GreaterThan node rightNode)
                | operatorMatches "<" token -> do 
                    eatToken
                    rightNode <- parseAddition
                    return (BinaryOpNode LessThan node rightNode)
                | operatorMatches ">=" token -> do 
                    eatToken
                    rightNode <- parseAddition
                    return (BinaryOpNode GreaterThanOrEqual node rightNode)
                | operatorMatches "<=" token -> do 
                    eatToken
                    rightNode <- parseAddition
                    return (BinaryOpNode LessThanOrEqual node rightNode)
                | otherwise                    -> return node

parseAddition :: ParseState SyntaxNode
parseAddition = do
    node <- parseMultiplication
    token <- peekToken
    case () of _
                | operatorMatches "+" token -> do 
                    eatToken
                    rightNode <- parseMultiplication
                    return (BinaryOpNode Addition node rightNode)
                | operatorMatches "-" token -> do 
                    eatToken
                    rightNode <- parseMultiplication
                    return (BinaryOpNode Subtraction node rightNode)
                | otherwise                    -> return node

parseMultiplication :: ParseState SyntaxNode
parseMultiplication = do
    node <- parseUnary
    token <- peekToken
    case () of _
                | operatorMatches "*" token -> do 
                    eatToken
                    rightNode <- parseUnary
                    return (BinaryOpNode Multiplication node rightNode)
                | operatorMatches "/" token -> do 
                    eatToken
                    rightNode <- parseUnary
                    return (BinaryOpNode Division node rightNode)
                | operatorMatches "%" token -> do 
                    eatToken
                    rightNode <- parseUnary
                    return (BinaryOpNode Mod node rightNode)
                | otherwise                    -> return node


parseUnary :: ParseState SyntaxNode
parseUnary = do
    maybeOp <- peekToken
    case () of _ 
                | operatorMatches "-" maybeOp -> do
                    scanToken
                    baseExpr <- parseBaseExpr
                    return $ UnaryOpNode Negate baseExpr
                | operatorMatches "!" maybeOp -> do
                    scanToken
                    baseExpr <- parseBaseExpr
                    return $ UnaryOpNode Not baseExpr
                | otherwise -> parseBaseExpr

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
        maybeParen <- peekToken
        if punctuationMatches "(" maybeParen
            then parseCall id
            else return $ IdentifierNode id
    parseCall id = do
        eatPunctuation "("
        argList <- parseArgList
        eatPunctuation ")"
        return $ FunctionCallNode id argList
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
