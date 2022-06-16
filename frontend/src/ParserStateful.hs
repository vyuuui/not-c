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
    statementList <- untilM parseStatement (peekToken >>= return . punctuationMatches "}") 
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
            node <- parseDeclaration
            eatPunctuation ";"
            return node
        | isConditional lookahead = parseCondition
        | isLoop lookahead        = parseLoop
        | isReturn lookahead      = do
            node <- parseReturn
            eatPunctuation ";"
            return node
        | otherwise               = raiseFailure

-- TODO
parseCondition :: ParseState SyntaxNode
parseCondition = raiseFailure
{-
parseCondition :: ParseState SyntaxNode
parseCondition = do
    (_, state) <- extractStrIfValid (controlMatches "if") (scanToken state)
    (_, state) <- extractStrIfValid (punctuationMatches "(") (scanToken state)
    (expressionNode, state) <- parseExpression state
    (_, state) <- extractStrIfValid (punctuationMatches ")") (scanToken state)
    (block, originalState) <- parseBlock state
    case scanToken originalState of
        Just (Control str, state)
                                    | str == "else" -> do 
                                        (elseBlock, state) <- parseBlock state
                                        Just (IfElseNode expressionNode block elseBlock, state)
                                    | otherwise -> Nothing
        _ -> Just (IfNode expressionNode block, originalState)
-}
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

-- TODO
parseExpression :: ParseState SyntaxNode
parseExpression = raiseFailure
    
assignOpsList :: S.Set String
assignOpsList = S.fromList ["=", "+=", "-=", "*=", "/=", "%="]

isAssignmentOperator :: Token -> Bool
isAssignmentOperator (Operator op) = S.member op assignOpsList
isAssignmentOperator _             = False
    
{-
parseAssignment :: ParseState -> Maybe ParseResult
parseAssignment = do
    identifier <- scanToken
    assignTok <- scanToken
    if isIdentifier identifier && isAssignmentOperator assignTok
    then do
        let op = getAssignOp assignTok
        let id = extractInner identifier
        subExpr <- parseAssignment
        return $ AssignmentNode id op subExpr
    else parseLogicOr state
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
    case extractStrIfValid (operatorMatches "||") (scanToken state) of
        Just (_, state) -> do 
            (rightNode, state) <- parseLogicAnd state
            Just (BinaryOpNode Or node rightNode, state)
        Nothing -> Just (node, state)

parseLogicAnd :: ParseState -> Maybe ParseResult
parseLogicAnd = do
    node <- parseEqComp
    token <- peekToken
    if operatorMatches "&&" token
    then
        rightNode <- parseEqComp state
        return (BinaryOpNode And node rightNode)
    else
        return node

parseEqComp :: ParseState -> Maybe ParseResult
parseEqComp state = do
    (node, originalState) <- parseOrdComp state
    (eqToken, state) <- scanToken originalState
    case () of _
                | operatorMatches "==" eqToken -> do 
                    (rightNode, state) <- parseOrdComp state
                    Just (BinaryOpNode Equal node rightNode, state)
                | operatorMatches "!=" eqToken -> do 
                    (rightNode, state) <- parseOrdComp state
                    Just (BinaryOpNode NotEqual node rightNode, state)
                | otherwise                    -> Just (node, originalState)

parseOrdComp :: ParseState -> Maybe ParseResult
parseOrdComp state = do
    (node, originalState) <- parseAddition state
    (eqToken, state) <- scanToken originalState
    case () of _
                | operatorMatches ">" eqToken -> do 
                    (rightNode, state) <- parseAddition state
                    Just (BinaryOpNode GreaterThan node rightNode, state)
                | operatorMatches "<" eqToken -> do 
                    (rightNode, state) <- parseAddition state
                    Just (BinaryOpNode LessThan node rightNode, state)
                | operatorMatches ">=" eqToken -> do 
                    (rightNode, state) <- parseAddition state
                    Just (BinaryOpNode GreaterThanOrEqual node rightNode, state)
                | operatorMatches "<=" eqToken -> do 
                    (rightNode, state) <- parseAddition state
                    Just (BinaryOpNode LessThanOrEqual node rightNode, state)
                | otherwise                    -> Just (node, originalState)
-}