module ParserStateful where


import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import Data.Maybe
import Control.Monad
import Control.Monad.Loops ( iterateUntilM, whileM_, whileM )
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

peekToken :: ParseState Token
peekToken = do
    (tokList, funcList) <- get
    if null tokList
      then raiseFailure
      else return $ head tokList

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

extractInner :: Token -> String
extractInner (Identifier s)  = s
extractInner (TypeName s)    = s
extractInner (Operator s)    = s
extractInner (Control s)     = s
extractInner (Punctuation s) = s
extractInner _               = error "Invalid call"

validateStr :: (Token -> Bool) -> Token -> ParseState String
validateStr check token =
    if check token
      then return (extractInner token)
      else raiseFailure

validateStrTypeName :: Token -> ParseState String
validateStrTypeName = validateStr isTypeName

validateStrIdentifier :: Token -> ParseState String
validateStrIdentifier = validateStr isIdentifier

validatePunctuation :: String -> Token -> ParseState String
validatePunctuation val = validateStr (punctuationMatches val)

validateControl :: String -> Token -> ParseState String
validateControl val = validateStr (controlMatches val)

validateOperator :: String -> Token -> ParseState String
validateOperator val = validateStr (operatorMatches val)

-- Return a parsed function as a SyntaxNode
parseFunction :: ParseState SyntaxNode
parseFunction = do
    typeName <- scanToken >>= validateStrTypeName
    id <- scanToken >>= validateStrIdentifier
    scanToken >>= validatePunctuation "("
    paramList <- parseParamList
    scanToken >>= validatePunctuation ")"
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
    doActualParseParamList :: ParseState ParameterList
    doActualParseParamList = do
        typeName <- scanToken >>= validateStrTypeName
        id <- scanToken >>= validateStrIdentifier
        fmap ((typeName, id):) (whileM (fmap (punctuationMatches ",") peekToken) parseCommaParamList)
      where
        parseCommaParamList :: ParseState (String, String)
        parseCommaParamList = do
            typeName <- scanToken >> scanToken >>= validateStrTypeName
            id <- scanToken >>= validateStrIdentifier
            return (typeName, id)

-- block = '{' stmt* '}'
parseBlock :: ParseState SyntaxNode
parseBlock = do
    scanToken >>= validatePunctuation "{"
    statementList <- untilM (peekToken >>= \x -> return (punctuationMatches "}" x)) parseStatementList (EmptyNode)
    scanToken >>= validatePunctuation "}"
    return statementList
    where
        parseStatementList (otherStatements, isFinished) = do
            parseStatement >>= \x -> return $ SeqNode otherStatements x



parseStatementLookahead :: Token -> ParseState SyntaxNode
parseStatementLookahead tok
    | isDecl
    | isBlock
    | isExpression
    | isConditional
    | isLoop
    | isReturn

parseStatement :: Token -> ParseState SyntaxNode
parseStatement
    | isDecl        = do
         node <- declResult
         scanToken >>= validatePunctuation ";"
         return node
    | isBlock       = blockResult
    | isExpression  = do
         node <- expressionResult
         scanToken >>= validatePunctuation ";"
         return node
    | isLoop        = loopResult
    | isCondition   = conditionResult
    | isReturn      = do
         node <- returnResult
         (_, state) <- validateStr (punctuationMatches ";") (scanToken state)
         Just (node, state)
    | otherwise     = 
  where
    declResult = parseDeclaration state
    isDecl = isJust declResult
    blockResult = parseBlock state
    isBlock = isJust blockResult
    expressionResult = parseExpression state
    isExpression = isJust expressionResult
    conditionResult = parseCondition state
    isCondition = isJust conditionResult
    loopResult = parseLoop state
    isLoop = isJust loopResult
    returnResult = parseReturn state
    isReturn = isJust returnResult

parseCondition :: ParseState SyntaxNode
parseCondition = do
    (_, state) <- validateStr (controlMatches "if") (scanToken state)
    (_, state) <- validateStr (punctuationMatches "(") (scanToken state)
    (expressionNode, state) <- parseExpression state
    (_, state) <- validateStr (punctuationMatches ")") (scanToken state)
    (block, originalState) <- parseBlock state
    case scanToken originalState of
        Just (Control str, state)
                                    | str == "else" -> do 
                                        (elseBlock, state) <- parseBlock state
                                        Just (IfElseNode expressionNode block elseBlock, state)
                                    | otherwise -> Nothing
        _ -> Just (IfNode expressionNode block, originalState)

parseLoop :: ParseState SyntaxNode
parseLoop = do
    scanToken >>= validateControl "while"
    scanToken >>= validatePunctuation "("
    expressionNode <- parseExpression
    scanToken >>= validatePunctuation ")"
    block <- parseBlock
    return (WhileNode expressionNode block)
    

parseDeclaration :: ParseState SyntaxNode
parseDeclaration = do
    typeName <- scanToken >>= validateStrTypeName
    id <- scanToken >>= validateStrIdentifier
    nextTok <- peekToken
    case nextTok of
        Operator "=" -> do 
            scanToken
            expressionNode <- parseExpression
            return (DefinitionNode typeName id expressionNode)
        _ -> return (DeclarationNode typeName id)

parseReturn :: ParseState SyntaxNode
parseReturn = do
    scanToken >>= validateControl "return"
    returnExpr <- parseExpression
    return (ReturnNode returnExpr)

parseExpression :: ParseState SyntaxNode
parseExpression = do
    
assignOpsList :: S.Set String
assignOpsList = S.fromList ["=", "+=", "-=", "*=", "/=", "%="]

isAssignmentOperator :: Token -> Bool
isAssignmentOperator (Operator op) = S.member op assignOpsList
isAssignmentOperator _             = False
    

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
    case validateStr (operatorMatches "||") (scanToken state) of
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