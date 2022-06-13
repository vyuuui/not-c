module Parser
( SyntaxNode(..)
, BinaryOp(..)
, UnaryOp(..)
, Program
, ArgumentList
, ParseState
, parseProg
) where

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import Data.Maybe
import Control.Monad
import Control.Monad.Loops ( iterateUntilM )
import Lexer
import System.IO


type Program = [SyntaxNode];

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
    deriving Show

data AssignmentOp
    = NoOp
    | PlusEq
    | MinusEq
    | MulEq
    | DivEq
    | ModEq
    deriving Show

data UnaryOp = Negate deriving Show

type ParseState = [Token]
type ParseResult = (SyntaxNode, ParseState)

scanToken :: ParseState -> Maybe (Token, ParseState)
scanToken []    = Nothing
scanToken state = return (head state, tail state)

isIdentifier :: Token -> Bool
isIdentifier (Identifier _) = True
isIdentifier _              = False

isTypeName :: Token -> Bool
isTypeName (TypeName _) = True
isTypeName _            = False

isConstant :: Token -> Bool
isConstant (Constant _) = True
isConstant _            = False

isOperator :: Token -> Bool
isOperator (Operator _) = True
isOperator _            = False

isControl :: Token -> Bool
isControl (Control _) = True
isControl _           = False

isPunctuation :: Token -> Bool
isPunctuation (Punctuation _) = True
isPunctuation _               = False

isEof :: Token -> Bool
isEof Eof = True
isEof _   = False

isInvalid :: Token -> Bool
isInvalid Invalid = True
isInvalid _       = False

punctuationMatches :: String -> Token -> Bool
punctuationMatches v (Punctuation p) = p == v
punctuationMatches _ _               = False

controlMatches :: String -> Token -> Bool
controlMatches v (Control c) = c == v
controlMatches _ _           = False

operatorMatches :: String -> Token -> Bool
operatorMatches v (Operator o) = o == v
operatorMatches _ _             = False

validateStr :: (Token -> Bool) -> Maybe (Token, ParseState) -> Maybe (String, ParseState)
validateStr _ Nothing = Nothing
validateStr check (Just (tok, state))
    | not $ check tok = Nothing
    | otherwise       = return (extractInner tok, state)

extractInner :: Token -> String
extractInner (Identifier s)  = s
extractInner (TypeName s)    = s
extractInner (Operator s)    = s
extractInner (Control s)     = s
extractInner (Punctuation s) = s
extractInner _               = error "Invalid call"

loadAndPrint :: String -> IO ()
loadAndPrint file = do
    handle <- openFile file ReadMode
    contents <- hGetContents handle
    let tokens = lexString contents
    print $ parseProg tokens
    

parseProg :: ParseState -> Maybe Program
parseProg state = fmap fst (
    iterateUntilM (\(_, state) -> null state || isEof (head state)) 
    (\(list, state) -> parseFunction state >>= \(newFunc, newState) -> Just (newFunc:list, newState))
    ([], state))

parseFunction :: ParseState -> Maybe ParseResult
parseFunction state = do
    (typeName, state1) <- validateStr isTypeName (scanToken state)
    (id, state2) <- validateStr isIdentifier (scanToken state1)
    (_, state3) <- validateStr (punctuationMatches "(") (scanToken state2)
    (paramList, state4) <- parseParamList state3
    (_, state5) <- validateStr (punctuationMatches ")") (scanToken state4)
    (block, state6) <- parseBlock state5
    return (FunctionDefinitionNode typeName id paramList block, state6)

-- paramlist = type identifier (',' type identifier)* | ε
type ParameterList = [(String, String)]

parseParamList :: ParseState -> Maybe (ParameterList, ParseState)
parseParamList state = do
    (typeToken, state1) <- scanToken state
    if isTypeName typeToken
    then doActualParseParamList state
    else return ([], state)

  where
    doActualParseParamList :: ParseState -> Maybe (ParameterList, ParseState)
    doActualParseParamList state = do
        (typeToken, state1) <- scanToken state
        let typeVal = extractInner typeToken
        (idToken, state2) <- scanToken state1
        let idVal = extractInner idToken
        iterateUntilM (not . punctuationMatches "," . head . snd)
                      parseCommaParamList
                      ([(typeVal, idVal)], state2)
                      
      where
        parseCommaParamList :: (ParameterList, ParseState) -> Maybe (ParameterList, ParseState)
        parseCommaParamList (curParamList, tokenList) = do
            let list1 = tail tokenList
            (typeToken, list2) <- scanToken list1
            let typeVal = extractInner typeToken
            (idToken, list3) <- scanToken list2
            let idVal = extractInner idToken
            Just (curParamList ++ [(typeVal, idVal)], list3)


-- block = '{' stmt* '}'
parseBlock :: ParseState -> Maybe ParseResult
parseBlock state = do
    (_, state1) <- validateStr (punctuationMatches "{") (scanToken state)
    let (statementList, state2, _) = until (\(statementList, state, isFinished) -> isFinished) parseStatementList (EmptyNode, state1, False)
    (_, state3) <- validateStr (punctuationMatches "}") (scanToken state2)
    Just (statementList, state3)
    where
        parseStatementList (otherStatements, state, isFinished) = 
            case parseStatement state of
                Just (node, newState) -> (SeqNode otherStatements node, newState, False)
                Nothing -> (otherStatements, state, True)

parseStatement :: ParseState -> Maybe ParseResult
parseStatement state
    | isDecl        = do
         (node, state) <- declResult
         (_, state) <- validateStr (punctuationMatches ";") (scanToken state)
         Just (node, state)
    | isBlock       = blockResult
    | isExpression  = do
         (node, state) <- expressionResult
         (_, state) <- validateStr (punctuationMatches ";") (scanToken state)
         Just (node, state)
    | isLoop        = loopResult
    | isCondition   = conditionResult
    | isReturn      = do
         (node, state) <- returnResult
         (_, state) <- validateStr (punctuationMatches ";") (scanToken state)
         Just (node, state)
    | otherwise     = Nothing
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


-- conditional = 'if' '(' expression ')' block elseconditional
-- elseconditional = 'else' block | ε

parseCondition :: ParseState -> Maybe ParseResult
parseCondition state = do
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

-- loop = 'while' '(' expression ')' block

parseLoop :: ParseState -> Maybe ParseResult
parseLoop state = do
    (_, state) <- validateStr (controlMatches "while") (scanToken state)
    (_, state) <- validateStr (punctuationMatches "(") (scanToken state)
    (expressionNode, state) <- parseExpression state
    (_, state) <- validateStr (punctuationMatches ")") (scanToken state)
    (block, originalState) <- parseBlock state
    Just (WhileNode expressionNode block, state)
    

parseDeclaration :: ParseState -> Maybe ParseResult
parseDeclaration state = do
    (typeName, state) <- validateStr isTypeName (scanToken state)
    (id, originalState) <- validateStr isIdentifier (scanToken state)
    case scanToken originalState of
        Just (Operator "=", state) -> do 
            (expressionNode, state) <- parseExpression state
            Just (DefinitionNode typeName id expressionNode, state)
        Just (_, _) -> Just (DeclarationNode typeName id, originalState)
        Nothing -> Nothing

parseReturn :: ParseState -> Maybe ParseResult
parseReturn state = do
    (_, state) <- validateStr (controlMatches "return") (scanToken state)
    (expressionNode, state) <- parseExpression state
    Just (ReturnNode expressionNode, state)

parseExpression :: ParseState -> Maybe ParseResult
parseExpression = parseAssignment

assignOpsList :: S.Set String
assignOpsList = S.fromList ["=", "+=", "-=", "*=", "/=", "%="]

isAssignmentOperator :: Token -> Bool
isAssignmentOperator (Operator op) = S.member op assignOpsList
isAssignmentOperator _             = False

parseAssignment :: ParseState -> Maybe ParseResult
parseAssignment state = do
    (identifier, state1) <- scanToken state
    (assignTok, state2) <- scanToken state1
    if isIdentifier identifier && isAssignmentOperator assignTok
    then do
        let op = getAssignOp assignTok
        let id = extractInner identifier
        (subExpr, state3) <- parseAssignment state2
        Just (AssignmentNode id op subExpr, state3)
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

parseLogicOr :: ParseState -> Maybe ParseResult
parseLogicOr state = do
    (node, state) <- parseLogicAnd state
    case validateStr (operatorMatches "||") (scanToken state) of
        Just (_, state) -> do 
            (rightNode, state) <- parseLogicAnd state
            Just (BinaryOpNode Or node rightNode, state)
        Nothing -> Just (node, state)

parseLogicAnd :: ParseState -> Maybe ParseResult
parseLogicAnd state = do
    (node, state) <- parseEqComp state
    case validateStr (operatorMatches "&&") (scanToken state) of
        Just (_, state) -> do 
            (rightNode, state) <- parseEqComp state
            Just (BinaryOpNode And node rightNode, state)
        Nothing -> Just (node, state)

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

parseAddition :: ParseState -> Maybe ParseResult
parseAddition state = do
    (node, originalState) <- parseMultiplication state
    (eqToken, state) <- scanToken originalState
    case () of _
                | operatorMatches "+" eqToken -> do 
                    (rightNode, state) <- parseMultiplication state
                    Just (BinaryOpNode Addition node rightNode, state)
                | operatorMatches "-" eqToken -> do 
                    (rightNode, state) <- parseMultiplication state
                    Just (BinaryOpNode Subtraction node rightNode, state)
                | otherwise                    -> Just (node, originalState)

parseMultiplication :: ParseState -> Maybe ParseResult
parseMultiplication state = do
    (node, originalState) <- parseUneg state
    (eqToken, state) <- scanToken originalState
    case () of _
                | operatorMatches "*" eqToken -> do 
                    (rightNode, state) <- parseUneg state
                    Just (BinaryOpNode Multiplication node rightNode, state)
                | operatorMatches "/" eqToken -> do 
                    (rightNode, state) <- parseUneg state
                    Just (BinaryOpNode Division node rightNode, state)
                | operatorMatches "%" eqToken -> do 
                    (rightNode, state) <- parseUneg state
                    Just (BinaryOpNode Mod node rightNode, state)
                | otherwise                    -> Just (node, originalState)

parseUneg :: ParseState -> Maybe ParseResult
parseUneg paramState = do
    (eqToken, state) <- scanToken paramState
    case () of _
                | operatorMatches "-" eqToken -> do 
                    (node, state) <- parseBaseExpr state
                    Just (UnaryOpNode Negate node, state)
                | otherwise                    -> do 
                    parseBaseExpr paramState

parseBaseExpr :: ParseState -> Maybe ParseResult
parseBaseExpr state = do
    (firstTok, _) <- scanToken state
    case () of _
                | isIdentifier firstTok           -> parseId state
                | isConstant firstTok             -> parseConstant state
                | punctuationMatches "(" firstTok -> parseParenthesis state
                | otherwise                       -> Nothing
  where
    parseCall id state = do
        (_, state) <- validateStr (punctuationMatches "(") (scanToken state)
        (argList, state) <- parseArgList state
        (_, state) <- validateStr (punctuationMatches ")") (scanToken state)
        Just (FunctionCallNode id argList, state)
    parseId state = do
        (identifier, state) <- validateStr isIdentifier (scanToken state)
        (nextTok, _) <- scanToken state
        if punctuationMatches "(" nextTok
        then parseCall identifier state
        else Just (IdentifierNode identifier, state)
    parseParenthesis state = do -- (x + 3 * y)
        (_, state) <- validateStr (punctuationMatches "(") (scanToken state)
        (expr, state) <- parseExpression state
        (_, state) <- validateStr (punctuationMatches ")") (scanToken state)
        Just (expr, state)
    parseConstant state = do 
        (Constant const, state) <- scanToken state
        Just (LiteralNode const, state)
        

type ArgumentList = [SyntaxNode]
parseArgList :: ParseState -> Maybe (ArgumentList, ParseState)
parseArgList state
    | isJust iterationStart = iterationStart >>= parseRemainingArgs
    | otherwise             = return ([], state)
  where
    iterationStart = (\(x, y) -> ([x], y)) <$> parseExpression state
    parseRemainingArgsIter (argList, restState) = do
        let list1 = tail restState
        (syntaxTree, list2) <- parseExpression list1
        Just (argList ++ [syntaxTree], list2)
    parseRemainingArgs = iterateUntilM (not . punctuationMatches "," . head . snd) parseRemainingArgsIter

{-
prog = function+
function = type identifier '(' paramlist ')' block
paramlist = type identifier (',' type identifier)* | ε
block = '{' stmt* '}'
stmt = declaration ';' | block | expression ';' | conditional | loop | ret ';'
declaration = type identifier optassign
optassign = '=' expression | ε
loop = 'while' '(' expression ')' block
conditional = 'if' '(' expression ')' block elseconditional
elseconditional = 'else' block | ε
ret = 'return' expression
expression = assignment
assignment = identifier '=' assignment  | identifier '+=' assignment |
             identifier '-=' assignment | identifier '*=' assignment |
             identifier '/=' assignment | identifier '%=' assignment | logicor
logicor = logicand ('||' logicand)*
logicand = eqcomp ('&&' eqcomp)*
eqcomp = ordcomp ('==' ordcomp)* | ordcomp ('!=' orcomp)*
ordcomp = addition ('<' addition)* | addition ('>' addition)* | addition ('<=' addition)* | addition ('>=' addition)*
addition = multiplication ('+' multiplication)* | multiplication ('-' multiplication)*
multiplication = uneg ('*' uneg)* | uneg ('/' uneg)* | uneg ('%' uneg)*
uneg = '-' baseexpr | baseexpr
baseexpr = identifier '(' arglist ')' | identifier | constant | '(' expression ')'
arglist = expression (',' expression)* | ε

type = 'void' | 'char' | 'short' | 'int' | 'long' | 'float' | 'double' | 'bool'
constant = 'true' | 'false' | number
number = -?[0-9]+\.[0-9]*
identifier = [A-Za-z][A-Za-z0-9_]*
-}