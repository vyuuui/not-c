{-# LANGUAGE TupleSections #-}
module CompilerShared where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Trans.State.Lazy ( StateT )
import Control.Monad.Trans (lift)

type TypeEnv = S.Set String
type LexerState = ([Token], String)
type DataType = (String, [Int])
type ParseAction = StateT ParseState (Either String)
type Program = ([FunctionDefinition], [StructDefinition])

data FunctionDefinition = FunctionDefinition
    { returnType :: DataType
    , funcName :: String
    , paramList :: [(DataType, String)]
    , rootNode :: SyntaxNode
    }
    deriving Show
newtype StructDefinition = StructDefinition (String, [(DataType, String)]) deriving Show

showDt :: DataType -> String
showDt (dataTypeName, ptrList) = dataTypeName ++ concatMap (\x -> if x > 0 then "[" ++ show x ++ "]" else "*") ptrList

raiseFailure :: String -> StateT s (Either String) a
raiseFailure msg = lift (Left msg)

baseTypes :: S.Set String
baseTypes = S.fromList ["void", "char", "short", "int", "long", "float", "bool"]

isBaseType :: DataType -> Bool
isBaseType (name, _) = S.member name baseTypes

initialState :: String -> ParseState
initialState progStr = ParseState ([], progStr) baseTypes [] [] [M.fromList (map (, TypeSym) $ S.toList baseTypes)]

getIdentifierType :: String -> SymbolMap -> SymbolType
getIdentifierType _ []          = UnkSym
getIdentifierType id (map:rest) = if M.member id map then map M.! id else getIdentifierType id rest

data SymbolType = FuncSym | TypeSym | VarSym | UnkSym deriving (Show, Eq)
type SymbolMap = [M.Map String SymbolType]

data ParseState = ParseState
    { lexerState :: LexerState
    , typeEnv :: TypeEnv  -- List of all valid types
    , funcList :: [FunctionDefinition]
    , structList :: [StructDefinition]
    , symbolMap :: SymbolMap  -- List of all taken symbol names + kind
    }
    deriving Show

popToken :: ParseState -> (Token, ParseState)
popToken (ParseState (h:t, rest) env funcs structs syms) = (h, ParseState (t, rest) env funcs structs syms)
popToken (ParseState ([], rest) env funcs structs syms) = error "popToken called on empty token list"

data ConstantType
    = IntConstant Int
    | FloatConstant Float
    | BoolConstant Bool
    | StringConstant String
    deriving (Show, Eq)

data Token
    = Identifier String
    | Constant ConstantType
    | Operator String
    | Control String
    | Punctuation String
    | Keyword String
    | Eof
    | Invalid
    deriving (Show, Eq)

isIdentifier :: Token -> Bool
isIdentifier (Identifier _) = True
isIdentifier _              = False

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

isKeyword :: Token -> Bool
isKeyword (Keyword _) = True
isKeyword _           = False

punctuationMatches :: String -> Token -> Bool
punctuationMatches v (Punctuation p) = p == v
punctuationMatches _ _               = False

controlMatches :: String -> Token -> Bool
controlMatches v (Control c) = c == v
controlMatches _ _           = False

operatorMatches :: String -> Token -> Bool
operatorMatches v (Operator o) = o == v
operatorMatches _ _            = False

keywordMatches :: String -> Token -> Bool
keywordMatches v (Keyword k) = v == k
keywordMatches _ _           = False

isEmptyNode :: SyntaxNode -> Bool
isEmptyNode EmptyNode = True
isEmptyNode _         = False

data SyntaxNode
    = EmptyNode
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
    | MemberAccessNode Bool SyntaxNode SyntaxNode
    | CastNode SyntaxNode DataType
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