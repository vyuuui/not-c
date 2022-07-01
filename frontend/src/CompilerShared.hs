{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
{-# Language TemplateHaskell #-}
module CompilerShared where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Trans.State.Lazy ( StateT )
import Control.Monad.Trans (lift)
import Data.Fix
import Data.Functor.Compose
import Data.Functor.Classes
import Data.Maybe
import Text.Show.Deriving

dupe :: a -> (a, a)
dupe x = (x, x)

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

-- DataType: Tuple of typename and array/pointer qualifiers
type DataType = (String, [Int])

invalidType, boolType, charType, shortType, intType, longType, floatType, voidType :: DataType
invalidType = ("$", [])
boolType = ("bool", [])
charType = ("char", [])
shortType = ("short", [])
intType = ("int", [])
longType = ("long", [])
floatType = ("float", [])
voidType = ("void", [])

classifySize :: String -> Int
classifySize tp
    | tp == "char"   = 1
    | tp == "bool"   = 1
    | tp == "short"  = 2
    | tp == "int"    = 4
    | tp == "long"   = 8
    | tp == "float"  = 8
    | otherwise      = 0

largestType :: DataType -> DataType -> DataType
largestType t1 t2 = snd $ maximum (zip (map (classifySize . fst) typeList) typeList)
  where
    typeList = [t1, t2]

-- Expression Tree: Subset of AST which is evaluable
-- Nodes will be annotated with a datatype
data BinaryOp
    = Addition
    | Multiplication
    | Subtraction
    | Division
    | Modulus
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

-- Copy annotation 'a' from an existing annotated fixpoint to an unannotated fixpoint
copyAnnot
    :: (Functor f)
    => Fix (Compose ((,) a) f)
    -> f (Fix (Compose ((,) a) f))
    -> Fix (Compose ((,) a) f)
copyAnnot from = (Fix . Compose) . (,) (fst $ getCompose $ unFix from)

data ExprF r
    = IdentifierNode String
    | StructMemberNode String  -- To differentiate between ids and structmems sans context
    | LiteralNode ConstantType
    | FunctionCallNode String [r]
    | ArrayIndexNode r r
    | ParenthesisNode r
    | BinaryOpNode BinaryOp r r
    | UnaryOpNode UnaryOp r
    | AssignmentNode AssignmentOp r r
    | MemberAccessNode Bool r r
    | CastNode DataType r
    deriving (Show, Functor)
deriveShow1 ''ExprF

newtype ExprType = ExprType { dataType :: DataType } deriving (Show, Eq)
type ExprAnn = Compose ((,) ExprType)
type Expr = Fix (ExprAnn ExprF)

annotExpr :: DataType -> ExprF Expr -> Expr
annotExpr tp = (Fix . Compose) . (,) (ExprType tp)
annotExprEmpty :: ExprF Expr -> Expr
annotExprEmpty = annotExpr invalidType
typeOf :: Expr -> DataType
typeOf = dataType . fst . getCompose . unFix

-- SyntaxNode: Non-evaluable subset of nodes for the not-c AST
data SyntaxNodeF r
    = EmptyNode
    -- Two sequential operations
    | SeqNode r r
    -- Control
    | WhileNode r r
    | ForNode r r r r
    | IfNode r r 
    | IfElseNode r r r
    | ReturnNode r
    | ContinueNode
    | BreakNode
    -- Decl
    | DeclarationNode DataType String
    | DefinitionNode DataType String r
    -- Breakout to expressions
    | ExprNode Expr
    deriving (Show, Functor)
deriveShow1 ''SyntaxNodeF

isEmptyNode :: SyntaxNode -> Bool
isEmptyNode nod = case snd $ getCompose $ unFix nod of
    EmptyNode -> True
    _         -> False

data SourceLoc = SourceLoc { srcBegin :: Int, srcEnd :: Int } deriving Show
type SourceAnn = Compose ((,) SourceLoc)
type SyntaxNode = Fix (SourceAnn SyntaxNodeF)

annotSyntax :: Int -> Int -> SyntaxNodeF SyntaxNode -> SyntaxNode
annotSyntax b e = (Fix . Compose) . (,) (SourceLoc b e)
annotSyntaxEmpty :: SyntaxNodeF SyntaxNode -> SyntaxNode
annotSyntaxEmpty = annotSyntax 0 0

type TypeEnv = S.Set String
type LexerState = ([Token], String)
type ParseAction = StateT ParseState (Either String)
type Program = ([FunctionDefinition], [StructDefinition])

data FunctionDefinition = FunctionDefinition
    { returnType :: DataType
    , funcName :: String
    , paramList :: [(DataType, String)]
    , rootNode :: SyntaxNode
    } deriving Show

newtype StructDefinition = StructDefinition (String, [(DataType, String)]) deriving Show

getMemberType :: StructDefinition -> String -> DataType 
getMemberType (StructDefinition (_, memberList)) name =
    maybe invalidType fst (L.find ((==name) . snd) memberList)

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
