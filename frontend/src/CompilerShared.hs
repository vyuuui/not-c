{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
module CompilerShared where

import Control.Arrow (arr, first, (>>>), (&&&))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.State.Lazy (StateT)
import Data.Fix (Fix(..), unFix)
import Data.Functor.Classes ()
import Data.Functor.Compose (Compose(..), getCompose)
import Data.Maybe (maybe)
import Data.Tuple (swap)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

dupe :: a -> (a, a)
dupe x = (x, x)
dupe2nd :: a -> b -> (a, b, b)
dupe2nd x y = (x, y, y)
dupe3 :: a -> (a, a, a)
dupe3 x = (x, x, x)

-- Tokens
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
    deriving (Eq)

type TokenPos = (Token, Int)
data FailureInfo = FailureInfo { failReason :: String, failRegion :: (Int, Int) }

-- DataType: Tuple of typename and array/pointer qualifiers
type DataType = (String, [Int])
type DeclList = [(DataType, String)]

-- DataType utilities
invalidType, boolType, charType, shortType, intType, longType, floatType, voidType, ptrdiffType :: DataType
invalidType = ("$", [])
boolType = ("bool", [])
charType = ("char", [])
shortType = ("short", [])
intType = ("int", [])
longType = ("long", [])
floatType = ("float", [])
voidType = ("void", [])
ptrdiffType = longType

-- Checking basic types
isValueType, isPointerType, isFloatType, isBoolType, isVoidType, isBasePointer :: DataType -> Bool
isValueType (_, ptrList) = null ptrList 
isPointerType = not . isValueType
isFloatType = (==floatType)
isBoolType = (==boolType)
isVoidType = (==voidType)
isBasePointer (_, [_]) = True
isBasePointer _        = False

datatypeSize :: DataType -> Int
datatypeSize tp
    | isPointerType tp = 8
    | tp == boolType  = 1
    | tp == charType  = 1
    | tp == shortType = 2
    | tp == intType   = 4
    | tp == longType  = 8
    | tp == floatType = 8
    | otherwise       = 0

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
largestType t1 t2
    | t1Size >= t2Size = t1
    | otherwise        = t2
  where
    t1Size = classifySize $ fst t1
    t2Size = classifySize $ fst t2

-- Copy annotation 'a' from an existing annotated fixpoint to an unannotated fixpoint
copyAnnot
    :: (Functor f)
    => Fix (Compose ((,) a) f)
    -> f (Fix (Compose ((,) a) f))
    -> Fix (Compose ((,) a) f)
copyAnnot from = (Fix . Compose) . (,) (fst $ getCompose $ unFix from)

-- Expression Tree: Subset of AST which is evaluable
-- Nodes will be annotated with a datatype
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
    deriving (Functor)

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

newtype ExprType = ExprType { dataType :: DataType } deriving (Eq)
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
    | BlockNode r
    -- Decl
    | DeclarationNode DataType String
    | DefinitionNode DataType String r
    -- Breakout to expressions
    | ExprNode Expr
    deriving (Functor)

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
type LexerState = ([TokenPos], String, (Int, Int))
type ParseAction = StateT ParseState (Either FailureInfo)
type Program = ([FunctionDefinition], [StructDefinition])

data FunctionDefinition = FunctionDefinition
    { returnType :: DataType
    , funcName :: String
    , paramList :: [(DataType, String)]
    , rootNode :: SyntaxNode
    , funcAnnot :: FunctionAnnotation
    }
data FunctionAnnotation = FunctionAnnotation
    { returnTypeLoc :: SourceLoc
    , funcNameLoc :: SourceLoc
    , paramsLoc :: [SourceLoc]
    }

newtype StructDefinition = StructDefinition { getStructDef :: (String, [(DataType, String)]) }

getMemberType :: StructDefinition -> String -> DataType 
getMemberType (StructDefinition (_, memberList)) name =
    maybe invalidType fst (L.find ((==name) . snd) memberList)

showDt :: DataType -> String
showDt (dataTypeName, ptrList) = dataTypeName ++ concatMap (\x -> if x > 0 then "[" ++ show x ++ "]" else "*") ptrList

raiseFailure :: String -> Int -> Int -> StateT s (Either FailureInfo) a
raiseFailure msg begin end = lift (Left (FailureInfo msg (begin, end)))
raiseFailureLoc :: String -> SourceLoc -> StateT s (Either FailureInfo) a
raiseFailureLoc msg = uncurry (raiseFailure msg) . (srcBegin &&& srcEnd)

baseTypes :: S.Set String
baseTypes = S.fromList ["void", "char", "short", "int", "long", "float", "bool"]

isBaseType :: DataType -> Bool
isBaseType (name, _) = S.member name baseTypes

initialState :: String -> ParseState
initialState progStr = ParseState ([], progStr, (0, 0)) baseTypes [] [] [M.fromList (map (, TypeSym) $ S.toList baseTypes)] 0

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
    , currentNodeLexStart :: Int
    }

popToken :: ParseState -> (Token, ParseState)
popToken (ParseState (h:t, rest, (curclt, prevclt)) env funcs structs syms lp) =
    (fst h, ParseState (t, rest, (curclt + snd h, curclt)) env funcs structs syms lp)
popToken (ParseState ([], rest, clt) env funcs structs syms lp) = error "popToken called on empty token list"

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

dropAndCount :: (a -> Bool) -> [a] -> ([a], Int)
dropAndCount fn = span fn >>> first (arr length) >>> swap