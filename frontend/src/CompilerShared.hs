{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}

module CompilerShared where

import Control.Arrow (arr, first, (>>>), (&&&), ArrowChoice)
import Control.Monad (join, unless)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.State.Lazy (StateT)
import Data.Char (ord, chr)
import Data.Fix (Fix(..), unFix)
import Data.Functor.Classes ()
import Data.Functor.Compose (Compose(..), getCompose)
import Data.Int
import Data.Maybe (maybe, isJust)
import Data.Tuple (swap)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

------------
-- Utilities
dupe :: a -> (a, a)
dupe x = (x, x)
dupe2nd :: a -> b -> (a, b, b)
dupe2nd x y = (x, y, y)
dupe3 :: a -> (a, a, a)
dupe3 x = (x, x, x)
uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x, y, z) = f x y z
combine1 :: a -> (b, c) -> (a, b, c)
combine1 x (y, z) = (x, y, z)
combine3 :: (a, b) -> c -> (a, b, c)
combine3 (x, y) z = (x, y, z)

dropAndCount :: (a -> Bool) -> [a] -> ([a], Int)
dropAndCount fn = span fn >>> first (arr length) >>> swap

seqPair :: Monad m => (m a, m b) -> m (a, b)
seqPair (mFirst, mSecond) = (,) <$> mFirst <*> mSecond
seqTrip :: Monad m => (m a, m b, m c) -> m (a, b, c)
seqTrip (mFirst, mSecond, mThird) = (,,) <$> mFirst <*> mSecond <*> mThird

unlessM :: Monad m => m Bool -> m () -> m ()
unlessM test def = test >>= (`unless` def)

decompose :: Functor f => Fix (Compose ((,) a) f) -> (a, f (Fix (Compose ((,) a) f)))
decompose = getCompose . unFix

opChar :: (Int -> Int -> Int) -> Char -> Char -> Char
opChar op c1 c2 = chr (ord c1 `op` ord c2)

---------
-- Tokens
data ConstantType
    = CharConstant Int8
    | IntConstant Int
    | FloatConstant Float
    | BoolConstant Bool
    | StringConstant String
    | NullConstant
    deriving (Show, Eq)

data Token
    = Identifier String
    | Constant ConstantType
    | Operator String
    | Control String
    | Punctuation String
    | Keyword String
    | Eof
    | Invalid String InvalidReason
    deriving (Eq)

data InvalidReason
    = UntermString
    | UnknownChar
    | BadOperator
    | BadCharStr deriving (Eq, Show)

type TokenPos = (Token, Int)

numCall :: (forall a. (Num a) => a -> a -> a) -> ConstantType -> ConstantType -> Maybe ConstantType
numCall f (CharConstant c0) (CharConstant c1) = Just $ CharConstant (c0 `f` c1)
numCall f (IntConstant i0) (IntConstant i1) = Just $ IntConstant (i0 `f` i1)
numCall f (FloatConstant f0) (FloatConstant f1) = Just $ FloatConstant (f0 `f` f1)
numCall _ _ _ = Nothing

boolCall :: (Bool -> Bool -> Bool) -> ConstantType -> ConstantType -> Maybe ConstantType
boolCall f (BoolConstant b0) (BoolConstant b1) = Just $ BoolConstant (b0 `f` b1)
boolCall _ _ _ = Nothing

cmpCall :: (forall a. (Ord a) => a -> a -> Bool) -> ConstantType -> ConstantType -> Maybe ConstantType
cmpCall f (CharConstant c0) (CharConstant c1) = Just $ BoolConstant (c0 `f` c1)
cmpCall f (IntConstant i0) (IntConstant i1) = Just $ BoolConstant (i0 `f` i1)
cmpCall f (FloatConstant f0) (FloatConstant f1) = Just $ BoolConstant (f0 `f` f1)
cmpCall _ _ _ = Nothing

isIdentifier, isConstant, isOperator, isControl, isPunctuation, isEof, isInvalid, isKeyword :: Token -> Bool
isIdentifier (Identifier _) = True
isIdentifier _              = False
isConstant (Constant _) = True
isConstant _            = False
isOperator (Operator _) = True
isOperator _            = False
isControl (Control _) = True
isControl _           = False
isPunctuation (Punctuation _) = True
isPunctuation _               = False
isEof Eof = True
isEof _   = False
isInvalid (Invalid _ _) = True
isInvalid _             = False
isKeyword (Keyword _) = True
isKeyword _           = False

punctuationMatches, controlMatches, operatorMatches, keywordMatches :: String -> Token -> Bool
punctuationMatches v (Punctuation p) = p == v
punctuationMatches _ _               = False
controlMatches v (Control c) = c == v
controlMatches _ _           = False
operatorMatches v (Operator o) = o == v
operatorMatches _ _            = False
keywordMatches v (Keyword k) = v == k
keywordMatches _ _           = False

-----------------------------------------------------------
-- DataType: Tuple of typename and array/pointer qualifiers
type DataType = (String, [Int])
type DeclList = [(DataType, String)]

-- DataType utilities
invalidType, nullType, boolType, charType, shortType, intType, longType, floatType, voidType, ptrdiffType :: DataType
invalidType = ("$", [])
nullType = ("no", [0])
boolType = ("bool", [])
charType = ("char", [])
shortType = ("short", [])
intType = ("int", [])
longType = ("long", [])
floatType = ("float", [])
voidType = ("void", [])
ptrdiffType = longType

-- Checking basic types
isValueType, isPointerType, isArrayType, isExclusivePointer, isFloatType, isBoolType, isVoidType, isBasePointer :: DataType -> Bool
isValueType (_, ptrList) = null ptrList 
isPointerType = not . isValueType
isArrayType (_, ptrList) = not (null ptrList) && (head ptrList /= 0)
isExclusivePointer = (isPointerType &&& (not . isArrayType)) >>> uncurry (&&)
isFloatType = (==floatType)
isBoolType = (==boolType)
isVoidType = (==voidType)
isBasePointer (_, [_]) = True
isBasePointer _        = False

isIntegralType :: DataType -> Bool
isIntegralType (typename, ptrList)
    | typename == "char"  = isntPtr
    | typename == "short" = isntPtr
    | typename == "int"   = isntPtr
    | typename == "long"  = isntPtr
    | otherwise           = False
  where
    isntPtr = null ptrList


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

baseTypes :: S.Set String
baseTypes = S.fromList ["void", "char", "short", "int", "long", "float", "bool"]

isBaseType :: DataType -> Bool
isBaseType (name, _) = S.member name baseTypes

------------------
-- Annotated trees
-- Copy annotation 'a' from an existing annotated fixpoint to an unannotated fixpoint
copyAnnot
    :: (Functor f)
    => Fix (Compose ((,) a) f)
    -> f (Fix (Compose ((,) a) f))
    -> Fix (Compose ((,) a) f)
copyAnnot from = (Fix . Compose) . (,) (fst $ getCompose $ unFix from)

----------------------------------------------------
-- Expression Tree: Subset of AST which is evaluable
-- Nodes will be annotated with a datatype
data ExprF r
    = IdentifierNode String
    | StructMemberNode String  -- To differentiate between ids and structmems sans context
    | LiteralNode ConstantType
    | ArrayLiteralNode [r]
    | FunctionCallNode String [r]
    | ArrayIndexNode r r
    | ParenthesisNode r
    | BinaryOpNode BinaryOp r r
    | UnaryOpNode UnaryOp r
    | PostfixOpNode PostfixOp r
    | AssignmentNode AssignmentOp r r
    | MemberAccessNode Bool r r
    | CastNode DataType r
    | DynamicAllocationNode DataType r
    | DynamicFreeNode r
    deriving (Functor, Foldable, Traversable)

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
    | PrefixInc
    | PrefixDec
    deriving (Show, Eq)

data PostfixOp = PostInc | PostDec deriving (Show, Eq)

data ExprInfo = ExprInfo
    { dataType :: DataType
    , handedness :: Handedness
    , sourceLoc :: SourceLoc }
data Handedness = LValue | RValue deriving (Show, Eq)
type ExprAnn = Compose ((,) ExprInfo)
type Expr = Fix (ExprAnn ExprF)

getExprF :: Expr -> ExprF Expr
getExprF = snd . getCompose . unFix
annotExpr :: DataType -> Handedness -> SourceLoc -> ExprF Expr -> Expr
annotExpr tp hd sl = (Fix . Compose) . (,) (ExprInfo tp hd sl)
annotExprEmpty :: ExprF Expr -> Expr
annotExprEmpty = annotExpr invalidType LValue (SourceLoc 0 0)
annotExprType :: DataType -> ExprF Expr -> Expr
annotExprType tp = annotExpr tp LValue (SourceLoc 0 0)
annotExprLoc :: SourceLoc -> ExprF Expr -> Expr
annotExprLoc = annotExpr invalidType LValue
typeOf :: Expr -> DataType
typeOf = dataType . fst . getCompose . unFix
handednessOf :: Expr -> Handedness
handednessOf = handedness . fst . getCompose . unFix
sourceLocOf :: Expr -> SourceLoc
sourceLocOf = sourceLoc . fst . getCompose . unFix

--------------------------------------------------------------
-- SyntaxNode: Non-evaluable subset of nodes for the not-c AST
data SyntaxNodeF r
    = EmptyNode
    -- Two sequential operations
    | SeqNode r r
    -- Control
    | WhileNode r r
    | ForNode r r r r r
    | IfNode r r 
    | IfElseNode r r r
    | ReturnNode r
    | ContinueNode
    | BreakNode
    | BlockNode r
    | PrintNode r
    -- Decl
    | DeclarationNode DataType String
    -- Breakout to expressions
    | ExprNode Expr
    deriving (Functor)

data SourceLoc = SourceLoc { srcBegin :: Int, srcEnd :: Int } deriving Show
type SourceAnn = Compose ((,) SourceLoc)
type SyntaxNode = Fix (SourceAnn SyntaxNodeF)

annotSyntax :: Int -> Int -> SyntaxNodeF SyntaxNode -> SyntaxNode
annotSyntax b e = (Fix . Compose) . (,) (SourceLoc b e)
annotSyntaxEmpty :: SyntaxNodeF SyntaxNode -> SyntaxNode
annotSyntaxEmpty = annotSyntax 0 0

isEmptyNode :: SyntaxNode -> Bool
isEmptyNode nod = case snd $ getCompose $ unFix nod of
    EmptyNode -> True
    _         -> False

---------------------------
-- Parser state information
data FailureInfo = FailureInfo { failReason :: String, failRegion :: (Int, Int), failLocation :: Int }
type TypeEnv = S.Set String
type LexerState = ([TokenPos], String, (Int, Int))
type ParseAction = StateT ParseState (Either FailureInfo)
type Program = ([Global], [StructDefinition])
type StructDefinition = (String, [(DataType, String)])

data SymbolType = FuncSym | TypeSym | VarSym | UnkSym deriving (Show, Eq)
type SymbolMap = [M.Map String SymbolType]

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

data Global = Function FunctionDefinition | GlobalVar SyntaxNode

data ParseState = ParseState
    { lexerState :: LexerState
    , typeEnv :: TypeEnv  -- List of all valid types
    , globalsList :: [Global]
    , structList :: [StructDefinition]
    , symbolMap :: SymbolMap  -- List of all taken symbol names + kind
    , currentNodeLexStart :: Int
    }

initialState :: String -> ParseState
initialState progStr = ParseState ([], progStr, (0, 0)) baseTypes [] [] [M.fromList (map (, TypeSym) $ S.toList baseTypes)] 0

raiseFailure :: String -> Int -> Int -> StateT s (Either FailureInfo) a
raiseFailure msg begin end = lift (Left (FailureInfo msg (begin, end) end))
raiseFailureLoc :: String -> SourceLoc -> StateT s (Either FailureInfo) a
raiseFailureLoc msg = uncurry (raiseFailure msg) . (srcBegin &&& srcEnd)
raiseFailurePrecise :: String -> Int -> Int -> Int -> StateT s (Either FailureInfo) a
raiseFailurePrecise msg begin end opt = lift (Left (FailureInfo msg (begin, end) opt))

getMemberType :: StructDefinition -> String -> DataType 
getMemberType (_, memberList) name =
    maybe invalidType fst (L.find ((==name) . snd) memberList)

getIdentifierType :: String -> SymbolMap -> SymbolType
getIdentifierType _ []          = UnkSym
getIdentifierType id (map:rest) = if M.member id map then map M.! id else getIdentifierType id rest

popToken :: ParseState -> (Token, ParseState)
popToken (ParseState (h:t, rest, (curclt, prevclt)) env globals structs syms lp) =
    (fst h, ParseState (t, rest, (curclt + snd h, curclt)) env globals structs syms lp)
popToken (ParseState ([], rest, clt) env globals structs syms lp) = error "popToken called on empty token list"

data DNAType
    = Int8  Int
    | Int16 Int
    | Int32 Int
    | Int64 Int
    | Float Int
    | InvalidType
    deriving (Eq, Ord)

data DNAVariable 
    = Temp String DNAType
    | Input String DNAType
    | Local String DNAType

data DNAOperand
    = Variable Bool DNAVariable
    | MemoryRef Bool DNAVariable Int DNAType
    | Immediate Rational DNAType
    | GlobalArr String DNAType
    | None
    
data JmpCondition
    = Always
    | Eq 
    | Ne 
    | Gt 
    | Lt 
    | Ge 
    | Le

type DNABlock = [DNAInstruction]
type DNAFunctionDefinition = (String, [DNAVariable], DNABlock)

type DNAInstruction = DNAInstructionF DNAOperand DNAOperand

data DNAInstructionF r w
    = Mov w r
    | Add w r r
    | Sub w r r
    | Mul w r r
    | Div w r r
    | Mod w r r
    | Cmp w r
    | Jmp JmpCondition String
    | Param r DNAType
    | Call String w
    | ReturnVal r
    | ReturnVoid
    | ArrayCopy w r Int
    | IntToFloat w r
    | FloatToInt w r
    | Allocate w r
    | Deallocate r
    | Label String
    | Print r

data VarInfo
    = FunctionVar DataType [(DataType, String)]
    | PrimitiveVar DataType
    | StructVar DataType
    deriving Show
type VarInfoMap = M.Map String VarInfo
data EnvBlock = EnvBlock { inLoop :: Bool, varMap :: VarInfoMap } deriving Show
type ValidationEnv = [EnvBlock]
type StructMap = M.Map String StructDefinition

lookupVar :: String -> ValidationEnv -> Maybe VarInfo
lookupVar id = join . L.find isJust . map (M.lookup id . varMap)

envInLoop :: ValidationEnv -> Bool
envInLoop = any inLoop
    
isPrimitiveType :: DataType -> Bool
isPrimitiveType (typename, _) = S.member typename baseTypes

isStructType :: DataType -> StructMap -> Bool
isStructType (typename, _) = M.member typename
