module Validator ( validateProgram ) where

import CompilerShared
import CompilerShow
import Control.Arrow
import Control.Monad
import Control.Monad.Loops
import Control.Monad.Trans.State.Lazy
import Data.Fix
import Data.Functor ((<&>))
import Data.Functor.Compose
import Data.Maybe
import Debug.Trace
import Lexer
import Parser
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

data VarInfo
    = FunctionVar DataType [(DataType, String)]
    | PrimitiveVar DataType
    | StructVar DataType
    deriving Show
type VarInfoMap = M.Map String VarInfo
data EnvBlock = EnvBlock { inLoop :: Bool, varMap :: VarInfoMap } deriving Show
type Environment = [EnvBlock]

envInLoop :: Environment -> Bool
envInLoop = any inLoop
-- map lookup over all blocks -> find first Just result -> Join Maybe(Maybe) to Maybe
lookupVar :: String -> Environment -> Maybe VarInfo
lookupVar id = join . L.find isJust . map (M.lookup id . varMap)
lookupVarFailure :: String -> GeneratorAction VarInfo
lookupVarFailure id = do
    maybeVar <- lookupVar id <$> (environment <$> get)
    maybe
      (raiseFailure ("Undefined id " ++ id) 0 0)
      return
      maybeVar

type StructMap = M.Map String StructDefinition

data GeneratorState = GeneratorState
    { structMap :: StructMap
    , environment :: Environment
    } deriving Show

type GeneratorAction = StateT GeneratorState (Either FailureInfo)

unlessM :: Monad m => m Bool -> m () -> m ()
unlessM test def = test >>= (`unless` def)
whenM :: Monad m => m Bool -> m () -> m ()
whenM test def = test >>= (`when` def)

putEnvironment :: Environment -> GeneratorAction ()
putEnvironment newEnv = modify (\(GeneratorState structs env) -> GeneratorState structs newEnv)
putStructs :: StructMap -> GeneratorAction ()
putStructs newStructs = modify (\(GeneratorState structs env) -> GeneratorState newStructs env)
addStruct :: StructDefinition -> GeneratorAction ()
addStruct struct@(StructDefinition (name, _)) =
    get >>= putStructs . M.insert name struct . structMap

pushEnvironment :: Bool -> GeneratorAction ()
pushEnvironment isLoop =
    get >>= putEnvironment . (EnvBlock isLoop M.empty:)  . environment

popEnvironment :: GeneratorAction ()
popEnvironment = get >>= putEnvironment . tail . environment

createVariable :: DataType -> SourceLoc -> GeneratorAction VarInfo
createVariable dataType sl = get >>= createVarHelper dataType . structMap
  where
    createVarHelper :: DataType -> StructMap -> GeneratorAction VarInfo
    createVarHelper dataType@(typename, _) structs
        | isPrimitiveType dataType      = return $ PrimitiveVar dataType
        | isStructType dataType structs = return $ StructVar dataType
        | otherwise                     = raiseFailureLoc ("Invalid typename " ++ typename) sl

insertIntoEnv :: String -> VarInfo -> GeneratorAction ()
insertIntoEnv varName varInfo =
    get >>= putEnvironment . insert varName varInfo . environment
  where
    insert :: String -> VarInfo -> Environment -> Environment
    insert varName varInfo ((EnvBlock loop envMap):rest) = EnvBlock loop (M.insert varName varInfo envMap):rest
    insert _ _ [] = []

validateInLoop :: SourceLoc -> GeneratorAction ()
validateInLoop sl = do
    env <- environment <$> get
    unless
      (envInLoop env)
      (raiseFailureLoc "Not contained in a loop" sl)

validateProgram :: Program -> Either FailureInfo Program
validateProgram (funcs, structs) =
    evalStateT
      (validateAllStructs structs >> validateAllFunctions funcs >>= \x -> return (x, structs))
      (GeneratorState M.empty [EnvBlock False M.empty])
    where 
        validateAllStructs :: [StructDefinition] -> GeneratorAction ()
        validateAllStructs = mapM_ (\x -> validateStruct x >> addStruct x)
        validateAllFunctions :: [FunctionDefinition] -> GeneratorAction [FunctionDefinition]
        validateAllFunctions = mapM (\x -> validateFunction x >>= \newFunc -> addFunctionToEnvironment x >> return newFunc)
        addFunctionToEnvironment :: FunctionDefinition -> GeneratorAction ()
        addFunctionToEnvironment (FunctionDefinition rtype name params _ _) =
            insertIntoEnv name (FunctionVar rtype params)
        validateFunction :: FunctionDefinition -> GeneratorAction FunctionDefinition
        validateFunction (FunctionDefinition rtype fname params body sl) = do
            pushEnvironment False
            addFunctionParameters params $ paramsLoc sl
            insertIntoEnv "$currentFunction" (FunctionVar rtype [])
            body <- validateSyntaxNode body
            unless (isVoidType rtype) (validateReturns body)
            popEnvironment
            return $ FunctionDefinition rtype fname params body sl
          where
            -- Ensmarten me, you can technically have dead code at the end
            validateReturns :: SyntaxNode -> GeneratorAction ()
            validateReturns node = return ()  -- TODO: this
            addFunctionParameters :: DeclList -> [SourceLoc] -> GeneratorAction ()
            addFunctionParameters = (fmap . fmap) mapZip zip
              where
                mapZip = mapM_ (\((dataType, id), sl) -> createVariable dataType sl >>= insertIntoEnv id)

validateStruct :: StructDefinition -> GeneratorAction ()
validateStruct (StructDefinition (name, memberList)) = do
    curStructs <- structMap <$> get
    unless
      (all (validateMember curStructs) memberList && membersUnique (map snd memberList))
      (raiseFailure ("Validating struct " ++ name ++ " failed") 0 0)
    when
      (null memberList)
      (raiseFailure ("Struct " ++ name ++ " has no members") 0 0)

validateMember :: StructMap -> (DataType, String) -> Bool
validateMember structs (datatype@(typename, _), id) = isPrimitiveType datatype || M.member typename structs

membersUnique :: [String] -> Bool
membersUnique names = length names == S.size nameSet
  where
    nameSet = S.fromList names
    

isPrimitiveType :: DataType -> Bool
isPrimitiveType (typename, _) = S.member typename baseTypes

isStructType :: DataType -> StructMap -> Bool
isStructType (typename, _) = M.member typename

isIntegralType :: DataType -> Bool
isIntegralType (typename, ptrList)
    | typename == "char"  = isntPtr
    | typename == "short" = isntPtr
    | typename == "int"   = isntPtr
    | typename == "long"  = isntPtr
    | otherwise           = False
  where
    isntPtr = null ptrList

isImplicitCastAllowed :: DataType -> DataType -> Bool
isImplicitCastAllowed toType fromType =
    implicitCastAllowedSingle toType fromType ||
    implicitCastAllowedSingle fromType toType ||
    isPointerCastAllowed toType fromType
  where
    implicitCastAllowedSingle :: DataType -> DataType -> Bool
    implicitCastAllowedSingle type1 type2
        | isIntegralType type1 && isFloatType type2    = True
        | type1 == type2                               = True
        | isIntegralType type1 && isIntegralType type2 = True
        | otherwise                                    = False

isPointerCastAllowed :: DataType -> DataType -> Bool
isPointerCastAllowed (toType, toPtr) (fromType, fromPtr) =
    not (null toPtr) &&
    toType == fromType &&
    length toPtr == length fromPtr &&
    last toPtr == 0

-- Syntax Tree actions (Stateful)
-- Needs to modify state to trace variable declarations and scope changes
canShadow :: String -> GeneratorAction Bool
canShadow varName = get <&> canShadowHelper varName . environment
  where
    canShadowHelper :: String -> Environment -> Bool
    canShadowHelper varName ((EnvBlock _ map):_) = not $ M.member varName map
    canShadowHelper varName [] = True

validateSyntaxNode :: SyntaxNode -> GeneratorAction SyntaxNode
validateSyntaxNode node = do
    result <- validateHelper $ getCompose $ unFix node
    return $ Fix $ Compose result
  where
    validateHelper :: (SourceLoc, SyntaxNodeF SyntaxNode) -> GeneratorAction (SourceLoc, SyntaxNodeF SyntaxNode)
    validateHelper = mapM validateSyntaxNodeF

    nodeLoc :: SourceLoc
    nodeLoc = fst $ getCompose $ unFix node

    -- Failure messages for syntax nodes
    failCantCastCondition :: DataType -> GeneratorAction ()
    failCantCastCondition condType =
        raiseFailureLoc ("Cannot convert for condition expression from " ++ showDt condType ++ " to bool") nodeLoc
    failCantCastReturn :: DataType -> DataType -> GeneratorAction ()
    failCantCastReturn t0 t1 =
        raiseFailureLoc ("Return type " ++ showDt t0 ++ " does not match function type " ++ showDt t1) nodeLoc
    failCantShadow :: String -> GeneratorAction ()
    failCantShadow id =
        raiseFailureLoc ("Cannot redeclare variable with name " ++ id) nodeLoc
    failCantDeclareVoid :: String -> GeneratorAction ()
    failCantDeclareVoid id = raiseFailureLoc ("Cannot declare the variable " ++ id ++ " with type void") nodeLoc
    failCantCastDef :: DataType -> DataType -> GeneratorAction ()
    failCantCastDef t0 t1 =
        raiseFailureLoc ("Cannot cast definition expression from " ++ showDt t0 ++ " to " ++ showDt t1) nodeLoc
    failExprInvalid :: Expr -> GeneratorAction ()
    failExprInvalid expr =
        raiseFailureLoc ("Expression typecheck failed. Expression tree:\n---\n" ++ showExprTree expr ++ "---\n") nodeLoc

    getExprDecltype :: SyntaxNode -> GeneratorAction DataType
    getExprDecltype node = case snd $ getCompose $ unFix node of 
        ExprNode expr -> return $ typeOf expr
        _             -> raiseFailureLoc "Expected an expression" nodeLoc
    getExprRoot :: SyntaxNode -> GeneratorAction Expr
    getExprRoot node = case snd $ getCompose $ unFix node of 
        ExprNode expr -> return expr
        _             -> raiseFailureLoc "Expected an expression" nodeLoc

    trueExpr :: SyntaxNode
    trueExpr = annotSyntaxEmpty (ExprNode $ annotExpr boolType $ LiteralNode (BoolConstant True))
    injectCast :: DataType -> Expr -> SyntaxNodeF SyntaxNode
    injectCast toType node = ExprNode $ annotExpr toType $ CastNode toType node

    -- Primary recursive logic for validating SyntaxNodes
    -- Fans out to validating Exprs @ ExprNode
    validateSyntaxNodeF :: SyntaxNodeF SyntaxNode -> GeneratorAction (SyntaxNodeF SyntaxNode)
    validateSyntaxNodeF EmptyNode = return EmptyNode
    validateSyntaxNodeF (SeqNode lhs rhs) = do
        lhs <- validateSyntaxNode lhs
        rhs <- validateSyntaxNode rhs
        return $ SeqNode lhs rhs
    validateSyntaxNodeF (WhileNode condition block) = do
        condition <- validateSyntaxNode condition
        condType <- getExprDecltype condition
        let condTypeName = showDt condType
        unless
          (isImplicitCastAllowed boolType condType)
          (raiseFailureLoc ("Cannot convert while condition expression from " ++ condTypeName ++ " to bool") nodeLoc)
        -- TODO: maybe add implicit casts to bool if we ever change our minds?
        pushEnvironment True
        block <- validateSyntaxNode block
        popEnvironment
        return $ WhileNode condition block
    validateSyntaxNodeF (ForNode init condition expr block) = do 
        pushEnvironment True
        init <- validateSyntaxNode init
        -- Correct a for condition that is EmptyNode to an expression that is `true`
        condition <- validateSyntaxNode condition
                  >>= \validCond -> return $ if isEmptyNode validCond
                                               then trueExpr
                                               else validCond
        condType <- getExprDecltype condition
        unless
          (isImplicitCastAllowed boolType condType)
          (failCantCastCondition condType)
        -- TODO: maybe add implicit casts to bool if we ever change our minds?
        expr <- validateSyntaxNode expr
        block <- validateSyntaxNode block
        popEnvironment
        return $ ForNode init condition expr block
    validateSyntaxNodeF (IfNode condition block) = do
        condition <- validateSyntaxNode condition
        condType <- getExprDecltype condition
        unless
          (isImplicitCastAllowed boolType condType)
          (failCantCastCondition condType)
        -- TODO: maybe add implicit casts to bool if we ever change our minds?
        pushEnvironment False
        block <- validateSyntaxNode block
        popEnvironment
        return $ IfNode condition block
    validateSyntaxNodeF (IfElseNode condition block elseBlock) = do
        condition <- validateSyntaxNode condition
        condType <- getExprDecltype condition
        let condTypeName = showDt condType
        unless
          (isImplicitCastAllowed boolType condType)
          (failCantCastCondition condType)
        -- TODO: maybe add implicit casts to bool if we ever change our minds?
        pushEnvironment False -- TODO: remove unnecessary blocks
        block <- validateSyntaxNode block
        popEnvironment
        pushEnvironment False
        elseBlock <- validateSyntaxNode elseBlock
        return $ IfElseNode condition block elseBlock
    validateSyntaxNodeF (ReturnNode expr) = do
        expr <- validateSyntaxNode expr
        exprType <- getExprDecltype expr
        funcNode <- lookupVarFailure "$currentFunction"
        let (FunctionVar funcRetType _) = funcNode
        unless
          (isImplicitCastAllowed funcRetType exprType)
          (failCantCastReturn exprType funcRetType)
        if exprType /= funcRetType
          then do
            -- Take the current ExprNode, get its Expr, inject a cast, reannotate, and return
            fmap (ReturnNode . copyAnnot expr . injectCast funcRetType)
                 (getExprRoot expr)
          else return $ ReturnNode expr
    validateSyntaxNodeF ContinueNode = do
        validateInLoop nodeLoc
        return ContinueNode
    validateSyntaxNodeF BreakNode = do
        validateInLoop nodeLoc
        return BreakNode
    validateSyntaxNodeF (BlockNode block) = do
        pushEnvironment False
        block <- validateSyntaxNode block
        popEnvironment
        return $ BlockNode block
    validateSyntaxNodeF sn@(DeclarationNode declaredType id) = do
        unlessM (canShadow id) (failCantShadow id)
        when (declaredType == voidType) (failCantDeclareVoid id)
        createVariable declaredType nodeLoc >>= insertIntoEnv id
        return sn
    validateSyntaxNodeF (DefinitionNode declaredType id expr) = do
        unlessM (canShadow id) (failCantShadow id)
        when (declaredType == voidType) (failCantDeclareVoid id)
        createVariable declaredType nodeLoc >>= insertIntoEnv id
        expr <- validateSyntaxNode expr
        exprType <- getExprDecltype expr
        unless (isImplicitCastAllowed declaredType exprType) (failCantCastDef declaredType exprType)
        if exprType /= declaredType
          then do
            fmap (DefinitionNode declaredType id . copyAnnot expr . injectCast declaredType)
                 (getExprRoot expr)
          else return $ DefinitionNode declaredType id expr
    validateSyntaxNodeF (ExprNode expression) = do
        expression <- computeDecltype <$> (environment <$> get)
                                      <*> (structMap <$> get)
                                      <*> pure expression
        when (invalidType == typeOf expression) (failExprInvalid expression)
        return $ ExprNode expression

-- See below for binary operation casting rules
-- Takes a binary op, lhs, rhs and returns the (result type, operand cast type)
binaryTypeResult
    :: StructMap
    -> BinaryOp
    -> DataType
    -> DataType
    -> (DataType, DataType, DataType)
binaryTypeResult structs op lhsType rhsType
    | lhsType == invalidType   = invalidPair
    | rhsType == invalidType   = invalidPair
    | isBaseType lhsType && M.member (fst lhsType) structs = invalidPair
    | isBaseType rhsType && M.member (fst rhsType) structs = invalidPair
    | op == Addition           = decideAddition
    | op == Multiplication     = decideMultiplication
    | op == Subtraction        = decideSubtraction
    | op == Division           = decideDivision
    | op == Modulus            = decideModulus
    | op == Equal              = decideCompare
    | op == NotEqual           = decideCompare
    | op == LessThan           = decideRelCompare
    | op == GreaterThan        = decideRelCompare
    | op == GreaterThanOrEqual = decideRelCompare
    | op == LessThanOrEqual    = decideRelCompare
    | op == Or                 = decideLogical
    | op == And                = decideLogical
    | otherwise                = invalidPair
  where
    invalidPair = dupe3 invalidType
    typeFormMatches tp1 tp2 = fst tp1 == fst tp2 && length (snd tp1) == length (snd tp2)
    decideCompare :: (DataType, DataType, DataType)
    decideCompare
        | typeFormMatches lhsType rhsType                  = (boolType, lhsType, rhsType)
        | isIntegralType lhsType && isIntegralType rhsType = dupe2nd boolType $ largestType lhsType rhsType
        | isIntegralType lhsType && isFloatType rhsType    = (boolType, rhsType, rhsType)
        | isFloatType lhsType && isIntegralType rhsType    = (boolType, lhsType, lhsType)
        | otherwise                                        = invalidPair
    decideRelCompare :: (DataType, DataType, DataType)
    decideRelCompare
        | isBoolType lhsType || isBoolType rhsType = invalidPair
        | otherwise                                = decideCompare
    decideLogical :: (DataType, DataType, DataType)
    decideLogical
        | lhsType == boolType && rhsType == boolType = dupe3 boolType
        | otherwise                                  = invalidPair
    decideModulus :: (DataType, DataType, DataType)
    decideModulus
        | isIntegralType lhsType && isIntegralType rhsType = dupe3 $ largestType lhsType rhsType
        | otherwise                                        = invalidPair
    decideAddition :: (DataType, DataType, DataType)
    decideAddition
    -- ptr + integral (ptr)
        | isPointerType lhsType && isIntegralType rhsType  = (lhsType, lhsType, rhsType)
        | isPointerType rhsType && isIntegralType lhsType  = (rhsType, lhsType, rhsType)
    -- integral + integral (largest of 2)
        | isIntegralType lhsType && isIntegralType rhsType = dupe3 $ largestType lhsType rhsType
    -- integral + float (float)
        | isIntegralType lhsType && isFloatType rhsType    = dupe3 floatType
        | isIntegralType rhsType && isFloatType lhsType    = dupe3 floatType
    -- float + float (float)
        | isFloatType lhsType && isFloatType rhsType       = dupe3 floatType
    -- anything else = invalid
        | otherwise = invalidPair
    decideMultiplication :: (DataType, DataType, DataType)
    decideMultiplication
    -- either are pointers -> not allowed
        | isPointerType lhsType || isPointerType rhsType = invalidPair
        | otherwise = decideAddition
    decideSubtraction :: (DataType, DataType, DataType)
    decideSubtraction
    -- ptr - ptr (long)
        | isPointerType lhsType && isPointerType rhsType &&
          typeFormMatches lhsType rhsType = (ptrdiffType, lhsType, rhsType)
        | isPointerType rhsType && isBaseType rhsType = invalidPair
        | otherwise = decideAddition
    decideDivision :: (DataType, DataType, DataType)
    decideDivision = decideMultiplication

unaryTypeResult :: UnaryOp -> DataType -> DataType
unaryTypeResult op subType
    | subType == invalidType = invalidType
    | op == Negate           = decideNegate subType
    | op == Not              = decideNot subType
    | op == Reference        = decideReference subType
    | op == Dereference      = decideDereference subType
    | otherwise              = invalidType
  where
    decideNegate :: DataType -> DataType
    decideNegate tp
        | isFloatType tp || isIntegralType tp = tp
        | otherwise = invalidType
    decideNot :: DataType -> DataType
    decideNot tp
        | isBoolType tp = tp
        | otherwise     = invalidType
    decideReference :: DataType -> DataType
    decideReference (typeName, ptrList) = (typeName, 0:ptrList)
    decideDereference :: DataType -> DataType
    decideDereference (typeName, ptrList)
        | not (null ptrList) = (typeName, tail ptrList)
        | otherwise          = invalidType

-- This is the core typechecking function
-- It will act as both the typechecker as well as the cast generator for a full Expr tree
computeDecltype :: Environment -> StructMap -> Expr -> Expr
computeDecltype env structs = foldFix (Fix . Compose . first (arr ExprType) . alg . snd . getCompose)
  where
    lookup :: String -> VarInfo
    lookup = fromMaybe (PrimitiveVar invalidType) . flip lookupVar env
    -- Cast node insertion rules:
    -- If a given node is invalid, keep it as invalid
    -- If the given node's type matches the to the target, don't insert a cast
    -- If the given node's type does not match the target but is implicitly castable, make a cast
    -- Otherwise mark the uncastable node with a cast node of invalid type
    castOrInvalid :: Expr -> DataType -> Expr
    castOrInvalid expr toType
        | dataType == invalidType               = expr
        | dataType == toType                    = expr
        | isImplicitCastAllowed dataType toType = castExpr toType 
        | otherwise                             = castExpr invalidType 
      where
        (ExprType dataType, exprNode) = getCompose $ unFix expr
        castExpr :: DataType -> Expr
        castExpr toType = Fix $ Compose (ExprType toType, CastNode toType expr)

    fixupFunction
        :: DataType 
        -> [(DataType, String)]
        -> String
        -> [Expr]
        -> (DataType, ExprF Expr)
    fixupFunction rtype params name args
        | length args /= length params              = (invalidType, FunctionCallNode name args)
        | any ((==invalidType) . typeOf) castedArgs = (invalidType, FunctionCallNode name args)
        | otherwise                                 = (rtype, FunctionCallNode name castedArgs)
      where
        castedArgs = zipWith castOrInvalid args (map fst params)

    -- By our bottom-up typecheck, if it is identifier & valid, then it must be prim/struct
    isIdVar :: Expr -> Bool
    isIdVar expr = case snd $ getCompose $ unFix expr of
        IdentifierNode id -> True
        _                 -> False

    -- 1. Compute the decltype of a given expression node
    -- 2. Insert casting nodes for viable implicit casts
    -- 3. If any children are invalid, propogate
    -- 4. If any cast is impossible, propogate
    alg :: ExprF Expr -> (DataType, ExprF Expr)
    alg n@(IdentifierNode name) = case lookup name of
        PrimitiveVar t   -> (t, n)
        StructVar    t   -> (t, n)
        _                -> (invalidType, n)
    alg n@(LiteralNode const) = case const of
        IntConstant _    -> (longType, n)
        FloatConstant _  -> (floatType, n)
        BoolConstant _   -> (boolType, n)
        StringConstant s -> (("char", [length s + 1]), n)
    alg n@(FunctionCallNode name args) =
        case lookup name of
            FunctionVar rtype params -> fixupFunction rtype params name args
            _                        -> (invalidType, n)
    alg n@(ArrayIndexNode arr idx)
        | not $ isIntegralType $ typeOf idx = (invalidType, n)
        | otherwise = (unaryTypeResult Dereference $ typeOf arr, n)
    alg n@(ParenthesisNode sub) = (typeOf sub, n)
    alg n@(BinaryOpNode op lhs rhs)
        | typeOf lhsCast == invalidType = (invalidType, n)
        | typeOf rhsCast == invalidType = (invalidType, n)
        | otherwise                     = (binOpType, BinaryOpNode op lhsCast rhsCast)
      where
        (binOpType, lhsType, rhsType) = binaryTypeResult structs op (typeOf lhs) (typeOf rhs)
        lhsCast = castOrInvalid lhs lhsType
        rhsCast = castOrInvalid rhs rhsType
    alg n@(UnaryOpNode op sub)
        | typeOf sub == invalidType            = (invalidType, n)
        | op == Reference && not (isIdVar sub) = (invalidType, n)
        | otherwise                            = (uType, UnaryOpNode op sub)
      where
        uType = unaryTypeResult op $ typeOf sub
    alg n@(AssignmentNode op lhs rhs) -- TODO: this should probably be broken into a (x = x op y | op /= NoOp)
        | typeOf lhs == invalidType    = (invalidType, n)
        | typeOf newRhs == invalidType = (invalidType, n)
        | otherwise                    = (typeOf lhs, AssignmentNode op lhs newRhs)
      where
        newRhs = castOrInvalid rhs $ typeOf lhs
    -- This is very stupid, I hate throwing context & state into expressions like this, it really shouldn't happen 
    alg n@(MemberAccessNode isPtr lhs rhs)
        | typeOf lhs == invalidType             = (invalidType, n)
        | isPtr && isBasePointer (typeOf lhs)   = memberAccessHelper maybeStructDef
        | not isPtr && isValueType (typeOf lhs) = memberAccessHelper maybeStructDef
        | otherwise                             = (invalidType, n)
      where
        memberAccessHelper :: Maybe StructDefinition -> (DataType, ExprF Expr)
        memberAccessHelper (Just def) 
            | rhsFixedType == invalidType = (invalidType, n)
            | otherwise                   = (rhsFixedType, MemberAccessNode isPtr lhs rhsFixed)
          where
            rhsFixed = computeMemberAccess def rhs
            rhsFixedType = typeOf rhsFixed
            newN = MemberAccessNode 
        memberAccessHelper _          = (invalidType, n)
        maybeStructDef :: Maybe StructDefinition
        maybeStructDef = M.lookup (fst $ typeOf lhs) structs
    alg n@(CastNode datatype sub) = -- TODO: add checks for explicit cast
        if typeOf sub == invalidType
          then (invalidType, n)
          else (datatype, n)
    -- This will be dealt with by recomputeDeclWithStruct
    alg n@(StructMemberNode _) = (invalidType, n)

    -- why do structs even exist? I kinda just hate them
    computeMemberAccess :: StructDefinition -> Expr -> Expr
    computeMemberAccess struct = foldFix (Fix . Compose . alg . getCompose)
      where
        alg :: (ExprType, ExprF Expr) -> (ExprType, ExprF Expr)
        alg (_, n@(StructMemberNode name)) = (ExprType $ getMemberType struct name, n)
        alg (_, n@(ArrayIndexNode arr _))  = (ExprType $ unaryTypeResult Dereference $ typeOf arr, n)
        alg n                              = n
