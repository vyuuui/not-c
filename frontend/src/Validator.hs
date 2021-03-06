{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module Validator ( validateProgram ) where

import CompilerShared
import CompilerShow
import Control.Arrow
import Control.Monad
import Control.Monad.Loops
import Control.Monad.Trans.State.Lazy
import Data.Either
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
lookupVarFailure :: String -> ValidatorAction VarInfo
lookupVarFailure id = do
    maybeVar <- lookupVar id <$> (environment <$> get)
    maybe
      (raiseFailure ("Undefined id " ++ id) 0 0)
      return
      maybeVar

type StructMap = M.Map String StructDefinition

data ValidatorState = ValidatorState
    { structMap :: StructMap
    , environment :: Environment
    } deriving Show

type ValidatorAction = StateT ValidatorState (Either FailureInfo)

unlessM :: Monad m => m Bool -> m () -> m ()
unlessM test def = test >>= (`unless` def)
whenM :: Monad m => m Bool -> m () -> m ()
whenM test def = test >>= (`when` def)

putEnvironment :: Environment -> ValidatorAction ()
putEnvironment newEnv = modify (\(ValidatorState structs env) -> ValidatorState structs newEnv)
putStructs :: StructMap -> ValidatorAction ()
putStructs newStructs = modify (\(ValidatorState structs env) -> ValidatorState newStructs env)
addStruct :: StructDefinition -> ValidatorAction ()
addStruct struct@(name, _) =
    get >>= putStructs . M.insert name struct . structMap

pushEnvironment :: Bool -> ValidatorAction ()
pushEnvironment isLoop =
    get >>= putEnvironment . (EnvBlock isLoop M.empty:)  . environment

popEnvironment :: ValidatorAction ()
popEnvironment = get >>= putEnvironment . tail . environment

createVariable :: DataType -> SourceLoc -> ValidatorAction VarInfo
createVariable dataType sl = get >>= createVarHelper dataType . structMap
  where
    createVarHelper :: DataType -> StructMap -> ValidatorAction VarInfo
    createVarHelper dataType@(typename, _) structs
        | isPrimitiveType dataType      = return $ PrimitiveVar dataType
        | isStructType dataType structs = return $ StructVar dataType
        | otherwise                     = raiseFailureLoc ("Invalid typename " ++ typename) sl

insertIntoEnv :: String -> VarInfo -> ValidatorAction ()
insertIntoEnv varName varInfo =
    get >>= putEnvironment . insert varName varInfo . environment
  where
    insert :: String -> VarInfo -> Environment -> Environment
    insert varName varInfo ((EnvBlock loop envMap):rest) = EnvBlock loop (M.insert varName varInfo envMap):rest
    insert _ _ [] = []

validateInLoop :: SourceLoc -> ValidatorAction ()
validateInLoop sl = do
    env <- environment <$> get
    unless
      (envInLoop env)
      (raiseFailureLoc "Not contained in a loop" sl)

validateProgram :: Program -> Either FailureInfo Program
validateProgram (globals, structs) =
    evalStateT
      (validateAllStructs structs >> validateAllGlobals globals >>= \x -> return (x, structs))
      (ValidatorState M.empty [EnvBlock False M.empty])
    where 
        validateAllStructs :: [StructDefinition] -> ValidatorAction ()
        validateAllStructs = mapM_ (\x -> addStruct x >> validateStruct x)
        validateAllGlobals :: [Global] -> ValidatorAction [Global]
        validateAllGlobals = mapM validateGlobal
        validateGlobal :: Global -> ValidatorAction Global
        validateGlobal (Function fn) =
            addFunctionToEnvironment fn >> validateFunction fn >>= return . Function
        validateGlobal (GlobalVar node) =
            validateSyntaxNode node >>= return . GlobalVar
        addFunctionToEnvironment :: FunctionDefinition -> ValidatorAction ()
        addFunctionToEnvironment (FunctionDefinition rtype name params _ _) =
            insertIntoEnv name (FunctionVar rtype params)
        validateFunction :: FunctionDefinition -> ValidatorAction FunctionDefinition
        validateFunction (FunctionDefinition rtype fname params body sl) = do
            pushEnvironment False
            addFunctionParameters params $ paramsLoc sl
            insertIntoEnv "$currentFunction" (FunctionVar rtype [])
            body <- skipBlockAndValidate body
            unless (isVoidType rtype) (validateReturns body)
            popEnvironment
            return $ FunctionDefinition rtype fname params body sl
          where
            -- Ensmarten me, you can technically have dead code at the end
            validateReturns :: SyntaxNode -> ValidatorAction ()
            validateReturns node = return ()  -- TODO: this
            addFunctionParameters :: DeclList -> [SourceLoc] -> ValidatorAction ()
            addFunctionParameters = (fmap . fmap) mapZip zip
              where
                mapZip = mapM_ (\((dataType, id), sl) -> createVariable dataType sl >>= insertIntoEnv id)

validateStruct :: StructDefinition -> ValidatorAction ()
validateStruct (name, memberList) = do
    curStructs <- structMap <$> get
    when
      (any (\(dt@(tp, ptr), _) -> (tp == name) && (null ptr || isArrayType dt)) memberList)
      (raiseFailure ("Struct " ++ name ++ " cannot have non-pointer self reference") 0 0)
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

isImplicitCastAllowed :: DataType -> DataType -> Bool
isImplicitCastAllowed toType@(toName, toPtr) fromType@(fromName, fromPtr) =
    implicitCastAllowedSingle toType fromType ||
    implicitCastAllowedSingle fromType toType ||
    isPointerCastAllowed
  where
    implicitCastAllowedSingle :: DataType -> DataType -> Bool
    implicitCastAllowedSingle type1 type2
        | isIntegralType type1 && isFloatType type2    = True
        | type1 == type2                               = True
        | isIntegralType type1 && isIntegralType type2 = True
        | otherwise                                    = False
    isPointerCastAllowed =
        isPointerType toType &&
        ((not (isArrayType toType) &&
          fromType == nullType) ||
         (toName == fromName &&
          length toPtr == length fromPtr &&
          last toPtr == 0))

-- Syntax Tree actions (Stateful)
-- Needs to modify state to trace variable declarations and scope changes
canShadow :: String -> ValidatorAction Bool
canShadow varName = get <&> canShadowHelper varName . environment
  where
    canShadowHelper :: String -> Environment -> Bool
    canShadowHelper varName ((EnvBlock _ map):_) = not $ M.member varName map
    canShadowHelper varName [] = True

skipBlockAndValidate :: SyntaxNode -> ValidatorAction SyntaxNode
skipBlockAndValidate node = do
    let (loc, nodeF) = getCompose $ unFix node
    result <- case nodeF of
        (BlockNode sub) -> validateSyntaxNode sub
        _               -> raiseFailureLoc "Expected to find a block" loc
    return $ Fix $ Compose (loc, BlockNode result)

validateSyntaxNode :: SyntaxNode -> ValidatorAction SyntaxNode
validateSyntaxNode node = do
    result <- validateHelper $ getCompose $ unFix node
    return $ Fix $ Compose result
  where
    validateHelper :: (SourceLoc, SyntaxNodeF SyntaxNode) -> ValidatorAction (SourceLoc, SyntaxNodeF SyntaxNode)
    validateHelper = mapM validateSyntaxNodeF

    nodeLoc :: SourceLoc
    nodeLoc = fst $ getCompose $ unFix node

    -- Failure messages for syntax nodes
    failCantCastCondition :: DataType -> ValidatorAction ()
    failCantCastCondition condType =
        raiseFailureLoc ("Cannot convert for condition expression from " ++ showDt condType ++ " to bool") nodeLoc
    failCantCastReturn :: DataType -> DataType -> ValidatorAction ()
    failCantCastReturn t0 t1 =
        raiseFailureLoc ("Return type " ++ showDt t0 ++ " does not match function type " ++ showDt t1) nodeLoc
    failCantShadow :: String -> ValidatorAction ()
    failCantShadow id =
        raiseFailureLoc ("Cannot redeclare variable with name " ++ id) nodeLoc
    failCantDeclareVoid :: String -> ValidatorAction ()
    failCantDeclareVoid id = raiseFailureLoc ("Cannot declare the variable " ++ id ++ " with type void") nodeLoc
    failCantCastDef :: DataType -> DataType -> ValidatorAction ()
    failCantCastDef t0 t1 =
        raiseFailureLoc ("Cannot cast definition expression from " ++ showDt t0 ++ " to " ++ showDt t1) nodeLoc
    failExprInvalid :: Expr -> ValidatorAction ()
    failExprInvalid expr = do
        exprErr <- findExprError <$> (environment <$> get) <*> (structMap <$> get) <*> pure expr
        raiseFailureLoc (message exprErr) (location exprErr)

    getExprDecltype :: SyntaxNode -> ValidatorAction DataType
    getExprDecltype node = case snd $ getCompose $ unFix node of 
        ExprNode expr -> return $ typeOf expr
        _             -> raiseFailureLoc "Expected an expression" nodeLoc
    getExprRoot :: SyntaxNode -> ValidatorAction Expr
    getExprRoot node = case snd $ getCompose $ unFix node of 
        ExprNode expr -> return expr
        _             -> raiseFailureLoc "Expected an expression" nodeLoc

    trueExpr :: SyntaxNode
    trueExpr = annotSyntaxEmpty (ExprNode $ annotExpr boolType RValue (SourceLoc 0 0) $ LiteralNode (BoolConstant True))
    injectCast :: DataType -> Expr -> SyntaxNodeF SyntaxNode
    injectCast toType node = ExprNode $ annotExpr toType (handednessOf node) (sourceLocOf node) $ CastNode toType node

    -- Primary recursive logic for validating SyntaxNodes
    -- Fans out to validating Exprs @ ExprNode
    validateSyntaxNodeF :: SyntaxNodeF SyntaxNode -> ValidatorAction (SyntaxNodeF SyntaxNode)
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
    validateSyntaxNodeF (ForNode init condition expr block or) = do 
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
        -- We want to count the for body in the same "scope" as the iterator
        block <- skipBlockAndValidate block
        popEnvironment
        or <- validateSyntaxNode or
        return $ ForNode init condition expr block or
    validateSyntaxNodeF (PrintNode expr) = do
        expr <- validateSyntaxNode expr
        getExprDecltype expr
        return $ PrintNode expr
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
        exprType <- if isEmptyNode expr then return voidType else getExprDecltype expr
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
    | lhsType == invalidType   = invalidResult
    | rhsType == invalidType   = invalidResult
    | isBaseType lhsType && M.member (fst lhsType) structs = invalidResult
    | isBaseType rhsType && M.member (fst rhsType) structs = invalidResult
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
    | otherwise                = invalidResult
  where
    invalidResult = (invalidType, lhsType, rhsType)
    typeFormMatches tp1 tp2 = fst tp1 == fst tp2 && length (snd tp1) == length (snd tp2)
    decideCompare :: (DataType, DataType, DataType)
    decideCompare
        | typeFormMatches lhsType rhsType                  = (boolType, lhsType, rhsType)
        | isIntegralType lhsType && isIntegralType rhsType = dupe2nd boolType $ largestType lhsType rhsType
        | isIntegralType lhsType && isFloatType rhsType    = (boolType, rhsType, rhsType)
        | isFloatType lhsType && isIntegralType rhsType    = (boolType, lhsType, lhsType)
        | lhsType == nullType                              = (boolType, rhsType, rhsType)
        | rhsType == nullType                              = (boolType, lhsType, lhsType)
        | otherwise                                        = invalidResult
    decideRelCompare :: (DataType, DataType, DataType)
    decideRelCompare
        | isBoolType lhsType || isBoolType rhsType = invalidResult
        | otherwise                                = decideCompare
    decideLogical :: (DataType, DataType, DataType)
    decideLogical
        | lhsType == boolType && rhsType == boolType = dupe3 boolType
        | otherwise                                  = invalidResult
    decideModulus :: (DataType, DataType, DataType)
    decideModulus
        | isIntegralType lhsType && isIntegralType rhsType = dupe3 $ largestType lhsType rhsType
        | otherwise                                        = invalidResult
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
        | otherwise = invalidResult
    decideMultiplication :: (DataType, DataType, DataType)
    decideMultiplication
    -- either are pointers -> not allowed
        | isPointerType lhsType || isPointerType rhsType = invalidResult
        | otherwise = decideAddition
    decideSubtraction :: (DataType, DataType, DataType)
    decideSubtraction
    -- ptr - ptr (long)
        | isPointerType lhsType && isPointerType rhsType &&
          typeFormMatches lhsType rhsType = (ptrdiffType, lhsType, rhsType)
        | isPointerType rhsType && isBaseType rhsType = invalidResult
        | otherwise = decideAddition
    decideDivision :: (DataType, DataType, DataType)
    decideDivision = decideMultiplication

compoundAssignable :: DataType -> Bool
compoundAssignable tp = isIntegralType tp || (isPointerType tp && not (isArrayType tp)) || isFloatType tp

unaryTypeResult :: UnaryOp -> (DataType, Handedness) -> (DataType, Handedness)
unaryTypeResult op (subType, subHandedness)
    | subType == invalidType = (invalidType, RValue)
    | op == Negate           = decideNegate subType
    | op == Not              = decideNot subType
    | op == Reference        = decideReference subType
    | op == Dereference      = decideDereference subType
    | op == PrefixInc        = decidePrefix subType
    | op == PrefixDec        = decidePrefix subType
    | otherwise              = (invalidType, RValue)
  where
    decideNegate :: DataType -> (DataType, Handedness)
    decideNegate tp
        | isFloatType tp || isIntegralType tp = (tp, RValue)
        | otherwise = (invalidType, RValue)
    decideNot :: DataType -> (DataType, Handedness)
    decideNot tp
        | isBoolType tp = (tp, RValue)
        | otherwise     = (invalidType, RValue)
    decideReference :: DataType -> (DataType, Handedness)
    decideReference (typeName, ptrList) = ((typeName, 0:ptrList), RValue)
    decideDereference :: DataType -> (DataType, Handedness)
    decideDereference (typeName, ptrList)
        | (typeName, tail ptrList) == voidType = (invalidType, LValue)
        | not (null ptrList) = ((typeName, tail ptrList), LValue)
        | otherwise          = (invalidType, LValue)
    decidePrefix :: DataType -> (DataType, Handedness)
    decidePrefix tp
        | subHandedness == RValue = (invalidType, RValue)
        | compoundAssignable tp  = (tp, RValue)
        | otherwise               = (invalidType, RValue)

-- This is the core typechecking function
-- It will act as both the typechecker as well as the cast generator for a full Expr tree
computeDecltype :: Environment -> StructMap -> Expr -> Expr
computeDecltype env structs = foldFix (Fix . Compose . alg . getCompose)
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
        | isImplicitCastAllowed toType dataType = castExpr toType toType
        | otherwise                             = castExpr invalidType toType
      where
        (ExprInfo dataType hd sl, exprNode) = getCompose $ unFix expr
        castExpr :: DataType -> DataType -> Expr
        castExpr lblType toType = Fix $ Compose (ExprInfo lblType hd sl, CastNode toType expr)

    -- By our bottom-up typecheck, if it is identifier & valid, then it must be prim/struct
    isIdVar :: Expr -> Bool
    isIdVar expr = case snd $ getCompose $ unFix expr of
        IdentifierNode id -> True
        _                 -> False

    -- 1. Compute the decltype of a given expression node
    -- 2. Insert casting nodes for viable implicit casts
    -- 3. If any children are invalid, propogate
    -- 4. If any cast is impossible, propogate
    alg :: (ExprInfo, ExprF Expr) -> (ExprInfo, ExprF Expr)
    alg (ExprInfo _ _ sl, n@(IdentifierNode name)) = case lookup name of
        PrimitiveVar t   -> (ExprInfo t LValue sl, n)
        StructVar    t   -> (ExprInfo t LValue sl, n)
        _                -> (ExprInfo invalidType LValue sl, n)
    alg (ExprInfo _ _ sl, n@(LiteralNode const)) = case const of
        CharConstant _   -> (ExprInfo charType RValue sl, n)
        IntConstant _    -> (ExprInfo longType RValue sl, n)
        FloatConstant _  -> (ExprInfo floatType RValue sl, n)
        BoolConstant _   -> (ExprInfo boolType RValue sl, n)
        StringConstant s -> (ExprInfo ("char", [length s + 1]) RValue sl, n)
        NullConstant     -> (ExprInfo nullType RValue sl, n)
    alg (ExprInfo _ _ sl, n@(ArrayLiteralNode exprs)) =
        let types = map typeOf exprs
            firstElem@(firstTp, firstPtr) = head types
        in if | elem invalidType types  -> (ExprInfo invalidType RValue sl, n)
              | all (==firstElem) types -> (ExprInfo (firstTp, length exprs:firstPtr) RValue sl, n)
              | otherwise               -> (ExprInfo invalidType RValue sl, n)
    alg (ExprInfo _ _ sl, n@(FunctionCallNode name args)) =
        case lookup name of
            FunctionVar rtype params -> fixupFunction rtype params
            _                        -> (ExprInfo invalidType RValue sl, n)
      where
        fixupFunction :: DataType -> DeclList -> (ExprInfo, ExprF Expr)
        fixupFunction rtype params
            | length args /= length params =
                (annot invalidType, FunctionCallNode name args)
            | any ((==invalidType) . typeOf) castedArgs =
                (annot invalidType, FunctionCallNode name castedArgs)
            | otherwise = (annot rtype, FunctionCallNode name castedArgs)
          where
            annot tp = ExprInfo tp RValue sl
            castedArgs = zipWith castOrInvalid args (map fst params)
    alg (ExprInfo _ _ sl, n@(ArrayIndexNode arr idx))
        | not $ isIntegralType $ typeOf idx = (ExprInfo invalidType RValue sl, n)
        | otherwise =
            (uncurry3 ExprInfo (combine3 (unaryTypeResult Dereference (typeOf arr, handednessOf arr)) sl), n)
    alg (ExprInfo _ _ sl, n@(ParenthesisNode sub)) = (ExprInfo (typeOf sub) (handednessOf sub) sl, n)
    alg (ExprInfo _ _ sl, n@(BinaryOpNode op lhs rhs))
        | typeOf lhsCast == invalidType = (ExprInfo invalidType RValue sl, BinaryOpNode op lhsCast rhsCast)
        | typeOf rhsCast == invalidType = (ExprInfo invalidType RValue sl, BinaryOpNode op lhsCast rhsCast)
        | otherwise                     = (ExprInfo binOpType RValue sl, BinaryOpNode op lhsCast rhsCast)
      where
        (binOpType, lhsType, rhsType) = binaryTypeResult structs op (typeOf lhs) (typeOf rhs)
        lhsCast = castOrInvalid lhs lhsType
        rhsCast = castOrInvalid rhs rhsType
    alg (ExprInfo _ _ sl, n@(UnaryOpNode op sub))
        | typeOf sub == invalidType            = (ExprInfo invalidType RValue sl, n)
        | op == Reference && not (isIdVar sub) = (ExprInfo invalidType RValue sl, n)
        | otherwise                            = (ExprInfo uType uHand sl, n)
      where
        (uType, uHand) = unaryTypeResult op (typeOf sub, handednessOf sub)
    alg (ExprInfo _ _ sl, n@(PostfixOpNode op sub))
        | typeOf sub == invalidType  = (ExprInfo invalidType RValue sl, n)
        | handednessOf sub /= LValue = (ExprInfo invalidType RValue sl, n)
        | compoundAssignable (typeOf sub) = (ExprInfo (typeOf sub) RValue sl, n)
        | otherwise = (ExprInfo invalidType RValue sl, n)
      where
        typeChecks = [isIntegralType, isFloatType, (isPointerType &&& (not . isArrayType)) >>> uncurry (&&)]
    alg (ExprInfo _ _ sl, n@(AssignmentNode NoOp lhs rhs))
        | typeOf lhs == invalidType    = (ExprInfo invalidType LValue sl, n)
        | handednessOf lhs /= LValue   = (ExprInfo invalidType LValue sl, n)
        | typeOf newRhs == invalidType = if isArrayType (typeOf lhs) && canCopyArray
                                           then (ExprInfo (typeOf lhs) LValue sl, n)
                                           else (ExprInfo invalidType LValue sl, AssignmentNode NoOp lhs newRhs)
        | otherwise                    = (ExprInfo (typeOf lhs) LValue sl, AssignmentNode NoOp lhs newRhs)
      where
        newRhs = castOrInvalid rhs $ typeOf lhs
        canCopyArray = isArrayType (typeOf rhs) &&
                       (lhsTn == rhsTn) &&
                       (head lhsPtr >= head rhsPtr) &&
                       (tail lhsPtr == tail rhsPtr)
          where
            (lhsTn, lhsPtr) = typeOf lhs
            (rhsTn, rhsPtr) = typeOf rhs
    alg (ExprInfo _ _ sl, n@(AssignmentNode op lhs rhs))
        | typeOf lhs == invalidType                     = (ExprInfo invalidType LValue sl, n)
        | typeOf rhs == invalidType                     = (ExprInfo invalidType LValue sl, n)
        | handednessOf lhs /= LValue                    = (ExprInfo invalidType LValue sl, n)
        | not $ compoundAssignable $ typeOf lhs        = (ExprInfo invalidType LValue sl, n)
        | rhsType == invalidType                        = (ExprInfo invalidType LValue sl, AssignmentNode op lhs rhsCast)
        | not $ isImplicitCastAllowed lhsType binOpType = (ExprInfo invalidType LValue sl, AssignmentNode op lhs rhsCast)
        | otherwise                                     = (ExprInfo lhsType LValue sl, AssignmentNode op lhs rhsCast)
      where
        convertBinaryOp PlusEq = Addition
        convertBinaryOp MinusEq = Subtraction
        convertBinaryOp MulEq = Multiplication
        convertBinaryOp DivEq = Division
        convertBinaryOp ModEq = Modulus
        convertBinaryOp _     = error "Assignment op is not binary"
        (binOpType, lhsType, rhsType) = binaryTypeResult structs (convertBinaryOp op) (typeOf lhs) (typeOf rhs)
        rhsCast = castOrInvalid rhs rhsType

    -- This is very stupid, I hate throwing context & state into expressions like this, it really shouldn't happen 
    alg (ExprInfo _ _ sl, n@(MemberAccessNode isPtr lhs rhs))
        | typeOf lhs == invalidType             = (ExprInfo invalidType LValue sl, n)
        | isPtr && isBasePointer (typeOf lhs)   = fixMemberAccess
        | not isPtr && isValueType (typeOf lhs) = fixMemberAccess
        | otherwise                             = (ExprInfo invalidType LValue sl, n)
      where
        fixMemberAccess :: (ExprInfo, ExprF Expr)
        fixMemberAccess =
            let fixedRhs = maybe (ExprInfo invalidType LValue sl, n)
                  (fixStructMember $ getCompose $ unFix rhs)
                  (M.lookup (fst $ typeOf lhs) structs)
                annotRhs = Fix $ Compose fixedRhs
            in (ExprInfo (typeOf annotRhs) LValue sl, MemberAccessNode isPtr lhs annotRhs)
        fixStructMember :: (ExprInfo, ExprF Expr) -> StructDefinition -> (ExprInfo, ExprF Expr)
        fixStructMember (ExprInfo _ _ sl, n@(StructMemberNode name)) struct =
            (ExprInfo (getMemberType struct name) LValue sl, n)
        fixStructMember _ _ = error "Member access contains non-struct-member rhs"
    alg (ExprInfo _ _ sl, n@(CastNode dataType sub)) =
        if validCast dataType (typeOf sub)
          then (ExprInfo dataType RValue sl, n)
          else (ExprInfo invalidType RValue sl, n)
      where
        validCast :: DataType -> DataType -> Bool
        validCast to from
            | isIntegralType to && isIntegralType from         = True
            | to == floatType && isIntegralType from           = True
            | isIntegralType to && from == floatType           = True
            | isIntegralType to && isExclusivePointer from     = True
            | isExclusivePointer to && isIntegralType from     = True
            | to == boolType && isIntegralType from            = True
            | isIntegralType to && from == boolType            = True
            | isExclusivePointer to && isExclusivePointer from = True
            | isExclusivePointer to && isArrayType from        = True
            | otherwise                                        = False
    -- This will be dealt with by recomputeDeclWithStruct
    alg (ExprInfo _ _ sl, n@(StructMemberNode _)) = (ExprInfo invalidType LValue sl, n)
    alg (ExprInfo _ _ sl, n@(DynamicAllocationNode dataType count))
        | dataType == voidType          = (ExprInfo invalidType RValue sl, n)
        | isIntegralType (typeOf count) = (ExprInfo (second (0:) dataType) RValue sl, n)
        | otherwise                     = (ExprInfo invalidType RValue sl, n)
    alg (ExprInfo _ _ sl, n@(DynamicFreeNode address))
        | isExclusivePointer (typeOf address) = (ExprInfo voidType RValue sl, n)
        | otherwise                           = (ExprInfo invalidType RValue sl, n)

data ExprError = ExprError
    { location :: SourceLoc
    , message :: String
    , nodeType :: ExprF ()
    }

type ErrOrType = Either ExprError ExprInfo

findExprError :: Environment -> StructMap -> Expr -> ExprError
findExprError env structs expr =
    case foldFix (alg . getCompose) expr of
        Left msg -> msg
        Right _  -> error "findExprError called with no error present"
  where
    subType t = case t of
        Left _ -> invalidType
        Right info -> dataType info
    subHandedness t = case t of
        Left _ -> RValue
        Right info -> handedness info
    showSub t = showDt $ subType t

    makeErr :: (ExprInfo, ExprF a) -> String -> ErrOrType
    makeErr (info, node) msg = Left $ ExprError { location = sourceLoc info, message = msg, nodeType = void node }

    alg :: (ExprInfo, ExprF ErrOrType) -> ErrOrType
    alg n@(info, IdentifierNode name)
        | dataType info == invalidType = makeErr n $ "Couldn't find identifier named " ++ name
        | otherwise = Right info
    alg n@(info, StructMemberNode name)
        | dataType info == invalidType = makeErr n ""
        | otherwise = Right info
    alg n@(info, LiteralNode _) = Right info
    alg n@(info, ArrayLiteralNode subs)
        | isLeft elemsErr = elemsErr
        | dataType info == invalidType = makeErr n "Inconsistent types for array elements"
        | otherwise = Right info
      where
        elemsErr = fmap (const info) (sequence subs)
    alg n@(info, FunctionCallNode name args)
        | isLeft argsErr = argsErr
        | otherwise = case lookupVar name env of
            Just (FunctionVar rt param)
                | length param /= length args -> makeErr n $ "Expected " ++ show (length param) ++ " arguments but got " ++ show (length args)
                | otherwise -> Right info
            Nothing -> makeErr n $ "Couldn't find function of name " ++ name
            _       -> makeErr n $ "Identifier " ++ name ++ " is not a function"
      where
        argsErr = fmap (const info) (sequence args)
    alg n@(info, ArrayIndexNode arr idx)
        | isLeft arr = arr
        | isLeft idx = idx
        | not $ isIntegralType $ subType idx = makeErr n $ "Can't index array with non-integral type " ++ showSub idx
        | dataType info == invalidType = makeErr n $ "Can't index a non-pointer type " ++ showSub arr
        | otherwise = Right info
    alg n@(_, ParenthesisNode sub) = sub
    alg n@(info, BinaryOpNode op lErr rErr)
        | isLeft lErr = lErr
        | isLeft rErr = rErr
        | dataType info == invalidType =
            makeErr n $ "Can not perform operation " ++ show op ++ " on types " ++ showSub lErr ++ " and " ++ showSub rErr
        | otherwise = Right info
    alg n@(info, UnaryOpNode op sub)
        | isLeft sub = sub
        | dataType info == invalidType = case op of
            Negate                            -> makeErr n $ "Can't negate non-integral or non-float type " ++ showSub sub
            Not                               -> makeErr n $ "Can't apply not to non-boolean type " ++ showSub sub
            Reference                         -> makeErr n "Can't take the reference of non-identifier"
            Dereference
                | isPointerType (subType sub) -> makeErr n $ "Can't dereference pointer of type " ++ showSub sub
                | otherwise                   -> makeErr n $ "Can't dereference non-pointer type " ++ showSub sub
            PrefixInc
                | subHandedness sub == RValue -> makeErr n "Can't do prefix ++ of r-value"
                | otherwise                   -> makeErr n $ "Can't do prefix ++ on type " ++ showSub sub
            PrefixDec
                | subHandedness sub == RValue -> makeErr n "Can't do prefix -- of r-value"
                | otherwise                   -> makeErr n $ "Can't do prefix -- on type " ++ showSub sub
        | otherwise = Right info
    alg n@(info, PostfixOpNode op sub)
        | isLeft sub = sub
        | dataType info == invalidType = sub >>= makeErr n . postErr
        | otherwise = Right info
      where
        postErr :: ExprInfo -> String
        postErr (ExprInfo subt subh _)
            | subh == RValue = "Can't do postfix " ++ show op ++ " on r-value"
            | otherwise      = "Can't do postfix " ++ show op ++ " on type " ++ showSub sub
    alg n@(info, AssignmentNode op lhs rhs)
        | isLeft lhs = lhs
        | isLeft rhs = rhs
        | dataType info == invalidType = (assignErr <$> lhs <*> rhs) >>= makeErr n
        | otherwise = Right info
      where
        assignErr :: ExprInfo -> ExprInfo -> String
        assignErr (ExprInfo ldt lhd _) (ExprInfo rdt _ _)
            | lhd == RValue = "Can't do assignment to r-value"
            | otherwise = case op of
                NoOp -> error "Unexpected error in assignment expression"
                _
                    | not (isPrimitiveType ldt || isPointerType ldt) ->
                        "Can't do assignment operation " ++ show op ++ " to a struct-type " ++ showDt ldt
                    | otherwise ->
                        "Can't do assignment operation " ++ show op ++ " over types " ++ showDt ldt ++ " and " ++ showDt rdt
    alg n@(info, MemberAccessNode isPtr lhs rhs)
        | isLeft lhs = lhs
        | not isPtr && isPointerType (subType lhs)   = makeErr n $ "Can't do '.' on pointer-type " ++ showSub lhs
        | isPtr && not (isPointerType (subType lhs)) = makeErr n $ "Can't do '->' on value-type " ++ showSub lhs
        | not $ M.member (fst (subType lhs)) structs = makeErr n $ "No struct found named " ++ fst (subType lhs)
        | otherwise = case rhs of
            Left errInfo -> case nodeType errInfo of
                StructMemberNode name -> makeErr n $ "No member " ++ name ++ " of struct " ++ fst (subType lhs)
                _                     -> rhs
            _            -> Right info
    alg n@(info, CastNode castType sub)
        | isLeft sub = sub
        | dataType info == invalidType = makeErr n $ "Can not cast from " ++ showSub sub ++ " to " ++ showDt castType
        | otherwise = Right info
    

-- Error layering:
-- data ErrorLayer { loc :: SourceLoc, msg :: String }
-- wrapping "lefts" =
-- wrapLeft :: ExprInfo -> Either ... -> Either
-- wrapLeft info wr = wrap the info around wr like, give sl and msg = "In expression"
-- you can then choose how deep you want the error layer to be w/ a list going left->right from shallow->deep
