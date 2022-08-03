{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module Validator ( validateProgram ) where

import CompilerShared
import CompilerShow (showDt)
import Control.Monad (unless, when, void)
import Control.Monad.Trans.State.Lazy (StateT(..), modify, put, get, evalStateT)
import Data.Bool (bool)
import Data.Either (Either(..), isLeft)
import Data.Fix (Fix(..), unFix, foldFix)
import Data.Functor ((<&>))
import Data.Functor.Compose (Compose(..), getCompose)
import Typecheck
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

data ValidatorState = ValidatorState
    { structMap :: StructMap
    , environment :: ValidationEnv
    } deriving Show
type ValidatorAction = StateT ValidatorState (Either FailureInfo)

data ExprError = ExprError
    { location :: SourceLoc
    , message :: String
    , nodeType :: ExprF ()
    }
type ErrOrType = Either ExprError ExprInfo

-- map lookup over all blocks -> find first Just result -> Join Maybe(Maybe) to Maybe
lookupVarFailure :: String -> ValidatorAction VarInfo
lookupVarFailure id = do
    maybeVar <- lookupVar id <$> (environment <$> get)
    maybe (raiseFailure ("Undefined id " ++ id) 0 0) return maybeVar

putEnvironment :: ValidationEnv -> ValidatorAction ()
putEnvironment newEnv = modify (\(ValidatorState structs env) -> ValidatorState structs newEnv)
putStructs :: StructMap -> ValidatorAction ()
putStructs newStructs = modify (\(ValidatorState structs env) -> ValidatorState newStructs env)
addStruct :: StructDefinition -> ValidatorAction ()
addStruct struct@(name, _) = get >>= putStructs . M.insert name struct . structMap

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
insertIntoEnv varName varInfo = get >>= putEnvironment . insert varName varInfo . environment
  where
    insert :: String -> VarInfo -> ValidationEnv -> ValidationEnv
    insert varName varInfo ((EnvBlock loop envMap):rest) = EnvBlock loop (M.insert varName varInfo envMap):rest
    insert _ _ [] = []

validateInLoop :: SourceLoc -> ValidatorAction ()
validateInLoop sl = do
    env <- environment <$> get
    unless (envInLoop env) (raiseFailureLoc "Not contained in a loop" sl)

validateProgram :: Program -> Either FailureInfo Program
validateProgram (globals, structs) =
    evalStateT
      (validateAllStructs structs >> validateAllGlobals globals >>= \x -> return (x, structs))
      (ValidatorState M.empty [EnvBlock False M.empty])
    where 
        validateAllStructs = mapM_ (\x -> addStruct x >> validateStruct x)
        validateAllGlobals = mapM validateGlobal
        validateGlobal (Function fn) =
            Function <$> (addFunctionToEnvironment fn >> validateFunction fn)
        validateGlobal (GlobalVar node) =
            GlobalVar <$> validateSyntaxNode node
        addFunctionToEnvironment (FunctionDefinition rtype name params _ _) =
            insertIntoEnv name (FunctionVar rtype params)
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
membersUnique names = length names == S.size (S.fromList names)

-- Syntax Tree actions (Stateful)
-- Needs to modify state to trace variable declarations and scope changes
canShadow :: String -> ValidatorAction Bool
canShadow varName = get <&> canShadowHelper varName . environment
  where
    canShadowHelper :: String -> ValidationEnv -> Bool
    canShadowHelper varName ((EnvBlock _ map):_) = not $ M.member varName map
    canShadowHelper varName [] = True

skipBlockAndValidate :: SyntaxNode -> ValidatorAction SyntaxNode
skipBlockAndValidate node = do
    let (loc, nodeF) = decompose node
    result <- case nodeF of
        (BlockNode sub) -> validateSyntaxNode sub
        _               -> raiseFailureLoc "Expected to find a block" loc
    return $ Fix $ Compose (loc, BlockNode result)

validateSyntaxNode :: SyntaxNode -> ValidatorAction SyntaxNode
validateSyntaxNode node = Fix . Compose <$> mapM validateSyntaxNodeF (decompose node)
  where
    nodeLoc = fst $ decompose node
    trueExpr = annotSyntaxEmpty (ExprNode $ annotExpr boolType RValue (SourceLoc 0 0) $ LiteralNode (BoolConstant True))

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
    getExprDecltype node = case snd $ decompose node of 
        ExprNode expr -> return $ typeOf expr
        _             -> raiseFailureLoc "Expected an expression" nodeLoc
    getExprRoot :: SyntaxNode -> ValidatorAction Expr
    getExprRoot node = case snd $ decompose node of 
        ExprNode expr -> return expr
        _             -> raiseFailureLoc "Expected an expression" nodeLoc

    injectCast :: DataType -> Expr -> SyntaxNodeF SyntaxNode
    injectCast toType node = ExprNode $ annotExpr toType (handednessOf node) (sourceLocOf node) $ CastNode toType node

    -- Primary recursive logic for validating SyntaxNodes
    -- Fans out to validating Exprs @ ExprNode
    validateSyntaxNodeF :: SyntaxNodeF SyntaxNode -> ValidatorAction (SyntaxNodeF SyntaxNode)
    validateSyntaxNodeF EmptyNode = return EmptyNode
    validateSyntaxNodeF (SeqNode lhs rhs) = do
        SeqNode <$> validateSyntaxNode lhs <*> validateSyntaxNode rhs
    validateSyntaxNodeF (WhileNode condition block) = do
        condition <- validateSyntaxNode condition
        condType <- getExprDecltype condition
        unless
          (isImplicitCastAllowed boolType condType)
          (raiseFailureLoc ("Cannot convert while condition expression from " ++ showDt condType ++ " to bool") nodeLoc)
        -- TODO: maybe add implicit casts to bool if we ever change our minds?
        pushEnvironment True
        block <- validateSyntaxNode block
        popEnvironment
        return $ WhileNode condition block
    validateSyntaxNodeF (ForNode init condition expr block or) = do 
        pushEnvironment True
        init <- validateSyntaxNode init
        -- Correct a for condition that is EmptyNode to an expression that is `true`
        condition <- validateSyntaxNode condition <&> \cond -> if isEmptyNode cond then trueExpr else cond
        condType <- getExprDecltype condition
        unless (isImplicitCastAllowed boolType condType) (failCantCastCondition condType)
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
        unless (isImplicitCastAllowed boolType condType) (failCantCastCondition condType)
        -- TODO: maybe add implicit casts to bool if we ever change our minds?
        pushEnvironment False
        block <- validateSyntaxNode block
        popEnvironment
        return $ IfNode condition block
    validateSyntaxNodeF (IfElseNode condition block elseBlock) = do
        condition <- validateSyntaxNode condition
        condType <- getExprDecltype condition
        unless (isImplicitCastAllowed boolType condType) (failCantCastCondition condType)
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
        unless (isImplicitCastAllowed funcRetType exprType) (failCantCastReturn exprType funcRetType)
        if exprType /= funcRetType
          then ReturnNode . copyAnnot expr . injectCast funcRetType <$> getExprRoot expr
          else return $ ReturnNode expr
    validateSyntaxNodeF ContinueNode = validateInLoop nodeLoc >> return ContinueNode
    validateSyntaxNodeF BreakNode = validateInLoop nodeLoc >> return BreakNode
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
        expression <- computeDecltype <$> (environment <$> get) <*> (structMap <$> get) <*> pure expression
        when (invalidType == typeOf expression) (failExprInvalid expression)
        return $ ExprNode expression

findExprError :: ValidationEnv -> StructMap -> Expr -> ExprError
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
    alg n@(info, DynamicAllocationNode tp count)
        | isLeft count                 = count
        | tp == voidType               = makeErr n "Can't dynamically allocate void-type"
        | dataType info == invalidType = makeErr n $ "Allocation count parameter expected integral type not " ++ showSub count
        | otherwise                    = Right info
    alg n@(info, DynamicFreeNode address)
        | isLeft address               = address
        | dataType info == invalidType = makeErr n $ "Deallocation expected pointer type not " ++ showSub address
        | otherwise                    = Right info

-- Error layering:
-- data ErrorLayer { loc :: SourceLoc, msg :: String }
-- wrapping "lefts" =
-- wrapLeft :: ExprInfo -> Either ... -> Either
-- wrapLeft info wr = wrap the info around wr like, give sl and msg = "In expression"
-- you can then choose how deep you want the error layer to be w/ a list going left->right from shallow->deep
