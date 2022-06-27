module Validator ( validateProgram ) where

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import Data.Maybe
import CompilerShared
import Control.Monad
import Control.Monad.Trans.State.Lazy
import Control.Monad.Loops
import ParserStateful
import Lexer
import Debug.Trace

data VarInfo
    = FunctionVar DataType [(DataType, String)]
    | PrimitiveVar DataType
    | StructVar DataType
    deriving Show
data Environment = EnvLink Bool (M.Map String VarInfo) Environment | EnvBase (M.Map String VarInfo) deriving Show

type StructMap = M.Map String StructDefinition

data GeneratorState = GeneratorState
    { structMap :: StructMap
    , environment :: Environment
    } deriving Show

type GeneratorAction = StateT GeneratorState (Either String)

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
    get >>= putEnvironment . EnvLink isLoop M.empty . environment

popEnvironment :: GeneratorAction ()
popEnvironment = (get >>= return . popEnvironmentHelper . environment) >>= putEnvironment
  where
    popEnvironmentHelper :: Environment -> Environment
    popEnvironmentHelper (EnvLink _ _ env) = env
    popEnvironmentHelper (EnvBase _) = error "Tried to pop environment with no more environments left" -- FIXME!!

createVariable :: DataType -> GeneratorAction VarInfo
createVariable dataType = get >>= createVarHelper dataType . structMap
  where
    createVarHelper :: DataType -> StructMap -> GeneratorAction VarInfo
    createVarHelper dataType@(typename, _) structs
        | isPrimitiveType dataType      = return $ PrimitiveVar dataType
        | isStructType dataType structs = return $ StructVar dataType
        | otherwise                     = raiseFailure $ "Invalid typename " ++ typename

insertIntoEnv :: String -> VarInfo -> GeneratorAction ()
insertIntoEnv varName varInfo =
    get >>= putEnvironment . insert varName varInfo . environment
  where
    insert :: String -> VarInfo -> Environment -> Environment
    insert varName varInfo (EnvLink loop envMap next) = EnvLink loop (M.insert varName varInfo envMap) next
    insert varName varInfo (EnvBase envMap) = EnvBase (M.insert varName varInfo envMap)

validateInLoop :: GeneratorAction ()
validateInLoop = get >>= (\st -> unless (isInLoop $ environment st) (raiseFailure "Not inside a loop"))
  where
    isInLoop :: Environment -> Bool
    isInLoop (EnvLink loop _ next) 
        | loop      = True
        | otherwise = isInLoop next
    isInLoop (EnvBase _) = False

validateProgram :: Program -> Either String Program
validateProgram (funcs, structs) =
    let result = evalStateT
         (validateAllStructs structs >> validateAllFunctions funcs >>= \x -> return (x, structs))
         (GeneratorState M.empty (EnvBase M.empty))
    in case result of
        Left err       -> Left err
        _              -> result
    where 
        validateAllStructs :: [StructDefinition] -> GeneratorAction ()
        validateAllStructs = mapM_ (\x -> validateStruct x >> addStruct x)
        validateAllFunctions :: [FunctionDefinition] -> GeneratorAction [FunctionDefinition]
        validateAllFunctions = mapM (\x -> validateFunction x >>= \newFunc -> addFunctionToEnvironment x >> return newFunc)
        addFunctionToEnvironment :: FunctionDefinition -> GeneratorAction ()
        addFunctionToEnvironment (FunctionDefinition rtype name params _) =
            insertIntoEnv name (FunctionVar rtype params)
        validateFunction :: FunctionDefinition -> GeneratorAction FunctionDefinition
        validateFunction (FunctionDefinition rtype fname params body) = do
            pushEnvironment False
            addFunctionParameters params
            insertIntoEnv "$currentFunction" (FunctionVar rtype [])
            body <- validateSyntaxNode body
            unless (isVoidType rtype) (validateReturns body)
            popEnvironment
            return $ FunctionDefinition rtype fname params body
          where
            validateReturns :: SyntaxNode -> GeneratorAction ()
            validateReturns (SeqNode _ (ReturnNode _)) = return ()
            validateReturns _ = raiseFailure $ "Function " ++ fname ++ " did not return a value"
            addFunctionParameters :: [(DataType, String)] -> GeneratorAction ()
            addFunctionParameters = mapM_ (\(dataType, id) -> createVariable dataType >>= insertIntoEnv id)

validateStruct :: StructDefinition -> GeneratorAction ()
validateStruct (StructDefinition (name, memberList)) = do
    curStructs <- structMap <$> get
    unless (all (validateMember curStructs) memberList && membersUnique (map snd memberList)) (raiseFailure $ "Validating struct " ++ name ++ " failed")
    when (null memberList) (raiseFailure $ "Struct " ++ name ++ " has no members")

validateMember :: StructMap -> (DataType, String) -> Bool
validateMember structs (datatype@(typename, _), id) = isPrimitiveType datatype || M.member typename structs

membersUnique :: [String] -> Bool
membersUnique names =
    let nameSet = S.fromList names
    in  length names == S.size nameSet
    

isPrimitiveType :: DataType -> Bool
isPrimitiveType (typename, quals) = S.member typename baseTypes

isStructType :: DataType -> StructMap -> Bool
isStructType (typename, ptrList) structs = M.member typename structs && null ptrList

isIntegralType :: DataType -> Bool
isIntegralType (typename, ptrList)
    | typename == "char"  = isntPtr
    | typename == "short" = isntPtr
    | typename == "int"   = isntPtr
    | typename == "long"  = isntPtr
    | otherwise           = False
  where
    isntPtr = null ptrList

isPointerType :: DataType -> Bool
isPointerType (_, ptrList) = not (null ptrList)

isFloatType :: DataType -> Bool
isFloatType (typename, ptrList)
    | typename == "float" = isntPtr
    | otherwise           = False
  where
    isntPtr = null ptrList

isBoolType :: DataType -> Bool
isBoolType (typename, ptrList)
    | typename == "bool" = isntPtr
    | otherwise          = False
  where
    isntPtr = null ptrList
    
isVoidType :: DataType -> Bool
isVoidType (typename, ptrList)
    | typename == "void" = isntPtr
    | otherwise          = False
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

validateAssignOp :: AssignmentOp -> SyntaxNode -> SyntaxNode -> GeneratorAction (SyntaxNode, SyntaxNode)
validateAssignOp op lhs rhs = case op of
    NoOp    -> do
        lhsType <- decltype lhs
        rhsType <- decltype rhs
        let lhsTypeName = showDt lhsType
        let rhsTypeName = showDt rhsType
        unless
            (isImplicitCastAllowed lhsType rhsType)
            (raiseFailure $ "Type mismatch for assignment between " ++ lhsTypeName ++ " and " ++ rhsTypeName)
        if rhsType /= lhsType
        then
            return (lhs, CastNode rhs lhsType)
        else
            return (lhs, rhs)
    PlusEq  -> validateBinaryOp Addition lhs rhs
    MinusEq -> validateBinaryOp Subtraction lhs rhs
    MulEq   -> validateBinaryOp Multiplication lhs rhs
    DivEq   -> validateBinaryOp Division lhs rhs
    ModEq   -> validateBinaryOp Mod lhs rhs

validateBinaryOp :: BinaryOp -> SyntaxNode -> SyntaxNode -> GeneratorAction (SyntaxNode, SyntaxNode)
validateBinaryOp op lhs rhs = do
        lhsType <- decltype lhs
        rhsType <- decltype rhs
        let lhsTypeName = showDt lhsType
        let rhsTypeName = showDt rhsType
        unless
          (isPrimitiveType lhsType && isPrimitiveType rhsType)
          (raiseFailure $ "Binary operations not allowed for struct types (either " ++ lhsTypeName ++ " or " ++ rhsTypeName ++ ")")
        unless
          (typeCheckBinaryOpHelper op lhsType rhsType)
          (raiseFailure $ "Type mismatch for " ++ show op ++ " between " ++ lhsTypeName ++ " and " ++ rhsTypeName)
        ourType <- decltype (BinaryOpNode op lhs rhs)
        case () of _
                    | ourType /= lhsType -> return (CastNode lhs ourType, rhs)
                    | ourType /= rhsType -> return (lhs, CastNode rhs ourType)
                    | otherwise          -> return (lhs, rhs)
  where 
    typeCheckBinaryOpHelper :: BinaryOp -> DataType -> DataType -> Bool
    typeCheckBinaryOpHelper op lhsType rhsType
        | op == Addition           = isImplicitCastAllowed lhsType rhsType || isPointerArithmetic op lhsType rhsType
        | op == Multiplication     = isImplicitCastAllowed lhsType rhsType
        | op == Subtraction        = isImplicitCastAllowed lhsType rhsType || isPointerArithmetic op lhsType rhsType
        | op == Division           = isImplicitCastAllowed lhsType rhsType
        | op == Mod                = isIntegralType lhsType && isIntegralType rhsType
        | op == Equal              = isImplicitCastAllowed lhsType rhsType
        | op == NotEqual           = isImplicitCastAllowed lhsType rhsType
        | op == LessThan           = isImplicitCastAllowed lhsType rhsType
        | op == GreaterThan        = isImplicitCastAllowed lhsType rhsType
        | op == GreaterThanOrEqual = isImplicitCastAllowed lhsType rhsType
        | op == LessThanOrEqual    = isImplicitCastAllowed lhsType rhsType
        | op == Or                 = isBoolType lhsType && isBoolType rhsType
        | op == And                = isBoolType lhsType && isBoolType rhsType
      where
        isPointerArithmetic :: BinaryOp -> DataType -> DataType -> Bool
        isPointerArithmetic op lhsType rhsType = 
            isPointerArithmeticSingle op lhsType rhsType || isPointerArithmeticSingle op rhsType lhsType
          where
            isPointerArithmeticSingle :: BinaryOp -> DataType -> DataType -> Bool
            isPointerArithmeticSingle op lhsType rhsType
                | op == Addition = isIntegralType lhsType && isPointerType rhsType
                | op == Subtraction = (isIntegralType lhsType && isPointerType rhsType) || (isPointerType lhsType && lhsType == rhsType)
        
validateUnaryOp :: UnaryOp -> SyntaxNode -> GeneratorAction ()
validateUnaryOp op sub = unlessM (validateUnaryOpHelper op sub) (raiseFailure $ "Invalid type " ++ "Sam fix me" ++ " for " ++ show op)
  where
    validateUnaryOpHelper :: UnaryOp -> SyntaxNode -> GeneratorAction Bool
    validateUnaryOpHelper op sub = do
        subType <- decltype sub
        case () of _
                    | op == Negate       -> return $ isIntegralType subType || isFloatType subType
                    | op == Not          -> return $ isBoolType subType
                    | op == Dereference  -> return $ isPointerType subType
                    | op == Reference    -> return $ case sub of
                                           (IdentifierNode _) -> True
                                           _                  -> False

validateArrayIndexing :: SyntaxNode -> SyntaxNode -> GeneratorAction ()
validateArrayIndexing arr idx = do
    arrType <- decltype arr
    idxType <- decltype idx
    let arrTypeName = showDt arrType
    let idxTypeName = showDt idxType
    case () of _
                | not $ isPointerType arrType  -> raiseFailure $ "Array indexing cannot be done on type " ++ arrTypeName
                | not $ isIntegralType idxType -> raiseFailure $ "Array index cannot be type " ++ idxTypeName
                | otherwise                    -> return ()

validateMemberAccess :: SyntaxNode -> [(DataType, String)] -> GeneratorAction SyntaxNode
validateMemberAccess (MemberAccessNode isPtr lhs rhs) _ = do
    lhsType@(lhsName, _) <- decltype lhs
    nlhs <- validateSyntaxNode lhs
    unlessM (get >>= return . isStructType lhsType . structMap) (raiseFailure "Tried to access member of non-struct type")
    unless (isPtr == isPointerType lhsType) (raiseFailure "Tried to access member of non-pointer type")
    structs <- structMap <$> get
    let structMembers = M.lookup lhsName structs
    nrhs <- maybe
      (raiseFailure $ "Struct type " ++ lhsName ++ " not declared")
      (\(StructDefinition v) -> validateMemberAccess rhs $ snd v)
      structMembers
    return $ MemberAccessNode isPtr nlhs nrhs
validateMemberAccess (IdentifierNode id) memberList = do
    unless
      (any (\x -> snd x == id) memberList)
      (raiseFailure $ "Could not find member variable " ++ id)
    return $ IdentifierNode id
validateMemberAccess (ArrayIndexNode arr idx) memberList = do
    nidx <- validateSyntaxNode idx
    narr <- validateMemberAccess arr memberList
    return $ ArrayIndexNode narr nidx

validateSyntaxNode :: SyntaxNode -> GeneratorAction SyntaxNode
validateSyntaxNode statement = case statement of
    FunctionCallNode name args -> do
        args <- mapM validateSyntaxNode args
        validateCall statement
    LiteralNode ct -> return statement
    IdentifierNode name -> do
        maybeVarInfo <- lookupVar name
        case maybeVarInfo of
            Left _ -> raiseFailure $ "Var " ++ name ++ " does not exist"
            Right varInfo -> return statement
    ParenthesisNode sub -> validateSyntaxNode sub
    BinaryOpNode op lhs rhs -> do
        nlhs <- validateSyntaxNode lhs
        nrhs <- validateSyntaxNode rhs
        (nlhs2, nrhs2) <- validateBinaryOp op nlhs nrhs
        return $ BinaryOpNode op nlhs2 nrhs2
    UnaryOpNode op sub -> do
        nsub <- validateSyntaxNode sub
        validateUnaryOp op nsub
        return $ UnaryOpNode op nsub
    ArrayIndexNode arr idx -> do
        narr <- validateSyntaxNode arr
        nidx <- validateSyntaxNode idx
        validateArrayIndexing narr nidx
        return $ ArrayIndexNode narr nidx
    AssignmentNode lhs op rhs -> do
        lhs <- validateSyntaxNode lhs
        rhs <- validateSyntaxNode rhs
        (lhs, rhs) <- validateAssignOp op lhs rhs
        return $ AssignmentNode lhs op rhs
    memberNode@(MemberAccessNode isPtr lhs rhs) -> validateMemberAccess memberNode []

    SeqNode left right -> do
        left <- validateSyntaxNode left
        right <- validateSyntaxNode right
        return $ SeqNode left right
    ContinueNode -> do
        validateInLoop
        return statement
    BreakNode -> do
        validateInLoop
        return statement
    WhileNode condition block -> do
        condition <- validateSyntaxNode condition
        condType <- decltype condition
        let condTypeName = showDt condType
        unless
          (isImplicitCastAllowed ("bool", []) condType)
          (raiseFailure $ "Cannot convert while condition expression from " ++ condTypeName ++ " to bool")
        -- TODO: maybe add implicit casts to bool if we ever change our minds?
        pushEnvironment True
        block <- validateSyntaxNode block
        popEnvironment
        return $ WhileNode condition block
    ForNode init condition expr block -> do 
        pushEnvironment True
        ninit <- validateSyntaxNode init
        condition <- validateSyntaxNode condition
        condType <- decltype condition
        let condTypeName = showDt condType
        unless
          (isEmptyNode condition || isImplicitCastAllowed ("bool", []) condType)
          (raiseFailure $ "Cannot convert for condition expression from " ++ condTypeName ++ " to bool")
        -- TODO: maybe add implicit casts to bool if we ever change our minds?
        expr <- validateSyntaxNode expr
        block <- validateSyntaxNode block
        popEnvironment
        return $ ForNode init condition expr block
    IfNode condition block -> do
        condition <- validateSyntaxNode condition
        condType <- decltype condition
        let condTypeName = showDt condType
        unless
          (isImplicitCastAllowed ("bool", []) condType)
          (raiseFailure $ "Cannot convert if condition expression from " ++ condTypeName ++ " to bool")
        -- TODO: maybe add implicit casts to bool if we ever change our minds?
        pushEnvironment False
        block <- validateSyntaxNode block
        popEnvironment
        return $ IfNode condition block
    IfElseNode condition block elseBlock -> do
        condition <- validateSyntaxNode condition
        condType <- decltype condition
        let condTypeName = showDt condType
        unless
          (isImplicitCastAllowed ("bool", []) condType)
          (raiseFailure $ "Cannot convert if condition expression from " ++ condTypeName ++ " to bool")
        -- TODO: maybe add implicit casts to bool if we ever change our minds?
        pushEnvironment False
        block <- validateSyntaxNode block
        popEnvironment
        pushEnvironment False
        elseBlock <- validateSyntaxNode elseBlock
        return $ IfElseNode condition block elseBlock
    ReturnNode expr -> do
        exprType <- decltype expr
        funcNode <- lookupVar "$currentFunction"
        let Right (FunctionVar funcRetType _) = funcNode
        let exprTypeName = showDt exprType
        let funcRetTypeName = showDt funcRetType
        expr <- validateSyntaxNode expr
        unless
          (isImplicitCastAllowed funcRetType exprType)
          (raiseFailure $ "Return type " ++ exprTypeName ++ " does not match function type " ++ funcRetTypeName)
        if exprType /= funcRetType
          then return $ ReturnNode (CastNode expr funcRetType)
          else return $ ReturnNode expr
    DeclarationNode dataType id -> do
        unlessM (canShadow id) (raiseFailure $ "Cannot redeclare variable with name " ++ id)
        when (fst dataType == "void") (raiseFailure $ "Cannot declare the variable " ++ id ++ " with type void")
        createVariable dataType >>= insertIntoEnv id
        return statement
    DefinitionNode dataType id expr -> do
        unlessM (canShadow id) (raiseFailure $ "Cannot redeclare variable with name " ++ id)
        when (fst dataType == "void") (raiseFailure $ "Cannot declare the variable " ++ id ++ " with type void")
        createVariable dataType >>= insertIntoEnv id
        exprType <- decltype expr
        expr <- validateSyntaxNode expr
        let exprTypeName = showDt exprType
        let varTypeName = showDt dataType
        unless
          (isImplicitCastAllowed dataType exprType)
          (raiseFailure $ "Cannot cast definition expression from " ++ exprTypeName ++ " to " ++ varTypeName)
        if exprType /= dataType
          then return $ DefinitionNode dataType id (CastNode expr dataType)
          else return $ DefinitionNode dataType id expr
    EmptyNode -> return statement
    CastNode node dataType -> do
        node <- validateSyntaxNode node
        return $ CastNode node dataType

canShadow :: String -> GeneratorAction Bool
canShadow varName = get >>= return . canShadowHelper varName . environment
  where
    canShadowHelper :: String -> Environment -> Bool
    canShadowHelper varName (EnvLink _ map nextEnv) = not $ M.member varName map
    canShadowHelper varName (EnvBase map) = not $ M.member varName map

lookupVar :: String -> GeneratorAction (Either String VarInfo)
lookupVar varName = get >>= return . lookupVarHelper varName . environment
  where
    lookupVarHelper :: String -> Environment -> Either String VarInfo
    lookupVarHelper varName (EnvLink _ map nextEnv) =
        case M.lookup varName map of
            (Just member) -> Right member
            _             -> lookupVarHelper varName nextEnv
    lookupVarHelper varName (EnvBase map) = case M.lookup varName map of
        Just varInfo -> return varInfo
        Nothing      -> Left varName

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

-- See below for binary operation casting rules
binaryTypeResult :: BinaryOp -> DataType -> DataType -> GeneratorAction DataType
binaryTypeResult op lhsType rhsType
    | op == Addition           = decideAddition lhsType rhsType
    | op == Multiplication     = decideMultiplication lhsType rhsType
    | op == Subtraction        = decideSubtraction lhsType rhsType
    | op == Division           = decideDivision lhsType rhsType
    | op == Mod                = return $ largestType lhsType rhsType
    | op == Equal              = return ("bool", [])
    | op == NotEqual           = return ("bool", [])
    | op == LessThan           = return ("bool", [])
    | op == GreaterThan        = return ("bool", [])
    | op == GreaterThanOrEqual = return ("bool", [])
    | op == LessThanOrEqual    = return ("bool", [])
    | op == Or                 = return ("bool", [])
    | op == And                = return ("bool", [])
  where
    decideAddition :: DataType -> DataType -> GeneratorAction DataType
    decideAddition lhs rhs
    -- ptr + integral (ptr)
        | isPointerType lhsType && isIntegralType rhsType = return lhsType
        | isPointerType rhsType && isIntegralType lhsType = return rhsType
    -- integral + integral (largest of 2)
        | isIntegralType lhsType && isIntegralType rhsType = return $ largestType lhsType rhsType
    -- integral + float (float)
        | isIntegralType lhsType && isFloatType rhsType = return ("float", [])
    -- float + float (float)
        | isFloatType lhsType && isFloatType rhsType = return ("float", [])
    -- anything else = invalid
        | otherwise = raiseFailure "Invalid addition types"
    decideMultiplication :: DataType -> DataType -> GeneratorAction DataType
    decideMultiplication lhs rhs
    -- either are pointers -> not allowed
        | isPointerType lhsType || isPointerType rhsType = raiseFailure "You cannot multiply pointers"
        | otherwise = decideAddition lhs rhs
    decideSubtraction :: DataType -> DataType -> GeneratorAction DataType
    decideSubtraction lhs rhs
    -- ptr - ptr (long)
        | isPointerType lhsType && isPointerType rhsType = return ("long", [])
        | isPointerType rhsType && isPointerType lhsType = return ("long", [])
        | otherwise = decideAddition lhs rhs
    decideDivision :: DataType -> DataType -> GeneratorAction DataType
    decideDivision = decideMultiplication

unaryTypeResult :: UnaryOp -> DataType -> GeneratorAction DataType
unaryTypeResult op subType
    | op == Negate      = decideNegate subType
    | op == Not         = decideNot subType
    | op == Reference   = decideReference subType
    | op == Dereference = decideDereference subType
  where
    decideNegate :: DataType -> GeneratorAction DataType
    decideNegate tp
        | isFloatType tp || isIntegralType tp = return tp
        | otherwise = raiseFailure "Negate operand type is invalid, must be float or integral type"
    decideNot :: DataType -> GeneratorAction DataType
    decideNot tp
        | isBoolType tp = return tp
        | otherwise     = raiseFailure "Not operand type is invalid, must be a bool"
    decideReference :: DataType -> GeneratorAction DataType
    decideReference (typeName, ptrList) = return (typeName, 0:ptrList)
    decideDereference :: DataType -> GeneratorAction DataType
    decideDereference (typeName, ptrList)
        | not (null ptrList) = return (typeName, tail ptrList)
        | otherwise          = raiseFailure "Dereference operand type is invalid, must be a pointer"

decltype :: SyntaxNode -> GeneratorAction DataType
decltype EmptyNode = return ("void", [])
-- decltype of identifier is the type of the identifier
decltype (IdentifierNode varName) = do
    maybeVarInfo <- lookupVar varName
    case maybeVarInfo of
        Left _ -> raiseFailure $ "Var " ++ varName ++ " does not exist"
        Right varInfo -> case varInfo of
                            (FunctionVar _ _) -> raiseFailure $ varName ++ " is a function not a variable"
                            (PrimitiveVar tp) -> return tp
                            (StructVar tp)    -> return tp
-- decltype of a literal is the type of the literal
decltype (LiteralNode constantType) = case constantType of
    IntConstant _    -> return ("long", [])
    FloatConstant _  -> return ("float", [])
    BoolConstant _   -> return ("bool", [])
    StringConstant str -> return ("char", [length str])
-- decltype of a function call is the return type of the call
decltype (FunctionCallNode funcName _) = do
    maybeFuncInfo <- lookupVar funcName
    case maybeFuncInfo of
        Left _ -> raiseFailure $ funcName ++ " is not valid function identifier"
        Right funcInfo -> case funcInfo of
                            (FunctionVar returnTp _) -> return returnTp
                            (PrimitiveVar _) -> raiseFailure $ funcName ++ " is a variable not a function"
-- decltype of a parenthesis is the type of its sub expression
decltype (ParenthesisNode sub) = decltype sub
decltype (BinaryOpNode op lhs rhs) = do
  lhsType <- decltype lhs
  rhsType <- decltype rhs
  binaryTypeResult op lhsType rhsType
decltype (UnaryOpNode op sub) = do
    subType <- decltype sub
    unaryTypeResult op subType
-- Same as stripping a pointer off
decltype (ArrayIndexNode arr idx) = do
    subType <- decltype arr
    unaryTypeResult Dereference subType
decltype (AssignmentNode lhs op rhs) = decltype lhs
-- Type of the member, stripping the array indexing off
decltype (MemberAccessNode isPtr lhs rhs) = do
    lhsType@(lhsName, _) <- decltype lhs
    (rhsId, derefDepth) <- getMemberType rhs 0
    let lhsTypeName = showDt lhsType
    structs <- structMap <$> get
    unless (isStructType lhsType structs) (raiseFailure $ "Tried to access member of non-struct type " ++ lhsTypeName)
    (rhsTypename, rhsDepth) <- case M.lookup lhsName structs of
        Nothing -> raiseFailure $ "Struct type " ++ lhsTypeName ++ " not declared"
        Just (StructDefinition (_, memberList)) -> do
            case L.find ((== rhsId) . snd) memberList of
                Nothing -> raiseFailure $ "Struct type " ++ lhsTypeName ++ " does not have member " ++ rhsId
                Just (dataType, _) -> return dataType
    when (length rhsDepth < derefDepth) (raiseFailure "Too many dereferences")
    return (rhsTypename, (reverse . drop derefDepth . reverse) rhsDepth)
  where
    getMemberType :: SyntaxNode -> Int -> GeneratorAction (String, Int)
    getMemberType (ArrayIndexNode lhs idx) depth = getMemberType lhs (depth + 1)
    getMemberType (IdentifierNode name) depth    = return (name, depth)
    getMemberType _ _                            = raiseFailure "Couldn't find identifier right of '.' or '->'"
decltype (CastNode _ toType) = return toType

validateCall :: SyntaxNode -> GeneratorAction SyntaxNode
validateCall (FunctionCallNode name args) = do
    funcInfo <- lookupVar name
    case funcInfo of
        Right (FunctionVar rType params) -> do
            when
              (length args /= length params)
              (raiseFailure $ "Wrong number of parameters passed to the function " ++ name)
            paramResults <- mapM typeCheck (zip (map fst params) args)
            unless
              (all fst paramResults)
              (raiseFailure $ "Parameter type mismatch for function call to " ++ name)
            return $ FunctionCallNode name (zipWith castParam args (map snd paramResults))
        Left _                           -> raiseFailure $ "Function call to " ++ name ++ " not found"
  where
    typeCheck :: (DataType, SyntaxNode) -> GeneratorAction (Bool, (DataType, DataType))
    typeCheck (expectedType, paramExpr) = do
        paramType <- decltype paramExpr
        return (isImplicitCastAllowed expectedType paramType, (paramType, expectedType))
    castParam :: SyntaxNode -> (DataType, DataType) -> SyntaxNode
    castParam node (paramt, expectedt)
        | paramt == expectedt = node
        | otherwise           = CastNode node expectedt
validateCall _ = raiseFailure "Not a function call node"