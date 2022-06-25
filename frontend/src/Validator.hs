module Validator
( validateProgram

) where

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import Data.Maybe
import ParserStateful
import Lexer
import Debug.Trace

data VarInfo = FunctionVar DataType [(DataType, String)] | PrimitiveVar DataType
data Environment = EnvLink Bool (M.Map String VarInfo) Environment | EnvBase (M.Map String VarInfo)

insertIntoEnv :: Environment -> String -> VarInfo -> Environment
insertIntoEnv (EnvLink loop envMap next) varName varInfo = EnvLink loop (M.insert varName varInfo envMap) next
insertIntoEnv (EnvBase envMap) varName varInfo = EnvBase (M.insert varName varInfo envMap)

isInLoop :: Environment -> Bool
isInLoop (EnvLink loop _ next) 
  | loop      = True
  | otherwise = isInLoop next
isInLoop (EnvBase _) = False

validateProgram :: Program -> Bool
validateProgram program = let baseEnv = EnvBase (foldl addFunctionToEnvironment M.empty program) in
    all (checkFunction baseEnv) program
    where 
        addFunctionToEnvironment :: M.Map String VarInfo -> SyntaxNode -> M.Map String VarInfo
        addFunctionToEnvironment env func = let FunctionDefinitionNode returnType name argList _ = func in
            M.insert name (FunctionVar returnType argList) env
        checkFunction :: Environment -> SyntaxNode -> Bool
        checkFunction env node = let FunctionDefinitionNode typeName name argList body = node in
            snd (validateSyntaxNode body (addFunctionParameters (insertIntoEnv env "$currentFunction" (FunctionVar typeName [])) argList))
          where
            addFunctionParameters :: Environment -> [(DataType, String)] -> Environment
            addFunctionParameters = foldl (\a (typeName, name) -> insertIntoEnv a name (PrimitiveVar typeName))

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
isImplicitCastAllowed type1 type2 =
    implicitCastAllowedSingle type1 type2 || implicitCastAllowedSingle type2 type1
  where
    implicitCastAllowedSingle :: DataType -> DataType -> Bool
    implicitCastAllowedSingle type1 type2
        | isIntegralType type1 && isFloatType type2    = True
        | type1 == type2                               = True
        | isIntegralType type1 && isIntegralType type2 = True
        | pointerMatches type1 type2                   = True
        | otherwise                                    = False
      where
        pointerMatches (lhsType, lhsPtrList) (rhsType, rhsPtrList) = lhsType == rhsType && length lhsPtrList == length rhsPtrList

typeCheckAssignOp :: AssignmentOp -> SyntaxNode -> SyntaxNode -> Environment -> Bool
typeCheckAssignOp op lhs rhs env = case op of
    NoOp    -> isImplicitCastAllowed lhsType rhsType
    PlusEq  -> typeCheckBinaryOp Addition lhs rhs env
    MinusEq -> typeCheckBinaryOp Subtraction lhs rhs env
    MulEq   -> typeCheckBinaryOp Multiplication lhs rhs env
    DivEq   -> typeCheckBinaryOp Division lhs rhs env
    ModEq   -> typeCheckBinaryOp Mod lhs rhs env
  where
    lhsType = decltype lhs env
    rhsType = decltype rhs env

typeCheckBinaryOp :: BinaryOp -> SyntaxNode -> SyntaxNode -> Environment -> Bool
typeCheckBinaryOp op lhs rhs env
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
    lhsType = decltype lhs env
    rhsType = decltype rhs env
    isPointerArithmetic :: BinaryOp -> DataType -> DataType -> Bool
    isPointerArithmetic op lhsType rhsType = 
        isPointerArithmeticSingle op lhsType rhsType || isPointerArithmeticSingle op rhsType lhsType
      where
        isPointerArithmeticSingle :: BinaryOp -> DataType -> DataType -> Bool
        isPointerArithmeticSingle op lhsType rhsType
          | op == Addition = isIntegralType lhsType && isPointerType rhsType
          | op == Subtraction = (isIntegralType lhsType && isPointerType rhsType) || (isPointerType lhsType && lhsType == rhsType)
        

typeCheckUnaryOp :: UnaryOp -> SyntaxNode -> Environment -> Bool
typeCheckUnaryOp op sub env
    | op == Negate       = isIntegralType subType || isFloatType subType
    | op == Not          = isBoolType subType
    | op == Dereference  = isPointerType subType
    | op == Reference    = case sub of (IdentifierNode _) -> True
                                       _                  -> False
  where
    subType = decltype sub env

typeCheckArrayIndex :: SyntaxNode -> SyntaxNode -> Environment -> Bool
typeCheckArrayIndex arr idx env = isPointerType arrType && isIntegralType idxType
  where
    arrType = decltype arr env
    idxType = decltype idx env

isEmptyNode :: SyntaxNode -> Bool
isEmptyNode EmptyNode = True
isEmptyNode _         = False

validateSyntaxNode :: SyntaxNode -> Environment -> (Environment, Bool)
validateSyntaxNode statement env = case statement of
    FunctionCallNode name args -> (env, all (\x -> snd (validateSyntaxNode x env)) args
                                        && validateCall statement env)
    LiteralNode ct -> (env, True)
    IdentifierNode name -> (env, isJust $ lookupVar name env)
    ParenthesisNode sub -> validateSyntaxNode sub env
    BinaryOpNode op lhs rhs -> (env, snd (validateSyntaxNode lhs env)
                                     && snd (validateSyntaxNode rhs env)
                                     && typeCheckBinaryOp op lhs rhs env)
    UnaryOpNode op sub -> (env, snd (validateSyntaxNode sub env)
                                && typeCheckUnaryOp op sub env)
    ArrayIndexNode arr idx -> (env, snd (validateSyntaxNode arr env)
                                    && snd (validateSyntaxNode idx env)
                                    && typeCheckArrayIndex arr idx env)
    AssignmentNode lhs op rhs -> (env, snd (validateSyntaxNode rhs env)
                                       && snd (validateSyntaxNode lhs env)
                                       && typeCheckAssignOp op lhs rhs env)
    
    SeqNode left right -> let (modifiedEnv, valid) = validateSyntaxNode left env in
        if valid
        then
            validateSyntaxNode right modifiedEnv
        else
            (env, False)
    ContinueNode -> (env, isInLoop env)
    BreakNode -> (env, isInLoop env)
    WhileNode condition block -> (env, snd (validateSyntaxNode condition env)
                                       && isImplicitCastAllowed (decltype condition env) ("bool", [])
                                       && snd (validateSyntaxNode block $ EnvLink True M.empty env))
    ForNode init condition expr block -> (env, let (newEnv, initResult) = validateSyntaxNode init (EnvLink True M.empty env)
                                          in initResult
                                          && snd (validateSyntaxNode condition newEnv)
                                          && (isEmptyNode condition || isImplicitCastAllowed (decltype condition newEnv) ("bool", []))
                                          && snd (validateSyntaxNode expr newEnv)
                                          && snd (validateSyntaxNode block newEnv))
    IfNode condition block -> (env, snd (validateSyntaxNode condition env)
                                    && isImplicitCastAllowed (decltype condition env) ("bool", [])
                                    && snd (validateSyntaxNode block $ EnvLink False M.empty env))
    IfElseNode condition block elseBlock -> (env, snd (validateSyntaxNode condition env)
                                                  && isImplicitCastAllowed (decltype condition env) ("bool", [])
                                                  && snd (validateSyntaxNode block $ EnvLink False M.empty env)
                                                  && snd (validateSyntaxNode elseBlock $ EnvLink False M.empty env))
    ReturnNode expr -> let Just (FunctionVar currentFunctionRetType _) = lookupVar "$currentFunction" env in
        (env, snd (validateSyntaxNode expr env)
              && isImplicitCastAllowed (decltype expr env) currentFunctionRetType)
    DeclarationNode typeName id ->
        if canShadow id env && fst typeName /= "void"
          then (insertIntoEnv env id (PrimitiveVar typeName), True)
          else (env, False)
    DefinitionNode typeName id expr ->
        if canShadow id env && fst typeName /= "void"
          then (insertIntoEnv env id (PrimitiveVar typeName),
                  snd (validateSyntaxNode expr (insertIntoEnv env id (PrimitiveVar typeName)))
                  && isImplicitCastAllowed (decltype expr env) typeName)
          else (env, False)
    EmptyNode -> (env, True)

canShadow :: String -> Environment -> Bool
canShadow varName (EnvLink _ map nextEnv) = not $ M.member varName map
canShadow varName (EnvBase map) = not $ M.member varName map

lookupVar :: String -> Environment -> Maybe VarInfo
lookupVar varName (EnvLink _ map nextEnv) =
    if M.member varName map
      then M.lookup varName map
      else lookupVar varName nextEnv
lookupVar varName (EnvBase map) = M.lookup varName map

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

binaryTypeResult :: BinaryOp -> DataType -> DataType -> DataType
binaryTypeResult op lhsType rhsType
    | op == Addition           = decideAddition lhsType rhsType
    | op == Multiplication     = decideMultiplication lhsType rhsType
    | op == Subtraction        = decideSubtraction lhsType rhsType
    | op == Division           = decideDivision lhsType rhsType
    | op == Mod                = largestType lhsType rhsType
    | op == Equal              = ("bool", [])
    | op == NotEqual           = ("bool", [])
    | op == LessThan           = ("bool", [])
    | op == GreaterThan        = ("bool", [])
    | op == GreaterThanOrEqual = ("bool", [])
    | op == LessThanOrEqual    = ("bool", [])
    | op == Or                 = ("bool", [])
    | op == And                = ("bool", [])
  where
    decideAddition lhs rhs
    -- ptr + integral (ptr)
        | isPointerType lhsType && isIntegralType rhsType = lhsType
        | isPointerType rhsType && isIntegralType lhsType = rhsType
    -- integral + integral (largest of 2)
        | isIntegralType lhsType && isIntegralType rhsType = largestType lhsType rhsType
    -- integral + float (float)
        | isIntegralType lhsType && isFloatType rhsType = ("float", [])
    -- float + float (float)
        | isFloatType lhsType && isFloatType rhsType = ("float", [])
    -- anything else = invalid
        | otherwise = ("invalid", [])
    decideMultiplication lhs rhs
    -- either are pointers -> not allowed
        | isPointerType lhsType || isPointerType rhsType = ("invalid", [])
        | otherwise = decideAddition lhs rhs
    decideSubtraction lhs rhs
    -- ptr - ptr (long)
        | isPointerType lhsType && isPointerType rhsType = ("long", [])
        | isPointerType rhsType && isPointerType lhsType = ("long", [])
        | otherwise = decideAddition lhs rhs
    decideDivision = decideMultiplication

unaryTypeResult :: UnaryOp -> DataType -> DataType
unaryTypeResult op subType
    | op == Negate = decideNegate subType
    | op == Not    = decideNot subType
    | op == Reference   = decideReference subType
    | op == Dereference = decideDereference subType
  where
    decideNegate tp
      | isFloatType tp || isIntegralType tp = tp
      | otherwise = ("invalid", [])
    decideNot tp
      | isBoolType tp = tp
      | otherwise     = ("invalid", [])
    decideReference (typeName, ptrList) = (typeName, 0:ptrList)
    decideDereference (typeName, ptrList)
      | not (null ptrList) = (typeName, tail ptrList)
      | otherwise          = ("invalid", [])

decltype :: SyntaxNode -> Environment -> DataType
decltype EmptyNode env = ("void", [])
decltype (IdentifierNode varName) env =
    case maybeVarInfo of
        Nothing -> ("invalid", [])
        Just varInfo -> case varInfo of
                            (FunctionVar _ _) -> ("invalid", [])
                            (PrimitiveVar tp) -> tp
  where 
    maybeVarInfo = lookupVar varName env
decltype (LiteralNode constantType) _ = case constantType of
    IntConstant _    -> ("int", [])
    FloatConstant _  -> ("float", [])
    BoolConstant _   -> ("bool", [])
    StringConstant str -> ("char", [length str])
decltype (FunctionCallNode funcName _) env =
    case maybeFuncInfo of
        Nothing -> ("invalid", [])
        Just funcInfo -> case funcInfo of
                            (FunctionVar returnTp _) -> returnTp
                            (PrimitiveVar _) -> ("invalid", [])
  where 
    maybeFuncInfo = lookupVar funcName env
decltype (ParenthesisNode sub) env = decltype sub env
decltype (BinaryOpNode op lhs rhs) env = binaryTypeResult op lhsType rhsType
  where
    lhsType = decltype lhs env
    rhsType = decltype rhs env
decltype (UnaryOpNode op sub) env = unaryTypeResult op subType
  where
    subType = decltype sub env
decltype (ArrayIndexNode arr idx) env = unaryTypeResult Dereference subType
  where
    subType = decltype arr env
decltype (AssignmentNode lhs op rhs) env = decltype lhs env

validateCall :: SyntaxNode -> Environment -> Bool
validateCall (FunctionCallNode name args) env =
    case funcInfo of
        Just (FunctionVar rType params) -> length args == length params && all (typeCheck env) (zip (map fst params) args)
        _                               -> False
  where
    funcInfo = lookupVar name env
    typeCheck :: Environment -> (DataType, SyntaxNode) -> Bool
    typeCheck env (expectedType, paramExpr) = isImplicitCastAllowed (decltype paramExpr env) expectedType
validateCall _ _ = False
