module Generator
(

) where

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import Data.Maybe
import Parser
import Lexer

data VarInfo = FunctionVar String [(String, String)] | PrimitiveVar String
data Environment = EnvLink (M.Map String VarInfo) Environment | EnvBase (M.Map String VarInfo)

-- Check variable existence upon reference
--  - Add declared variables & functions to environment as they are added
-- Check functions take the correct number of parameters and type

--reduceTypes :: (String, String) -> String
--reduceTypes (left, right) = 

insertIntoEnv :: Environment -> String -> VarInfo -> Environment
insertIntoEnv (EnvLink envMap next) varName varInfo = EnvLink (M.insert varName varInfo envMap) next
insertIntoEnv (EnvBase envMap) varName varInfo = EnvBase (M.insert varName varInfo envMap)

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
            addFunctionParameters :: Environment -> [(String, String)] -> Environment
            addFunctionParameters = foldl (\a (typeName, name) -> insertIntoEnv a name (PrimitiveVar typeName))

isIntegralType :: String -> Bool
isIntegralType typename
    | typename == "char"  = True
    | typename == "short" = True
    | typename == "int"   = True
    | typename == "long"  = True
    | otherwise           = False


isImplicitCastAllowed :: String -> String -> Bool
isImplicitCastAllowed type1 type2 =
    implicitCastAllowedSingle type1 type2 || implicitCastAllowedSingle type2 type1
  where
    implicitCastAllowedSingle :: String -> String -> Bool
    implicitCastAllowedSingle type1 type2
        | type1 == type2                               = True
        | isIntegralType type1 && isIntegralType type2 = True
        | isIntegralType type1 && type2 == "float"     = True
        | otherwise                                    = False
    
typeCheckAssignOp :: AssignmentOp -> String -> SyntaxNode -> Environment -> Bool
typeCheckAssignOp op varName rhs env = case op of
    NoOp    -> isImplicitCastAllowed rhsType varType
    PlusEq  -> typeCheckBinaryOp Addition rhs (IdentifierNode varName) env
    MinusEq -> typeCheckBinaryOp Subtraction rhs (IdentifierNode varName) env
    MulEq   -> typeCheckBinaryOp Multiplication rhs (IdentifierNode varName) env
    DivEq   -> typeCheckBinaryOp Division rhs (IdentifierNode varName) env
    ModEq   -> typeCheckBinaryOp Mod rhs (IdentifierNode varName) env
  where
    rhsType = decltype rhs env
    varType = decltype (IdentifierNode varName) env

typeCheckBinaryOp :: BinaryOp -> SyntaxNode -> SyntaxNode -> Environment -> Bool
typeCheckBinaryOp op lhs rhs env
    | op == Addition           = neitherIsString && isImplicitCastAllowed lhsType rhsType
    | op == Multiplication     = neitherIsString && isImplicitCastAllowed lhsType rhsType
    | op == Subtraction        = neitherIsString && isImplicitCastAllowed lhsType rhsType
    | op == Division           = neitherIsString && isImplicitCastAllowed lhsType rhsType
    | op == Mod                = neitherIsString && isIntegralType lhsType && isIntegralType rhsType
    | op == Equal              = neitherIsString && isImplicitCastAllowed lhsType rhsType
    | op == NotEqual           = neitherIsString && isImplicitCastAllowed lhsType rhsType
    | op == LessThan           = neitherIsString && isImplicitCastAllowed lhsType rhsType
    | op == GreaterThan        = neitherIsString && isImplicitCastAllowed lhsType rhsType
    | op == GreaterThanOrEqual = neitherIsString && isImplicitCastAllowed lhsType rhsType
    | op == LessThanOrEqual    = neitherIsString && isImplicitCastAllowed lhsType rhsType
    | op == Or                 = neitherIsString && lhsType == "bool" && rhsType == "bool"
    | op == And                = neitherIsString && lhsType == "bool" && rhsType == "bool"
  where
    lhsType = decltype lhs env
    rhsType = decltype rhs env
    neitherIsString = lhsType /= "string" && rhsType /= "string"

typeCheckUnaryOp :: UnaryOp -> SyntaxNode -> Environment -> Bool
typeCheckUnaryOp Negate sub env
    | subType == "string" = False
    | subType == "bool"   = False
    | otherwise           = True
  where
    subType = decltype sub env
typeCheckUnaryOp Not sub env
    | subType == "bool" = True
    | otherwise         = False
  where
    subType = decltype sub env

validateSyntaxNode :: SyntaxNode -> Environment -> (Environment, Bool)
validateSyntaxNode statement env = case statement of
    FunctionCallNode name args -> (env, validateCall statement env)
    LiteralNode ct -> (env, True)
    IdentifierNode name -> (env, isJust $ lookupVar name env)
    ParenthesisNode sub -> validateSyntaxNode sub env
    BinaryOpNode op lhs rhs -> (env, snd (validateSyntaxNode lhs env)
                                     && snd (validateSyntaxNode rhs env)
                                     && typeCheckBinaryOp op lhs rhs env)
    UnaryOpNode op sub -> (env, snd (validateSyntaxNode sub env)
                                && typeCheckUnaryOp op sub env)
    AssignmentNode varName op rhs -> (env, snd (validateSyntaxNode rhs env)
                                           && typeCheckAssignOp op varName rhs env)
    
    SeqNode left right -> let (modifiedEnv, valid) = validateSyntaxNode left env in
        if valid
        then
            validateSyntaxNode right modifiedEnv
        else
            (env, False)
    WhileNode condition block -> (env, snd (validateSyntaxNode condition env)
                                       && isImplicitCastAllowed (decltype condition env) "bool"
                                       && snd (validateSyntaxNode block $ EnvLink M.empty env))
    IfNode condition block -> (env, snd (validateSyntaxNode condition env)
                                    && isImplicitCastAllowed (decltype condition env) "bool"
                                    && snd (validateSyntaxNode block $ EnvLink M.empty env))
    IfElseNode condition block elseBlock -> (env, snd (validateSyntaxNode condition env)
                                                  && isImplicitCastAllowed (decltype condition env) "bool"
                                                  && snd (validateSyntaxNode block $ EnvLink M.empty env)
                                                  && snd (validateSyntaxNode block $ EnvLink M.empty env))
    ReturnNode expr -> let Just (FunctionVar currentFunctionRetType _) = lookupVar "$currentFunction" env in
        (env, snd (validateSyntaxNode expr env)
              && isImplicitCastAllowed (decltype expr env) currentFunctionRetType)
    DeclarationNode typeName id ->
        if isJust $ lookupVar id env
        then
            (env, False)
        else
            (insertIntoEnv env id (PrimitiveVar typeName), True)
    DefinitionNode typeName id expr ->
        if isJust $ lookupVar id env
        then
            (env, False)
        else
            (insertIntoEnv env id (PrimitiveVar typeName), snd (validateSyntaxNode expr (insertIntoEnv env id (PrimitiveVar typeName)))
                    && isImplicitCastAllowed (decltype expr env) typeName)
    EmptyNode -> (env, True)

lookupVar :: String -> Environment -> Maybe VarInfo
lookupVar varName (EnvLink map nextEnv) =
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
    | tp == "string" = 0
    | otherwise      = 0

largestType :: String -> String -> String
largestType t1 t2 = snd $ maximum (zip (map classifySize typeList) typeList)
  where
    typeList = [t1, t2]

binaryTypeResult :: BinaryOp -> String -> String -> String
binaryTypeResult op lhsType rhsType
    | op == Addition           = decideBasicOp lhsType rhsType
    | op == Multiplication     = decideBasicOp lhsType rhsType
    | op == Subtraction        = decideBasicOp lhsType rhsType
    | op == Division           = decideBasicOp lhsType rhsType
    | op == Mod                = largestType lhsType rhsType
    | op == Equal              = "bool"
    | op == NotEqual           = "bool"
    | op == LessThan           = "bool"
    | op == GreaterThan        = "bool"
    | op == GreaterThanOrEqual = "bool"
    | op == LessThanOrEqual    = "bool"
    | op == Or                 = "bool"
    | op == And                = "bool"
  where
    decideBasicOp lhs rhs
        | isIntegralType lhsType && isIntegralType rhsType = largestType lhsType rhsType
        | lhsType == "float" || rhsType == "float" = "float"
        | otherwise = "invalid"

unaryTypeResult :: UnaryOp -> String -> String
unaryTypeResult op subType
    | op == Negate = subType

decltype :: SyntaxNode -> Environment -> String
decltype EmptyNode env = "void"
decltype (IdentifierNode varName) env =
    case maybeVarInfo of
        Nothing -> "invalid"
        Just varInfo -> case varInfo of
                            (FunctionVar _ _) -> "invalid"
                            (PrimitiveVar tp) -> tp
  where 
    maybeVarInfo = lookupVar varName env
decltype (LiteralNode constantType) _ = case constantType of
    IntConstant _    -> "int"
    FloatConstant _  -> "float"
    BoolConstant _   -> "bool"
    StringConstant _ -> "string"
decltype (FunctionCallNode funcName _) env =
    case maybeFuncInfo of
        Nothing -> "invalid"
        Just funcInfo -> case funcInfo of
                            (FunctionVar returnTp _) -> returnTp
                            (PrimitiveVar _) -> "invalid"
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
decltype (AssignmentNode assName op rhs) env =
    case maybeVarInfo of
        Nothing -> "invalid"
        Just varInfo -> case varInfo of
                            (FunctionVar _ _) -> "invalid"
                            (PrimitiveVar tp) -> tp
  where 
    maybeVarInfo = lookupVar assName env


validateCall :: SyntaxNode -> Environment -> Bool
validateCall (FunctionCallNode name args) env =
    case funcInfo of
        Just (FunctionVar rType params) -> length args == length params && all (typeCheck env) (zip (map fst params) args)
        _                               -> False
  where
    funcInfo = lookupVar name env
    typeCheck :: Environment -> (String, SyntaxNode) -> Bool
    typeCheck env (expectedType, paramExpr) = isImplicitCastAllowed (decltype paramExpr env) expectedType
validateCall _ _ = False

-- f(false)
-- void f(int x);
