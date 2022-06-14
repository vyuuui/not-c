module Generator
(

) where

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import Parser
import Lexer

data VarInfo = FunctionVar String [(String, String)] | PrimitiveVar String
data Environment = EnvLink (M.Map String VarInfo) Environment | EnvBase (M.Map String VarInfo)

-- Check variable existence upon reference
--  - Add declared variables & functions to environment as they are added
-- Check functions take the correct number of parameters and type
-- 

--reduceTypes :: (String, String) -> String
--reduceTypes (left, right) = 


validateProgram :: Program -> Bool
validateProgram program = buildEnvBase program
    where
        buildEnvBase :: Program -> Environment
        buildEnvBase program = EnvBase(foldl addFunctionToEnvironment M.empty program)
            where 
                addFunctionToEnvironment (env, func) = case func of
                    FunctionDefinitionNode returnType name argList -> M.insert name FunctionVar(returnType, argList)
                    _ -> env

validateFunction :: FunctionDefinitionNode -> Environment -> Bool
validateFunction func env = case func of
    FunctionDefinitionNode _ _ _ body -> validateSyntaxNode body env

isImplicitCastAllowed :: String -> String -> Bool
isImplicitCastAllowed 

typeCheckAssignOp :: AssignOp -> String -> SyntaxNode -> Environment -> Bool
typeCheckAssignOp op varName rhs env = case op of
    NoOp    -> isImplicitCastAllowed rhsType varType
    PlusEq  -> False
    MinusEq -> False
    MulEq   -> False
    DivEq   -> False
    ModEq   -> False
  where
    rhsType = decltype rhs env
    varType = decltype (IdentifierNode varName) env


typeCheckUnaryOp :: UnaryOp -> SyntaxNode -> Environment -> Bool
typeCheckUnaryOp Negate sub env
    | sub == "string" = False
    | sub == "bool"   = False
    | otherwise       = True
  where
    subType = decltype subType env

validateSyntaxNode :: SyntaxNode -> Environment -> (Environment, Bool)
validateSyntaxNode statement env = case statement of
    FunctionCallNode name args -> validateCall statement env
    LiteralNode ct -> True
    IdentifierNode name -> isJust $ lookupVar name env
    ParenthesisNode sub -> validateSyntaxNode sub env
    BinaryOpNode op lhs rhs -> (env, (snd $ validateSyntaxNode lhs env) && (snd $ validateSyntaxNode rhs env) && (typeCheckBinaryOp op lhs rhs env))
    UnaryOpNode op sub -> (env, (snd $ validateSyntaxNode sub env) && (typeCheckUnaryOp op sub env))
    AssignmentNode varName op rhs -> (env, (snd $ validateSyntaxNode rhs env) && (typeCheckAssignOp op varName rhs env))
    
    SeqNode left right -> let (modifiedEnv, valid) = validateSyntaxNode left env in
        if valid
        then
            validateSyntaxNode right modifiedEnv
        else
            (env, False)
    WhileNode condition block -> (validateSyntaxNode condition env) && (validateSyntaxNode block EnvLink(M.empty, env))
    IfNode condition block -> (validateSyntaxNode condition env) && (validateSyntaxNode block EnvLink(M.empty, env))
    IfElseNode condition block elseBlock -> (validateSyntaxNode condition env) && (validateSyntaxNode block EnvLink(M.empty, env)) && (validateSyntaxNode block EnvLink(M.empty, env))
    ReturnNode expr -> validateSyntaxNode expr env
    DeclarationNode typeName id ->
        if M.member id
        then
            (env, False)
        else
            (M.insert id VarInfo $ PrimitiveVar typeName, True)
    DefinitionNode typeName id expr ->
        if M.member id
        then
            (env, False)
        else
            validateSyntaxNode expr (M.insert id VarInfo $ PrimitiveVar typeName)

lookupVar :: String -> Environment -> Maybe VarInfo
lookupVar varName (EnvLink map nextEnv) =
    if M.member varName map
    then M.lookup varName map
    else lookupVar varName nextEnv
lookupVar varName (EnvBase map) = M.lookup varName map

decltype :: SyntaxNode -> Environment -> String
decltype (IdentifierNode varName) env =
    case maybeVarInfo of
        Nothing -> "invalid"
        Just varInfo -> case varInfo of
                            (FunctionVar _ _) -> "invalid"
                            (PrimitiveVar tp) -> tp
  where 
    maybeVarInfo = lookupVar varName env
decltype (LiteralNode constantType) _ = case constantType of
    IntConstant -> "int"
    FloatConstant -> "float"
    BoolConstant -> "bool"
    StringConstant -> "string"
decltype (FunctionCallNode funcName _) env =
    case maybeFuncInfo of
        Nothing -> "invalid"
        Just funcInfo -> case funcInfo of
                            (FunctionVar returnTp _) -> returnTp
                            (PrimitiveVar _) -> "invalid"
  where 
    maybeFuncInfo = lookupVar funcName env
decltype (ParenthesisNode sub) env = decltype sub env
decltype (BinaryOpNode op lhs rhs) env = "invalid"
  where
    lhsType = decltype lhs env
    rhsType = decltype rhs env
decltype (UnaryOpNode op sub) env = "invalid"
  where
    subType = decltype sub env
decltype (AssignmentNode assName op rhs) =
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
        (FunctionVar rType params) -> length args == length params && and $ map typeCheck args 
        _                          -> False
  where
    funcInfo = lookupVar name env
    typeCheck :: String -> SyntaxNode -> Bool
    typeCheck expectedType paramExpr =

-- f(false)
-- void f(int x);

validateCall _ _ = False