module Typecheck (isImplicitCastAllowed, computeDecltype) where

import CompilerShared
import Control.Arrow (second, (>>>), (&&&))
import Data.Fix (Fix(..), unFix, foldFix)
import Data.Functor.Compose (Compose(..), getCompose)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M

compoundAssignable :: DataType -> Bool
compoundAssignable tp = isIntegralType tp || (isPointerType tp && not (isArrayType tp)) || isFloatType tp

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


-- This is the core typechecking function
-- It will act as both the typechecker as well as the cast generator for a full Expr tree
computeDecltype :: ValidationEnv -> StructMap -> Expr -> Expr
computeDecltype env structs = foldFix (Fix . Compose . alg . getCompose)
  where
    lookup :: String -> VarInfo
    lookup = fromMaybe (PrimitiveVar invalidType) . (`lookupVar` env)
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
        (ExprInfo dataType hd sl, exprNode) = decompose expr
        castExpr :: DataType -> DataType -> Expr
        castExpr lblType toType = Fix $ Compose (ExprInfo lblType hd sl, CastNode toType expr)

    -- By our bottom-up typecheck, if it is identifier & valid, then it must be prim/struct
    isIdVar :: Expr -> Bool
    isIdVar expr = case snd $ decompose expr of
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
    alg (ExprInfo _ _ sl, n@(ArrayLiteralNode exprs))
        | invalidType `elem` types = (ExprInfo invalidType RValue sl, n)
        | all (==firstElem) types  = (ExprInfo (firstTp, length exprs:firstPtr) RValue sl, n)
        | otherwise                = (ExprInfo invalidType RValue sl, n)
      where
        types = map typeOf exprs
        firstElem@(firstTp, firstPtr) = head types
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
                       lhsTn == rhsTn &&
                       head lhsPtr >= head rhsPtr &&
                       tail lhsPtr == tail rhsPtr
          where
            (lhsTn, lhsPtr) = typeOf lhs
            (rhsTn, rhsPtr) = typeOf rhs
    alg (ExprInfo _ _ sl, n@(AssignmentNode op lhs rhs))
        | typeOf lhs == invalidType                     = (ExprInfo invalidType LValue sl, n)
        | typeOf rhs == invalidType                     = (ExprInfo invalidType LValue sl, n)
        | handednessOf lhs /= LValue                    = (ExprInfo invalidType LValue sl, n)
        | not $ compoundAssignable $ typeOf lhs         = (ExprInfo invalidType LValue sl, n)
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
        fixMemberAccess = (ExprInfo (typeOf annotRhs) LValue sl, MemberAccessNode isPtr lhs annotRhs)
          where
            fixedRhs = maybe (ExprInfo invalidType LValue sl, n)
                  (fixStructMember $ decompose rhs)
                  (M.lookup (fst $ typeOf lhs) structs)
            annotRhs = Fix $ Compose fixedRhs
            
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

    decideCompare, decideRelCompare, decideLogical, decideModulus, decideAddition, decideMultiplication, decideSubtraction, decideDivision :: (DataType, DataType, DataType)
    decideCompare
        | typeFormMatches lhsType rhsType                  = (boolType, lhsType, rhsType)
        | isIntegralType lhsType && isIntegralType rhsType = dupe2nd boolType $ largestType lhsType rhsType
        | isIntegralType lhsType && isFloatType rhsType    = (boolType, rhsType, rhsType)
        | isFloatType lhsType && isIntegralType rhsType    = (boolType, lhsType, lhsType)
        | lhsType == nullType                              = (boolType, rhsType, rhsType)
        | rhsType == nullType                              = (boolType, lhsType, lhsType)
        | otherwise                                        = invalidResult
    decideRelCompare
        | isBoolType lhsType || isBoolType rhsType = invalidResult
        | otherwise                                = decideCompare
    decideLogical
        | lhsType == boolType && rhsType == boolType = dupe3 boolType
        | otherwise                                  = invalidResult
    decideModulus
        | isIntegralType lhsType && isIntegralType rhsType = dupe3 $ largestType lhsType rhsType
        | otherwise                                        = invalidResult
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
    decideMultiplication
    -- either are pointers -> not allowed
        | isPointerType lhsType || isPointerType rhsType = invalidResult
        | otherwise = decideAddition
    decideSubtraction
    -- ptr - ptr (long)
        | isPointerType lhsType && isPointerType rhsType &&
          typeFormMatches lhsType rhsType = (ptrdiffType, lhsType, rhsType)
        | isPointerType rhsType && isBaseType rhsType = invalidResult
        | otherwise = decideAddition
    decideDivision = decideMultiplication

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
    decideNegate, decideNot, decideReference, decideDereference, decidePrefix :: DataType -> (DataType, Handedness)
    decideNegate tp
        | isFloatType tp || isIntegralType tp = (tp, RValue)
        | otherwise = (invalidType, RValue)
    decideNot tp
        | isBoolType tp = (tp, RValue)
        | otherwise     = (invalidType, RValue)
    decideReference (typeName, ptrList) = ((typeName, 0:ptrList), RValue)
    decideDereference (typeName, ptrList)
        | (typeName, tail ptrList) == voidType = (invalidType, LValue)
        | not (null ptrList) = ((typeName, tail ptrList), LValue)
        | otherwise          = (invalidType, LValue)
    decidePrefix tp
        | subHandedness == RValue = (invalidType, RValue)
        | compoundAssignable tp   = (tp, RValue)
        | otherwise               = (invalidType, RValue)
