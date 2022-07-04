{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module Generator where

import CompilerShared
import Control.Arrow
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State.Lazy
import Data.Fix
import Data.Functor.Compose
import Data.Maybe
import Parser
import Validator
import qualified Data.Heap as H
import qualified Data.Map as M

data DNAType
    = Int8  Int
    | Int16 Int
    | Int32 Int
    | Int64 Int
    | Float Int
    | InvalidType
    deriving (Eq, Ord, Show)

data DNAVariable 
    = Temp String DNAType
    | Input String DNAType
    | Local String DNAType
    deriving Show

opVarRef :: DNAVariable -> DNAOperand
opVarRef = Variable True
opVar :: DNAVariable -> DNAOperand
opVar = Variable False
exprToDNA :: DataType -> DNAType
exprToDNA dataType 
    | isPointerType dataType = Int64 1
    | dataType == boolType   = Int8 1
    | dataType == charType   = Int8 1
    | dataType == shortType  = Int16 1
    | dataType == intType    = Int32 1
    | dataType == longType   = Int64 1
    | dataType == floatType  = Float 1
    | otherwise              = error "Invalid datatype"

data DNAOperand
    = Variable Bool DNAVariable
    | MemoryRef Bool DNAVariable Int DNAType
    | Immediate Rational DNAType
    | StructMemberFixup String DNAType
    | None
    deriving Show

type DNALabel = DNAInstruction

data JmpCondition
    = Always
    | Eq 
    | Ne 
    | Gt 
    | Lt 
    | Ge 
    | Le
    deriving Show


data DNAInstruction
    = Mov DNAOperand DNAOperand
    | Add DNAOperand DNAOperand DNAOperand
    | Sub DNAOperand DNAOperand DNAOperand
    | Mul DNAOperand DNAOperand DNAOperand
    | Div DNAOperand DNAOperand DNAOperand
    | Mod DNAOperand DNAOperand DNAOperand
    | Cmp DNAOperand DNAOperand
    | Jmp JmpCondition DNALabel
    | Param DNAOperand
    | Call String DNAOperand
    | ReturnVal DNAOperand
    | ReturnVoid
    | ArrayCopy DNAOperand DNAOperand Int
    | IntToFloat DNAOperand DNAOperand
    | FloatToInt DNAOperand DNAOperand
    | Label String
    deriving Show

type DNABlock = [DNAInstruction]
type TempFreeList = M.Map DNAType [DNAVariable]
type LocalEnv = M.Map String DNAVariable
type TempVarList = (TempFreeList, Int)
type GeneratorAction = State GeneratorState
type StructMap = M.Map String StructDefinition

data GeneratorState = GeneratorState
    { labelIdx :: Int
    , freeVars :: TempVarList
    , env :: LocalEnv
    , structMap :: StructMap
    }
    deriving Show

lookupStruct :: String -> GeneratorAction StructDefinition
lookupStruct structName = do
    structs <- structMap <$> get
    let struct = M.lookup structName structs
    return $ fromMaybe (error "Failed to lookup struct") struct

getMemberOffset :: String -> StructDefinition -> Int
getMemberOffset name struct = 0
    --L.foldl' (\(offs, _) (tp, name) -> (offs + datatypeSize tp, name)) (0, "")

initialState :: [StructDefinition] -> GeneratorState
initialState defs = GeneratorState 0
                                  (M.empty, 0)
                                   M.empty
                                 $ M.fromList (map (fst . getStructDef &&& id) defs)

setEnvironment :: LocalEnv -> GeneratorAction ()
setEnvironment _ = return ()

parseDNAType :: String -> (Int -> DNAType)
parseDNAType typename
    | typename == "int8"  = Int8
    | typename == "int16" = Int16
    | typename == "int32" = Int32
    | typename == "int64" = Int64
    | typename == "float" = Float
    | otherwise           = const InvalidType

getOperandType :: DNAOperand -> DNAType
getOperandType (Variable isPtr var)
    | isPtr     = Int64 1
    | otherwise = getOperandVar var
  where
    getOperandVar (Temp _ tp)  = tp
    getOperandVar (Input _ tp) = tp
    getOperandVar (Local _ tp) = tp
getOperandType (MemoryRef _ _ _ tp) = tp
getOperandType (Immediate _ tp) = tp
getOperandType _                = error "getOperandType on Operand with 'None', this should not have passed through the validator"

addVar :: (String -> DNAType -> DNAVariable) -> String -> String -> GeneratorAction ()
addVar constructor typeName varName = do
    GeneratorState lblCtr freeVars envMap structs <- get
    let var = constructor varName $ parseDNAType typeName 1
    put $ GeneratorState lblCtr freeVars (M.insert varName var envMap) structs
addLocalVar :: String -> String -> GeneratorAction ()
addLocalVar = addVar Local
addParameterVar :: String -> String -> GeneratorAction ()
addParameterVar = addVar Input
getDNAType :: DataType -> DNAType
getDNAType (typeName, ptrList) =
    let baseTypeConstructor =
          if null ptrList || last ptrList > 0
            then parseDNAType typeName
            else Int64
        totalElems = product $ takeWhile (>0) ptrList
    in  baseTypeConstructor totalElems

getTempVar :: DNAType -> GeneratorAction DNAVariable
getTempVar typeName = do
    GeneratorState lblCtr (tmpList, tmpCount) envMap structs <- get
    if M.member typeName tmpList
      then do
        let (Just freeVars) = M.lookup typeName tmpList
        if not $ null freeVars
          then do
            put $ GeneratorState lblCtr (M.insert typeName (tail freeVars) tmpList, tmpCount) envMap structs
            return $ head freeVars
          else addNewTemp typeName
      else addNewTemp typeName
  where
    addNewTemp :: DNAType -> GeneratorAction DNAVariable
    addNewTemp typeName = do
        state (\(GeneratorState lblCtr (tmpMap, tmpCount) envMap structs) ->
            let newVarName = 't' : show tmpCount
                newVar = Temp newVarName typeName
                newTmpList = M.findWithDefault [] typeName tmpMap
                newTmpMap = M.insert typeName newTmpList tmpMap
                newEnvMap = M.insert newVarName newVar envMap
            in (newVar, GeneratorState lblCtr (newTmpMap, tmpCount + 1) newEnvMap structs))

freeTempVar :: DNAVariable -> GeneratorAction ()
freeTempVar var = do
    GeneratorState lblCtr (tmpList, tmpCount) envMap structs <- get
    let result = insertVar var tmpList
    when (isJust result) $ put $ GeneratorState lblCtr (fromJust result, tmpCount) envMap structs
  where
    insertVar :: DNAVariable -> TempFreeList -> Maybe TempFreeList
    insertVar var tmpMap = do
        let Temp _ varType = var
        freeList <- M.lookup varType tmpMap
        return $ M.insert varType (var:freeList) tmpMap

tryFreeOperand :: DNAOperand -> GeneratorAction ()
tryFreeOperand (Variable _ var) = case var of
    Temp _ _ -> freeTempVar var
--tryFreeOperand MemoryRef DNAVariable Bool Int DNAType
tryFreeOperand _ = return ()

createLabel :: GeneratorAction DNAInstruction
createLabel = do
    GeneratorState ctr temps env structs <- get
    let newLbl = "l" ++ show ctr
    put $ GeneratorState (ctr + 1) temps env structs
    return $ Label newLbl

generateIr :: SyntaxNode -> GeneratorAction (DNABlock, DNAOperand)
generateIr = generateIrHelper . snd . getCompose . unFix
  where
    generateIrHelper (IfNode condition block) = do
        (conditionBlock, resultOp) <- generateIr condition
        (bodyBlock, _) <- generateIr block
        afterLbl <- createLabel
        let newBlock = (conditionBlock
                    ++ [Cmp resultOp (Immediate 0 (Int8 1)),
                        Jmp Eq afterLbl]
                    ++  bodyBlock
                    ++ [afterLbl], None)
        tryFreeOperand resultOp
        return newBlock
    generateIrHelper (IfElseNode condition trueBody falseBody) = do
        (conditionBlock, resultOp) <- generateIr condition
        (trueBlock, _) <- generateIr trueBody
        (falseBlock, _) <- generateIr falseBody
        afterLbl <- createLabel
        elseLbl <- createLabel
        let newBlock = (conditionBlock
                    ++ [Cmp resultOp (Immediate 0 (Int8 1)),
                        Jmp Eq elseLbl]
                    ++  trueBlock
                    ++ [Jmp Always afterLbl]
                    ++ [elseLbl]
                    ++ falseBlock
                    ++ [afterLbl], None)
        tryFreeOperand resultOp
        return newBlock
    generateIrHelper (ReturnNode expr) = do
        (exprBlock, resultOp) <- generateIr expr
        tryFreeOperand resultOp
        if isEmptyNode expr
            then return ([ReturnVoid], None)
            else return (exprBlock ++ [ReturnVal resultOp], None)
    generateIrHelper EmptyNode = return ([], None)
    generateIrHelper (SeqNode first second) = do
        (statement, _) <- generateIr first
        (statementTwo, _) <- generateIr second
        return (statement ++ statementTwo, None)
    generateIrHelper (WhileNode cond body) = do
        (conditionBlock, resultOp) <- generateIr cond
        (bodyBlock, _) <- generateIr body
        afterLbl <- createLabel
        condLbl <- createLabel
        let newBlock = ([condLbl]
                    ++ conditionBlock
                    ++ [Cmp resultOp (Immediate 0 (Int8 1)),
                        Jmp Eq afterLbl]
                    ++ bodyBlock
                    ++ [Jmp Always condLbl]
                    ++ [afterLbl], None)
        tryFreeOperand resultOp
        return newBlock
    generateIrHelper (DeclarationNode datatype id) = do
        localEnv <- env <$> get
        let dnaType = getDNAType datatype
        let var = Local id dnaType
        setEnvironment (M.insert id var localEnv)
        return ([], None)


generateIrExpr :: Expr -> GeneratorAction (DNABlock, DNAOperand)
generateIrExpr = uncurry generateIrExprHelper . first dataType . getCompose . unFix
  where
    generateIrExprHelper :: DataType -> ExprF Expr -> GeneratorAction (DNABlock, DNAOperand)
    generateIrExprHelper exprType (BinaryOpNode Addition left right) = do
        (leftBlock, resultOp) <- generateIrExpr left
        (rightBlock, resultOp2) <- generateIrExpr right
        let sumType = getOperandType resultOp
        sum <- getTempVar sumType
        let newBlock = (leftBlock
                    ++  rightBlock
                    ++ [Add (opVar sum) resultOp resultOp2], opVar sum)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType (BinaryOpNode Subtraction left right) = do
        (leftBlock, resultOp) <- generateIrExpr left
        (rightBlock, resultOp2) <- generateIrExpr right
        let diffType = getOperandType resultOp
        diff <- getTempVar diffType
        let newBlock = (leftBlock
                    ++  rightBlock
                    ++ [Sub (opVar diff) resultOp resultOp2], opVar diff)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType (BinaryOpNode Multiplication left right) = do
        (leftBlock, resultOp) <- generateIrExpr left
        (rightBlock, resultOp2) <- generateIrExpr right
        let prodType = getOperandType resultOp
        prod <- getTempVar prodType
        let newBlock = (leftBlock
                    ++  rightBlock
                    ++ [Mul (opVar prod) resultOp resultOp2], opVar prod)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType (BinaryOpNode Division  left right) = do
        (leftBlock, resultOp) <- generateIrExpr left
        (rightBlock, resultOp2) <- generateIrExpr right
        let quotType = getOperandType resultOp
        quot <- getTempVar quotType
        let newBlock = (leftBlock
                    ++  rightBlock
                    ++ [Div (opVar quot) resultOp resultOp2], opVar quot)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType (BinaryOpNode Modulus left right) = do
        (leftBlock, resultOp) <- generateIrExpr left
        (rightBlock, resultOp2) <- generateIrExpr right
        let modType = getOperandType resultOp
        mod <- getTempVar modType
        let newBlock = (leftBlock
                    ++  rightBlock
                    ++ [Mod (opVar mod) resultOp resultOp2], opVar mod)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType (BinaryOpNode Equal left right) = do
        (leftBlock, resultOp) <- generateIrExpr left
        (rightBlock, resultOp2) <- generateIrExpr right
        equals <- getTempVar (Int8 1)
        equalLabel <- createLabel
        let eqVar = opVar equals
        let newBlock = (leftBlock
                    ++  rightBlock
                    ++ [Mov eqVar (Immediate 1 (Int8 1))]
                    ++ [Cmp resultOp resultOp2]
                    ++ [Jmp Eq equalLabel]
                    ++ [Mov eqVar (Immediate 0 (Int8 1))]
                    ++ [equalLabel], eqVar)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType (BinaryOpNode NotEqual left right) = do
        (leftBlock, resultOp) <- generateIrExpr left
        (rightBlock, resultOp2) <- generateIrExpr right
        notEquals <- getTempVar (Int8 1)
        equalLabel <- createLabel
        let neVar = opVar notEquals
        let newBlock = (leftBlock
                    ++  rightBlock
                    ++ [Mov neVar (Immediate 0 (Int8 1))]
                    ++ [Cmp resultOp resultOp2]
                    ++ [Jmp Eq equalLabel]
                    ++ [Mov neVar (Immediate 1 (Int8 1))]
                    ++ [equalLabel], neVar)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType (BinaryOpNode LessThan left right) = do
        (leftBlock, resultOp) <- generateIrExpr left
        (rightBlock, resultOp2) <- generateIrExpr right
        lessThan <- getTempVar (Int8 1)
        lessThanLabel <- createLabel
        let ltVar = opVar lessThan
        let newBlock = (leftBlock
                    ++  rightBlock
                    ++ [Mov ltVar (Immediate 1 (Int8 1))]
                    ++ [Cmp resultOp resultOp2]
                    ++ [Jmp Lt lessThanLabel]
                    ++ [Mov ltVar (Immediate 0 (Int8 1))]
                    ++ [lessThanLabel], ltVar)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType (BinaryOpNode GreaterThanOrEqual left right) = do
        (leftBlock, resultOp) <- generateIrExpr left
        (rightBlock, resultOp2) <- generateIrExpr right
        lessThan <- getTempVar (Int8 1)
        lessThanLabel <- createLabel
        let ltVar = opVar lessThan
        let newBlock = (leftBlock
                    ++  rightBlock
                    ++ [Mov ltVar (Immediate 0 (Int8 1))]
                    ++ [Cmp resultOp resultOp2]
                    ++ [Jmp Lt lessThanLabel]
                    ++ [Mov ltVar (Immediate 1 (Int8 1))]
                    ++ [lessThanLabel], ltVar)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType (BinaryOpNode GreaterThan left right) = do
        (leftBlock, resultOp) <- generateIrExpr left
        (rightBlock, resultOp2) <- generateIrExpr right
        greaterThan <- getTempVar (Int8 1)
        greaterThanLabel <- createLabel
        let gtVar = opVar greaterThan
        let newBlock = (leftBlock
                    ++  rightBlock
                    ++ [Mov gtVar (Immediate 1 (Int8 1))]
                    ++ [Cmp resultOp resultOp2]
                    ++ [Jmp Gt greaterThanLabel]
                    ++ [Mov gtVar (Immediate 0 (Int8 1))]
                    ++ [greaterThanLabel], gtVar)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType (BinaryOpNode LessThanOrEqual left right) = do
        (leftBlock, resultOp) <- generateIrExpr left
        (rightBlock, resultOp2) <- generateIrExpr right
        greaterThan <- getTempVar (Int8 1)
        greaterThanLabel <- createLabel
        let gtVar = opVar greaterThan
        let newBlock = (leftBlock
                    ++  rightBlock
                    ++ [Mov gtVar (Immediate 0 (Int8 1))]
                    ++ [Cmp resultOp resultOp2]
                    ++ [Jmp Gt greaterThanLabel]
                    ++ [Mov gtVar (Immediate 1 (Int8 1))]
                    ++ [greaterThanLabel], gtVar)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType (BinaryOpNode Or left right) = do
        (leftBlock, resultOp) <- generateIrExpr left
        (rightBlock, resultOp2) <- generateIrExpr right
        result <- getTempVar (Int8 1)
        shortCircuit <- createLabel
        let resVar = opVar result
        let newBlock = (leftBlock
                    ++ [Mov resVar resultOp]
                    ++ [Cmp resultOp (Immediate 1 (Int8 1))]
                    ++ [Jmp Eq shortCircuit]
                    ++ rightBlock
                    ++ [Mov resVar resultOp2]
                    ++ [shortCircuit], resVar)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType (BinaryOpNode And left right) = do
        (leftBlock, resultOp) <- generateIrExpr left
        (rightBlock, resultOp2) <- generateIrExpr right
        result <- getTempVar (Int8 1)
        shortCircuit <- createLabel
        let resVar = opVar result
        let newBlock = (leftBlock
                    ++ [Mov resVar resultOp]
                    ++ [Cmp resultOp (Immediate 0 (Int8 1))]
                    ++ [Jmp Eq shortCircuit]
                    ++ rightBlock
                    ++ [Mov resVar resultOp2]
                    ++ [shortCircuit], resVar)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType (UnaryOpNode Negate expr) = do
        (subBlock, resultOp) <- generateIrExpr expr
        let negType = getOperandType resultOp
        negation <- getTempVar negType
        let negVar = opVar negation
        let newBlock = (subBlock
                    ++ [Sub negVar (Immediate 0 negType) resultOp], negVar)
        tryFreeOperand resultOp
        return newBlock
    generateIrExprHelper exprType (UnaryOpNode Not expr) = do
        (notBlock, resultOp) <- generateIrExpr expr
        _not <- getTempVar (Int8 1)
        let notVar = opVar _not
        let newBlock = (notBlock
                    ++ [Sub notVar (Immediate 1 (Int8 1)) resultOp], notVar)
        tryFreeOperand resultOp
        return newBlock
    generateIrExprHelper exprType (UnaryOpNode Reference expr) = do
        (refBlock, resultOp) <- generateIrExpr expr
        let refTo = case resultOp of
                    Variable _ dnaVar -> opVarRef dnaVar
                    _                 -> error "Validator broken :("
        return ([], refTo)
    generateIrExprHelper exprType node@(UnaryOpNode Dereference expr) = do
        (derefBlock, resultOp) <- generateIrExpr expr
        ptr <- getTempVar (Int64 1)
        let ptrDerefType = exprToDNA exprType
            ptrDeref = MemoryRef False ptr 0 ptrDerefType
        let newBlock = (derefBlock
                    ++ [Mov (Variable False ptr) resultOp], ptrDeref)
        tryFreeOperand resultOp
        return newBlock
    generateIrExprHelper exprType node@(IdentifierNode name) = do
        env <- env <$> get
        let Just var = M.lookup name env
        return ([], Variable False var)
    generateIrExprHelper exprType node@(LiteralNode lit) = do
        case lit of
            IntConstant v    -> return ([], Immediate (toRational v) $ Int64 1)
            FloatConstant v  -> return ([], Immediate (toRational v) $ Float 1)
            BoolConstant v   -> return ([], Immediate (if v then 1 else 0) $ Int8 1)
            StringConstant v -> error "Strings not supported yet"
    generateIrExprHelper exprType node@(FunctionCallNode name args) = do
        instList <- mapM generateIrExpr args
        let paramInsts = map (Param . snd) instList
        let argBlocks  = concatMap fst instList
        returnVal <- getTempVar $ exprToDNA exprType
        let returnOp = Variable False returnVal
        let newBlock = (argBlocks
                     ++ paramInsts
                     ++ [Call name returnOp], returnOp)
        mapM_ (tryFreeOperand . snd) instList
        return newBlock
    generateIrExprHelper exprType node@(ArrayIndexNode arr idx) = do
        (arrBlock, resultOp) <- generateIrExpr arr
        (idxBlock, resultOp2) <- generateIrExpr idx
        ptr <- getTempVar (Int64 1)
        let ptrDerefType = exprToDNA exprType
            ptrDeref = MemoryRef False ptr 0 ptrDerefType
            ptrRaw = Variable False ptr
        let newBlock = (arrBlock
                     ++ idxBlock
                     ++ [Add ptrRaw resultOp resultOp2], ptrDeref)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType node@(ParenthesisNode sub) = generateIrExpr sub
    generateIrExprHelper exprType node@(AssignmentNode op lhs rhs) = do
        (rightBlock, resultOp) <- generateIrExpr rhs
        (leftBlock, resultOp2) <- generateIrExpr lhs
        let assnInsts = case op of
                NoOp -> [Mov resultOp resultOp2]
                PlusEq -> [Add resultOp resultOp resultOp2]
                MinusEq -> [Sub resultOp resultOp resultOp2]
                MulEq -> [Mul resultOp resultOp resultOp2]
                DivEq -> [Div resultOp resultOp resultOp2]
                ModEq -> [Mod resultOp resultOp resultOp2]
        let newBlock = (rightBlock
                     ++ leftBlock
                     ++ assnInsts, resultOp)
        tryFreeOperand resultOp2
        return newBlock
    generateIrExprHelper exprType node@(CastNode toType expr) = do
        let castType = exprToDNA toType
        (exprBlock, resultOp) <- generateIrExpr expr
        let resultOpType = getOperandType resultOp
        outVar <- getTempVar castType
        let outOperand = Variable False outVar
        let castInst = if | resultOpType == Float 1 && castType /= Float 1 -> [FloatToInt resultOp outOperand]
                          | resultOpType /= Float 1 && castType == Float 1 -> [IntToFloat resultOp outOperand]
                          | resultOpType /= Float 1 && castType /= Float 1 -> [Mov outOperand resultOp]
        let newBlock = (exprBlock
                     ++ castInst, outOperand)
        tryFreeOperand resultOp
        return newBlock
    generateIrExprHelper exprType node@(StructMemberNode id) = do
        let dnaType = getDNAType exprType
        retVar <- getTempVar dnaType
        let retOp = Variable False retVar
        return ([Mov retOp (StructMemberFixup id dnaType)], retOp)
    generateIrExprHelper exprType node@(MemberAccessNode isPtr lhs rhs) = do
        (lhsBlock, structOp) <- generateIrExpr lhs
        (rhsBlock, valOp) <- generateIrExpr rhs

        let fixedRhs = foldr (curry (first fixupOperand >>> uncurry (:))) [] rhsBlock
        return ([], None)
      where
        fixupOperand :: DNAInstruction -> DNAInstruction
        -- fixupOperand (Mov op1 (StructMemberFixup name memType)) =
            -- Mov op1 ()
        fixupOperand op = op