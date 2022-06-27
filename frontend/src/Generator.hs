module Generator where

import Parser
import CompilerShared
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State.Lazy
import qualified Data.Heap as H
import qualified Data.Map as M
import Data.Maybe

data DNAType
    = Int8  Int
    | Int16 Int
    | Int32 Int
    | Int64 Int
    | Float Int
    | InvalidType
    deriving (Eq, Ord, Show)

data ImmInner = Integral Int | Floating Float deriving Show

data DNAVariable 
    = Temp String DNAType
    | Input String DNAType
    | Local String DNAType
    deriving Show

data DNAOperand
    = Variable DNAVariable
    | MemoryRef DNAVariable Bool Int DNAType
    | Immediate ImmInner DNAType
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
    | Call DNALabel DNAOperand
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

data GeneratorState = GeneratorState
    { labelIdx :: Int
    , freeVars :: TempVarList
    , env :: LocalEnv
    }
    deriving Show

initialState :: GeneratorState
initialState = GeneratorState 0 (M.empty, 0) M.empty

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
getOperandType (Variable var) = getOperandVar var
  where
    getOperandVar (Temp _ tp)  = tp
    getOperandVar (Input _ tp) = tp
    getOperandVar (Local _ tp) = tp
getOperandType (MemoryRef _ _ _ tp) = tp
getOperandType (Immediate _ tp) = tp
getOperandType _                = error "getOperandType on Operand with 'None', this should not have passed through the validator"

addVar :: (String -> DNAType -> DNAVariable) -> String -> String -> GeneratorAction ()
addVar constructor typeName varName = do
    GeneratorState lblCtr freeVars envMap <- get
    let var = constructor varName $ parseDNAType typeName 1
    put $ GeneratorState lblCtr freeVars (M.insert varName var envMap)
addLocalVar :: String -> String -> GeneratorAction ()
addLocalVar = addVar Local
addParameterVar :: String -> String -> GeneratorAction ()
addParameterVar = addVar Input
getDNAType :: DataType -> GeneratorAction DNAType
getDNAType (typeName, ptrList) = do
    let baseTypeConstructor = if null ptrList || last ptrList > 0
        then parseDNAType typeName
        else Int64
    let totalElems = product $ takeWhile (>0) ptrList
    return $ baseTypeConstructor totalElems

getTempVar :: DNAType -> GeneratorAction DNAVariable
getTempVar typeName = do
    GeneratorState lblCtr (tmpList, tmpCount) envMap <- get
    if M.member typeName tmpList
      then do
        let (Just freeVars) = M.lookup typeName tmpList
        if not $ null freeVars
          then do
            put $ GeneratorState lblCtr (M.insert typeName (tail freeVars) tmpList, tmpCount) envMap
            return $ head freeVars
          else addNewTemp typeName
      else addNewTemp typeName
  where
    addNewTemp :: DNAType -> GeneratorAction DNAVariable
    addNewTemp typeName = do
        state (\(GeneratorState lblCtr (tmpMap, tmpCount) envMap) ->
            let newVarName = 't' : show tmpCount
                newVar = Temp newVarName typeName
                newTmpList = M.findWithDefault [] typeName tmpMap
                newTmpMap = M.insert typeName newTmpList tmpMap
                newEnvMap = M.insert newVarName newVar envMap
            in (newVar, GeneratorState lblCtr (newTmpMap, tmpCount + 1) newEnvMap))

freeTempVar :: DNAVariable -> GeneratorAction ()
freeTempVar var = do
    GeneratorState lblCtr (tmpList, tmpCount) envMap <- get
    let result = insertVar var tmpList
    when (isJust result) $ put $ GeneratorState lblCtr (fromJust result, tmpCount) envMap
  where
    insertVar :: DNAVariable -> TempFreeList -> Maybe TempFreeList
    insertVar var tmpMap = do
        let Temp _ varType = var
        freeList <- M.lookup varType tmpMap
        return $ M.insert varType (var:freeList) tmpMap

createLabel :: GeneratorAction DNAInstruction
createLabel = do
    GeneratorState ctr temps env <- get
    let newLbl = "l" ++ show ctr
    put $ GeneratorState (ctr + 1) temps env
    return $ Label newLbl

generateIr :: SyntaxNode -> GeneratorAction (DNABlock, DNAOperand)
generateIr (IfNode condition block) = do
    (conditionBlock, resultOp) <- generateIr condition
    (bodyBlock, _) <- generateIr block
    afterLbl <- createLabel
    let newBlock = (conditionBlock
                ++ [Cmp resultOp (Immediate (Integral 0) (Int8 1)),
                    Jmp Eq afterLbl]
                ++  bodyBlock
                ++ [afterLbl], None)
    --freeTempVar resultOp -- fix me!!!!! andrew
    return newBlock
generateIr (IfElseNode condition trueBody falseBody) = do
    (conditionBlock, resultOp) <- generateIr condition
    (trueBlock, _) <- generateIr trueBody
    (falseBlock, _) <- generateIr falseBody
    afterLbl <- createLabel
    elseLbl <- createLabel
    let newBlock = (conditionBlock
                ++ [Cmp resultOp (Immediate (Integral 0) (Int8 1)),
                    Jmp Eq elseLbl]
                ++  trueBlock
                ++ [Jmp Always afterLbl]
                ++ [elseLbl]
                ++ falseBlock
                ++ [afterLbl], None)
    --freeTempVar resultOp
    return newBlock
generateIr (ReturnNode expr) = do
    (exprBlock, resultOp) <- generateIr expr
    if isEmptyNode expr
        then return ([ReturnVoid], None)
        else return (exprBlock ++ [ReturnVal resultOp], None)
generateIr EmptyNode = return ([], None)
generateIr (SeqNode first second) = do
    (statement, _) <- generateIr first
    (statementTwo, _) <- generateIr second
    return (statement ++ statementTwo, None)
generateIr (WhileNode cond body) = do
    (conditionBlock, resultOp) <- generateIr cond
    (bodyBlock, _) <- generateIr body
    afterLbl <- createLabel
    condLbl <- createLabel
    let newBlock = ([condLbl]
                 ++ conditionBlock
                 ++ [Cmp resultOp (Immediate (Integral 0) (Int8 1)),
                    Jmp Eq afterLbl]
                 ++ bodyBlock
                 ++ [Jmp Always condLbl]
                 ++ [afterLbl], None)
    -- freeTempVar resultOp
    return newBlock
generateIr (DeclarationNode datatype id) = do
    localEnv <- env <$> get
    dnaType <- getDNAType datatype
    let var = Local id dnaType
    setEnvironment (M.insert id var localEnv)
    return ([], None)
generateIr (BinaryOpNode Addition left right) = do
    (leftBlock, resultOp) <- generateIr left
    (rightBlock, resultOp2) <- generateIr right
    let additionType = getOperandType resultOp
    sum <- getTempVar additionType
    let newBlock = (leftBlock
                ++  rightBlock
                ++ [Add (Variable sum) resultOp resultOp2], Variable sum)
    return newBlock
generateIr (BinaryOpNode Subtraction left right) = do
    (leftBlock, resultOp) <- generateIr left
    (rightBlock, resultOp2) <- generateIr right
    let additionType = getOperandType resultOp
    sum <- getTempVar additionType
    let newBlock = (leftBlock
                ++  rightBlock
                ++ [Sub (Variable sum) resultOp resultOp2], Variable sum)
    return newBlock
