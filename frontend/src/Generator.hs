module Generator where

import ParserStateful
import Control.Monad.Trans
import Control.Monad.Trans.State.Lazy
import qualified Data.Heap as H
import qualified Data.Map as M
import Data.Maybe

data DNAType = Int8 | Int16 | Int32 | Int64 | Float

data ImmInner = Integral Int | Floating Float

data DNAOperand
    = Variable String
    | MemoryRef String Bool Int DNAType
    | Immediate ImmInner DNAType

type DNALabel = DNAInstruction

data JmpCondition = Always | Eq | Ne | Gt | Lt | Ge | Le

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
    | ReturnVal DNALabel
    | ReturnVoid
    | ArrayCopy DNAOperand DNAOperand Int
    | IntToFloat DNAOperand DNAOperand
    | FloatToInt DNAOperand DNAOperand
    | Label String

type DNABlock = [DNAInstruction]
type TempFreeList = M.Map String [String]
type TempVarList = (TempFreeList, Int)
type GeneratorAction = State GeneratorState

data GeneratorState = GeneratorState
    { labelIdx :: Int
    , freeVars :: TempVarList
    }

getTempVar :: String -> GeneratorAction String
getTempVar typeName = do 
    GeneratorState lblCtr (tmpList, tmpCount) <- get
    if M.member typeName tmpList
      then do
        let (Just freeVars) = M.lookup typeName tmpList
        if not $ null freeVars
          then do 
            put $ GeneratorState lblCtr (M.insert typeName (tail freeVars) tmpList, tmpCount)
            return $ head freeVars
          else do
            put $ GeneratorState lblCtr (tmpList, tmpCount + 1)
            return $ 't' : show tmpCount
      else do
          put $ GeneratorState lblCtr (M.insert typeName [] tmpList, tmpCount + 1)
          return $ 't' : show tmpCount

createLabel :: GeneratorAction DNAInstruction
createLabel = do
    GeneratorState ctr temps <- get
    let newLbl = "l" ++ show ctr
    put $ GeneratorState (ctr + 1) temps
    return $ Label newLbl

generateIr :: SyntaxNode -> GeneratorAction DNABlock
generateIr (IfNode condition block) = do
    conditionBlock <- generateIr condition 
    bodyBlock <- generateIr block
    afterLbl <- createLabel
    return $ conditionBlock 
         ++ [Cmp (Variable "result") (Immediate (Integral 0) Int8),
             Jmp Eq afterLbl]
         ++  bodyBlock
         ++ [afterLbl]
