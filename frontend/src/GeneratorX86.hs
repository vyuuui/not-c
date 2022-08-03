{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module GeneratorX86 where

import CompilerShared hiding (Immediate)
import Control.Monad.State.Lazy
import Generator
import Data.Monoid.Endo
import Minimal64

type X86Listing = [String]
type EndoList = Endo X86Listing
data CodeState = CodeState
    { codeList :: EndoList
    , asmIndex :: Int
    }
type CodeWriter = State CodeState
{-
Design for an x86 generator which is reg-allocator independant:
goal: Keep the register allocation scheme hidden, auto generate necessary spillage

Our state transformer will be type CGState = StateT (whatever we name the state) CodeM
1. Change DNAInstruction to be parameterized
        data DNAInstruction --> data DNAInstruction optype
   this will let us transform the operands we work in, while maintaining the context of the instruction
   Basically, this'll only be used to go from:
        DNAInstruction DNAOperand -> DNAInstruction (X86 operand type here)
   so now we can separate register allocation (going from DNAOperands to X86 operands)
   from actual instruction translation (DNAInstructions to X86 instructions)
   DNAInstruction should be a functor, allowing us to fmap the operands from type A to type B

2. to emit instructions, since we're a StateT (just a lift):
    emit :: CodeM a -> CGState a
    emit = lift

3. Our helper to translate operands
        withTranslateOperands
            :: DNAInstruction DNAOperand
            -> (DNAInstruction (Operand rw s) -> CGState a)
            -> CGState a
   withTranslateOperands will take an instruction with DNAOperands and an action
   with the corresponding instruction holding x86 operands, and perform the necessary
   register allocation for the operands, including coating the output-ted instructions with register allocation and de-allocation, tracking register ranges or graph coloring based on the CGState

3. Workhorse to translate our instructions
        translateInstruction :: DNAInstruction (Operand rw s) -> CGState a
   translateInstruction will take an untranslated instruction with proper x86 operands and emit the necessary x86 instructions for it

translateSubroutine :: (whatever our subroutine type was) -> CGState a
translateSubroutine will take a subroutine (params, stackvars, etc), translate its instructions, and wrap with the prologue/epilogue

-}

-- data CGState = CGState { placeholder :: Int } deriving Show
-- 
-- type CGAction = StateT CGState CodeM
-- 
-- 
-- emit :: CodeM a -> CGAction a
-- emit = lift
-- 
-- makeIntOperand :: Int -> Operand R S64
-- makeIntOperand v = ImmOp $ Immediate (fromIntegral v :: Int64)
-- 
-- translateInstruction
--      :: DNAInstructionF (X86Op s) (X86Op s)
--      -> CGAction ()
-- translateInstruction (Mov dest src) = emit $ mov dest src
-- translateInstruction (Add dest src1 src2) = do emit (mov dest src1 >> add dest src2)
-- translateInstruction (Sub dest src1 src2) = do emit (mov dest src1 >> sub dest src2)
-- --translateInstruction (Mul dest src1 src2) = do emit (mov dest src1 >> mul dest src2)
-- --translateInstruction (Div dest src1 src2) = do
-- --translateInstruction (Mod dest src1 src2) = do
-- translateInstruction (Cmp src1 src2) = emit $ cmp src1 src2
-- --translateInstruction (Jmp Always dest) = 
-- translateInstruction (Param src tp) = emit $ do
--      sub rsp 8
--      mov (addr rsp) src
-- --translateInstruction (Call loc dest) = 
-- translateInstruction (ReturnVal src) = emit (mov (resizeOperand rax) src >> ret)
-- translateInstruction ReturnVoid = emit ret
-- translateInstruction (ArrayCopy dest src count) = do
--      emit $ mov rcx (makeIntOperand count)
--      jmpLabel <- emit label
--      emit $ dec rcx
--      emit $ mov dest src -- dest = rax, src = rbx -> mov [rax + rcx] [rbx + rcx]
--      emit $ j G jmpLabel
     
     
     -- if | dest == src1 -> emit $ add dest src2
     --    | dest == src2 -> emit $ add dest src1
     --    | otherwise -> 

-- Add rax rax rbx -> rax = rax + rbx
-- Add rax rbx rcx -> 
