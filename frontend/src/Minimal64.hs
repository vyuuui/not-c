{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE FlexibleInstances #-}

module Minimal64
( DataSize (..)
, X86Reg (..)
, X86MemRef (..)
, X86SIB (..)
, ScaleFactor (..)
, Immediate (..)
, X86Op (..)
, X86Listing (..)
, EndoList (..)
, CodeState (..)
, CodeWriter (..)
, JumpCond (..)
, sizeName
, imm8
, imm16
, imm32
, imm64
, ipRel
, regMem
, regMemOff
, sibMem
, sibMemOff
, al, cl, dl, bl, spl, bpl, sil, dil, r8b, r9b, r10b, r11b, r12b, r13b, r14b, r15b
, ax, cx, dx, bx, sp, bp, si, di, r8w, r9w, r10w, r11w, r12w, r13w, r14w, r15w
, eax, ecx, edx, ebx, esp, ebp, esi, edi, r8d, r9d, r10d, r11d, r12d, r13d, r14d, r15d
, rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15
, writeBytes
, writeByte
, mov
, add
, sub
, jmp
, jcc
, call
, jmpreg
, callreg
, cmp
, test
, imul1
, imul2
, imul3
, idiv
, cbw, cwde, cdqe, cwd, cdq, cqo
, conditionVal
, jo, jno, jb, jae, je, jne, jbe, ja, js, jns, jp, jpo, jl, jge, jle, jg
, label
, showResult
) where

import Control.Arrow
import Control.Monad.State.Lazy
import Data.Bits
import Data.Bool ( bool )
import Data.Either
import Data.Functor ( (<&>) )
import Data.Functor.Classes ( Show1 )
import Data.Maybe
import Data.Monoid.Endo
import Data.Int
import Data.Word
import Numeric ( showHex )

import qualified Data.List as L

-- Most of the stuff here is 80%-rip 20%-remake of:
-- https://github.com/divipp/x86-64
-- Primary changes include
-- - Additional instructions we use for our compiler
-- - Less strict compile-time checking

bounded :: forall a b. (Integral a, Bounded b, Integral b) => a -> b -> Bool
bounded val _ =
    let max = fromIntegral (maxBound :: b) :: a
        min = fromIntegral (minBound :: b) :: a
    in  val <= max && val >= min

isInt8 :: (Integral a) => a -> Bool
isInt8 val = bounded val (0 :: Int8)
isInt16 :: (Integral a) => a -> Bool
isInt16 val = bounded val (0 :: Int16)
isInt32 :: (Integral a) => a -> Bool
isInt32 val = bounded val (0 :: Int32)

skip :: Monad m => m ()
skip = return ()

toW8 :: (Integral a) => a -> Word8
toW8 = fromIntegral
toW32 :: (Integral a) => a -> Word32
toW32 = fromIntegral

-----------------------------------------------------------------
-- Compiler size checking (ripped and reformatted from x86-64bit)
data DataSize = S8 | S16 | S32 | S64 deriving Eq

class HasDataSize a where
    size :: a -> DataSize
class IsDataSize (s :: DataSize) where
    ssize :: SSize s

data SSize (s :: DataSize) where
    SSize8 :: SSize S8
    SSize16 :: SSize S16
    SSize32 :: SSize S32
    SSize64 :: SSize S64

instance Eq (SSize s) where
    (==) SSize8 SSize8   = True
    (==) SSize16 SSize16 = True
    (==) SSize32 SSize32 = True
    (==) SSize64 SSize64 = True
instance HasDataSize (SSize s) where
    size SSize8  = S8
    size SSize16 = S16
    size SSize32 = S32
    size SSize64 = S64

instance IsDataSize s => HasDataSize (X86Reg s) where
    size _ = size (ssize :: SSize s)
instance IsDataSize s => HasDataSize (X86MemRef s) where
    size _ = size (ssize :: SSize s)
instance IsDataSize s => HasDataSize (Immediate s) where
    size _ = size (ssize :: SSize s)
instance IsDataSize s => HasDataSize (X86Op s) where
    size _ = size (ssize :: SSize s)

instance IsDataSize 'S8 where ssize = SSize8
instance IsDataSize 'S16 where ssize = SSize16
instance IsDataSize 'S32 where ssize = SSize32
instance IsDataSize 'S64 where ssize = SSize64

sizeName :: HasDataSize s => s -> String
sizeName v = case size v of 
    S8  -> "byte"
    S16 -> "word"
    S32 -> "dword"
    S64 -> "qword"

-- Registers
newtype X86Reg :: DataSize -> * where
    Reg :: Word8 -> X86Reg s
instance IsDataSize s => Show (X86Reg s) where
    show r@(Reg i) = (!! fromIntegral i) . (++ repeat (error "Invalid register index")) $ case size r of
        S8  -> ["al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil"] ++ map (++"b") rexNames
        S16 -> lowNames ++ map (++"w") rexNames
        S32 -> map ('e':) lowNames ++ map (++"d") rexNames
        S64 -> map ('r':) lowNames ++ rexNames
      where
        lowNames = ["ax", "cx", "dx", "bx", "sp", "bp", "si", "di"]
        rexNames = ["r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]

instance IsDataSize s => Eq (X86Reg s) where
    (==) (Reg r0) (Reg r1) = r0 == r1

-- Memory references
-- I'm not dealing with encoding non-64b memory references
data X86MemRefReg = RegBase (X86Reg S64) | SIBBase (X86SIB S64)
data X86MemRef s = X86MemRef
    { regSource :: X86MemRefReg
    , displace :: Maybe Int32
    }

data ScaleFactor = Scale1 | Scale2 | Scale4 | Scale8 deriving (Eq)

data X86SIB s = X86SIB
    { scale :: ScaleFactor
    , index :: X86Reg S64
    , base :: X86Reg S64
    }

instance Show ScaleFactor where
    show Scale1 = "1"
    show Scale2 = "2"
    show Scale4 = "4"
    show Scale8 = "8"

instance IsDataSize s => Show (X86SIB s) where
    show X86SIB { scale = s, index = i, base = b} =
        show b ++ (" + " ++ (show s ++ ('*':show i)))

instance IsDataSize s => Show (X86MemRef s) where
    show mr@X86MemRef { regSource = src, displace = dis } = sizeName mr ++ (" ptr " ++ case src of
        RegBase r -> '[': (show r ++ (maybe "" ((" + "++) . show) dis ++ "]"))
        SIBBase sib -> '[': (show sib ++ (maybe "" show dis ++ "]")))

-- Immediates
data Immediate :: DataSize -> * where
    Imm8  :: Int8  -> Immediate S8
    Imm16 :: Int16 -> Immediate S16
    Imm32 :: Int32 -> Immediate S32
    Imm64 :: Int64 -> Immediate S64

instance IsDataSize s => Show (Immediate s) where
    show (Imm8 v)  = show v
    show (Imm16 v) = show v
    show (Imm32 v) = show v
    show (Imm64 v) = show v

---------------------------------------------------------------------------
-- Operands with size checking (also ripped and reformatted from x86-64bit)
data X86Op :: DataSize -> * where
    RegOp   :: X86Reg s      -> X86Op s 
    MemOp   :: X86MemRef s   -> X86Op s
    ImmOp   :: Immediate s   -> X86Op s
    IPRelOp :: Immediate S32 -> X86Op s

instance IsDataSize s => Show (X86Op s) where
    show (RegOp r) = show r
    show (MemOp m) = show m
    show (ImmOp i) = show i
    show o@(IPRelOp i) = sizeName o ++ (" ptr " ++ ("[rip + " ++ (show i ++ "]")))

-- Typeclass allowing register helpers below to be context dependant
class ConvertableReg c where
    convertReg :: X86Reg s -> c s

instance ConvertableReg X86Reg where
    convertReg = id

instance ConvertableReg X86Op where
    convertReg = RegOp

-- Construct immediates
class Resizable r where
    resize :: r s -> r s'

imm8 :: (Integral a) => a -> X86Op S8
imm8 v = ImmOp $ Imm8 (fromIntegral v)
imm16 :: (Integral a) => a -> X86Op S16
imm16 v = ImmOp $ Imm16 (fromIntegral v)
imm32 :: (Integral a) => a -> X86Op S32
imm32 v = ImmOp $ Imm32 (fromIntegral v)
imm64 :: (Integral a) => a -> X86Op S64
imm64 v = ImmOp $ Imm64 (fromIntegral v)

isImm8 :: IsDataSize s => Immediate s -> Bool
isImm8 i = isInt8 $ extractImm i

extractImm :: (IsDataSize s, Num b) => Immediate s -> b
extractImm (Imm8  v) = fromIntegral v
extractImm (Imm16 v) = fromIntegral v
extractImm (Imm32 v) = fromIntegral v
extractImm (Imm64 v) = fromIntegral v

-- Construct RIP-relative operands
ipRel :: IsDataSize s => Int32 -> X86Op s
ipRel off = IPRelOp (Imm32 off)

-- Construct register-indirect memory references through reg or SIB
regMem :: IsDataSize s => X86Reg S64 -> X86Op s
regMem reg = MemOp $ X86MemRef { regSource = RegBase reg, displace = Nothing }
regMemOff :: IsDataSize s => X86Reg S64 -> Int32 -> X86Op s
regMemOff reg off = MemOp $ X86MemRef { regSource = RegBase reg, displace = Just off }
sibMem :: IsDataSize s => ScaleFactor -> X86Reg S64 -> X86Reg S64 -> X86Op s
sibMem s i b = MemOp $ X86MemRef { regSource = SIBBase (X86SIB s i b), displace = Nothing }
sibMemOff :: IsDataSize s => ScaleFactor -> X86Reg S64 -> X86Reg S64 -> Int32 -> X86Op s
sibMemOff s i b off = MemOp $ X86MemRef { regSource = SIBBase (X86SIB s i b), displace = Just off }

-- Definitions for all registers
al, cl, dl, bl, spl, bpl, sil, dil, r8b, r9b, r10b, r11b, r12b, r13b, r14b, r15b :: ConvertableReg c => c S8
al = convertReg $ Reg 0
cl = convertReg $ Reg 1
dl = convertReg $ Reg 2
bl = convertReg $ Reg 3
spl = convertReg $ Reg 4
bpl = convertReg $ Reg 5
sil = convertReg $ Reg 6
dil = convertReg $ Reg 7
r8b = convertReg $ Reg 8
r9b = convertReg $ Reg 9
r10b = convertReg $ Reg 10
r11b = convertReg $ Reg 11
r12b = convertReg $ Reg 12
r13b = convertReg $ Reg 13
r14b = convertReg $ Reg 14
r15b = convertReg $ Reg 15

ax, cx, dx, bx, sp, bp, si, di, r8w, r9w, r10w, r11w, r12w, r13w, r14w, r15w :: ConvertableReg c => c S16
ax = convertReg $ Reg 0
cx = convertReg $ Reg 1
dx = convertReg $ Reg 2
bx = convertReg $ Reg 3
sp = convertReg $ Reg 4
bp = convertReg $ Reg 5
si = convertReg $ Reg 6
di = convertReg $ Reg 7
r8w = convertReg $ Reg 8
r9w = convertReg $ Reg 9
r10w = convertReg $ Reg 10
r11w = convertReg $ Reg 11
r12w = convertReg $ Reg 12
r13w = convertReg $ Reg 13
r14w = convertReg $ Reg 14
r15w = convertReg $ Reg 15

eax, ecx, edx, ebx, esp, ebp, esi, edi, r8d, r9d, r10d, r11d, r12d, r13d, r14d, r15d :: ConvertableReg c => c S32
eax = convertReg $ Reg 0
ecx = convertReg $ Reg 1
edx = convertReg $ Reg 2
ebx = convertReg $ Reg 3
esp = convertReg $ Reg 4
ebp = convertReg $ Reg 5
esi = convertReg $ Reg 6
edi = convertReg $ Reg 7
r8d = convertReg $ Reg 8
r9d = convertReg $ Reg 9
r10d = convertReg $ Reg 10
r11d = convertReg $ Reg 11
r12d = convertReg $ Reg 12
r13d = convertReg $ Reg 13
r14d = convertReg $ Reg 14
r15d = convertReg $ Reg 15

rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15 :: ConvertableReg c => c S64
rax = convertReg $ Reg 0
rcx = convertReg $ Reg 1
rdx = convertReg $ Reg 2
rbx = convertReg $ Reg 3
rsp = convertReg $ Reg 4
rbp = convertReg $ Reg 5
rsi = convertReg $ Reg 6
rdi = convertReg $ Reg 7
r8 = convertReg $ Reg 8
r9 = convertReg $ Reg 9
r10 = convertReg $ Reg 10
r11 = convertReg $ Reg 11
r12 = convertReg $ Reg 12
r13 = convertReg $ Reg 13
r14 = convertReg $ Reg 14
r15 = convertReg $ Reg 15

-------------------
-- CodeWriter Monad
type X86Listing = [Word8]
type EndoList = Endo X86Listing
data CodeState = CodeState
    { codeList :: EndoList
    , asmIndex :: Int
    }
type CodeWriter = State CodeState


writeBytes :: [Word8] -> CodeWriter ()
writeBytes bs = modify updateState
  where
    updateState (CodeState cl idx) = CodeState (cl `mappend` Endo (bs++)) (idx + length bs)

writeByte :: Word8 -> CodeWriter ()
writeByte b = writeBytes [b]

isExtReg :: IsDataSize s => X86Reg s -> Bool
isExtReg (Reg r) = r >= 8
isHiReg :: IsDataSize s => X86Reg s -> Bool
isHiReg (Reg r) = r >= 4 && r < 8

_rexPat, _rexW, _rexR, _rexX, _rexB :: Word8
_rexPat = 0b01000000
_rexW = 0b00001000
_rexR = 0b00000100
_rexX = 0b00000010
_rexB = 0b00000001

rexModifier :: IsDataSize s => X86Op s -> X86Op s -> Maybe Word8
rexModifier op0@(RegOp rm) (RegOp reg)
    | not needsREX && rmExt == 0 && regExt == 0 = Nothing
    | otherwise = Just $ rmExt .|. regExt
  where
    rmExt = if isExtReg rm then _rexB else 0
    regExt = if isExtReg reg then _rexR else 0
    needsREX = size op0 == S8 && (isHiReg rm || isHiReg reg)
rexModifier op0@(MemOp (X86MemRef (RegBase rm) displace)) (RegOp reg)
    | not needsREX && rmExt == 0 && regExt == 0 = Nothing
    | otherwise = Just $ rmExt .|. regExt
  where
    rmExt = if isExtReg rm then _rexB else 0
    regExt = if isExtReg reg then _rexR else 0
    needsREX = size op0 == S8 && isHiReg reg
rexModifier op0@(MemOp (X86MemRef (SIBBase (X86SIB s i b)) displace)) (RegOp reg)
    | not needsREX && sibExt == 0 && regExt == 0 = Nothing 
    | otherwise = Just $ sibExt .|. regExt
  where
    sibExt = (if isExtReg i then _rexX else 0) .|. (if isExtReg b then _rexB else 0)
    regExt = if isExtReg reg then _rexR else 0
    needsREX = size op0 == S8 && isHiReg reg
rexModifier _ _ = error "Invalid/unhandled operand combination"

maybeWriteREX :: IsDataSize s => X86Op s -> X86Op s -> CodeWriter ()
maybeWriteREX rm reg = maybe skip (writeByte . (.|. _rexPat)) (rexModifier rm reg)

writeREXW :: IsDataSize s => X86Op s -> X86Op s -> CodeWriter ()
writeREXW rm reg = maybe (writeByte (_rexPat .|. _rexW)) (writeByte . (.|. (_rexW .|. _rexPat))) (rexModifier rm reg)

class ByteSerialize b where
    serialize :: b -> [Word8]

serializeShift :: (Integral a, Bits a) => Int -> a -> [Word8]
serializeShift byteCount val =
    zipWith (\val sh -> fromIntegral (val `shiftR` sh) :: Word8) (replicate byteCount val) [0, 8 .. 8 * (byteCount - 1)]
instance ByteSerialize Word8 where
    serialize = (:[])
instance ByteSerialize Word16 where
    serialize = serializeShift 2
instance ByteSerialize Word32 where
    serialize = serializeShift 4
instance ByteSerialize Word64 where
    serialize = serializeShift 8
instance ByteSerialize Int8 where
    serialize v = [fromIntegral v :: Word8]
instance ByteSerialize Int16 where
    serialize v = serializeShift 2 (fromIntegral v :: Word16)
instance ByteSerialize Int32 where
    serialize v = serializeShift 4 (fromIntegral v :: Word32)
instance ByteSerialize Int64 where
    serialize v = serializeShift 8 (fromIntegral v :: Word64)

scaleBit :: ScaleFactor -> Word8
scaleBit Scale1 = 0b00000000
scaleBit Scale2 = 0b01000000
scaleBit Scale4 = 0b10000000
scaleBit Scale8 = 0b11000000

writeModRM :: IsDataSize s => X86Op s -> X86Op s -> CodeWriter ()
writeModRM (RegOp (Reg rmNum)) (RegOp (Reg regNum)) = writeByte (0b11000000 .|. shift regMasked 3 .|. rmMasked)
  where
    rmMasked = rmNum .&. 0b00000111
    regMasked = regNum .&. 0b00000111
writeModRM (MemOp (X86MemRef (RegBase rm@(Reg rmNum)) displace)) (RegOp (Reg regNum)) = do
    writeByte (_mod .|. shift regMasked 3 .|. rmMasked)
    -- Referencing RSP as a memop requires it to be encoded as an SIB with index=rsp (index=rsp is invalid otherwise)
    if rm == rsp || rm == r12 then writeByte 0b00100100 else skip
    maybeDisplace
  where
    rmMasked = rmNum .&. 0b00000111
    regMasked = regNum .&. 0b00000111
    dispEither :: Maybe (Either Word8 Word32)
    dispEither = case displace of
        Nothing  -> if rm == rbp || rm == r13 then Just (Left 0) else Nothing
        Just val -> Just $ if isInt8 val then Left (toW8 val) else Right (toW32 val)
    -- mod: 0b00 = no displace, 0b01 = 8bit displace, 0b10 = 32bit displace
    _mod = maybe 0 (bool 0x80 0x40 . isLeft) dispEither
    maybeDisplace = maybe skip (writeBytes . (serialize ||| serialize)) dispEither
writeModRM (MemOp (X86MemRef (SIBBase (X86SIB s i@(Reg iNum) b@(Reg bNum))) displace)) (RegOp (Reg regNum)) = do
    if i == rsp then error "Invalid SIB encoding provided" else skip
    writeByte (_mod .|. shift regMasked 3 .|. 0b00000100)
    writeByte (scaleBit s .|. shift iMasked 3 .|. bMasked)
    maybeDisplace
  where
    iMasked = iNum .&. 0b00000111
    bMasked = bNum .&. 0b00000111
    regMasked = regNum .&. 0b00000111
    dispEither :: Maybe (Either Word8 Word32)
    dispEither = case displace of
        Nothing  -> if b == rbp || b == r13 then Just (Left 0) else Nothing
        Just val -> Just $ if isInt8 val then Left (toW8 val) else Right (toW32 val)
    _mod = maybe 0 (bool 0x80 0x40 . isLeft) dispEither
    maybeDisplace = maybe skip (writeBytes . (serialize ||| serialize)) dispEither
writeModRM _ _ = error "Invalid ModR/M"

writeImm :: IsDataSize s => Immediate s -> CodeWriter ()
writeImm (Imm8 v)  = writeBytes (serialize v)
writeImm (Imm16 v) = writeBytes (serialize v)
writeImm (Imm32 v) = writeBytes (serialize v)
writeImm (Imm64 v) = writeBytes (serialize v)

writeRmReg :: IsDataSize s => X86Op s -> X86Op s -> [[Word8]] -> CodeWriter ()
writeRmReg rmOp regOp opcodes = case size regOp of
    S8  -> maybeWriteREX rmOp regOp >> writeBytes (head opcodes) >> writeModRM rmOp regOp
    S16 -> writeByte 0x66 >> maybeWriteREX rmOp regOp >> writeBytes (opcodes !! 1) >> writeModRM rmOp regOp
    S32 -> maybeWriteREX rmOp regOp >> writeBytes (opcodes !! 2) >> writeModRM rmOp regOp
    S64 -> writeREXW rmOp regOp >> writeBytes (opcodes !! 3) >> writeModRM rmOp regOp

writeRmCode :: IsDataSize s => X86Op s -> Word8 -> [[Word8]] -> CodeWriter ()
writeRmCode rmOp rCode opcodes = case size rmOp of
    S8  -> maybeWriteREX rmOp nilReg >> writeBytes (head opcodes) >> writeModRM rmOp slashReg
    S16 -> writeByte 0x66 >> maybeWriteREX rmOp nilReg >> writeBytes (opcodes !! 1) >> writeModRM rmOp slashReg
    S32 -> maybeWriteREX rmOp nilReg >> writeBytes (opcodes !! 2) >> writeModRM rmOp slashReg
    S64 -> writeREXW rmOp nilReg >> writeBytes (opcodes !! 3) >> writeModRM rmOp slashReg
  where
    nilReg = convertReg $ Reg 0
    slashReg = convertReg $ Reg rCode

writeRmImm :: IsDataSize s => X86Op s -> Immediate s -> Word8 -> [[Word8]] -> CodeWriter ()
writeRmImm rmOp imm rCode opcodes = do
    writeRmCode rmOp rCode opcodes
    case size imm of
        S64 -> writeImm (Imm32 (extractImm imm))
        _   -> writeImm imm

mov :: IsDataSize s => X86Op s -> X86Op s -> CodeWriter ()
mov dest src = case (dest, src) of
    (rmOp@(RegOp _), regOp@(RegOp _)) -> writeRmReg rmOp regOp (fmap (:[]) [0x88, 0x89, 0x89, 0x89])
    (regOp@(RegOp _), rmOp@(MemOp _)) -> writeRmReg rmOp regOp (fmap (:[]) [0x8a, 0x8b, 0x8b, 0x8b])
    (rmOp@(MemOp _), regOp@(RegOp _)) -> writeRmReg rmOp regOp (fmap (:[]) [0x88, 0x89, 0x89, 0x89])
    (RegOp reg, ImmOp imm)            -> movRegImm reg imm
    (memOp@(MemOp _), ImmOp imm)      -> writeRmImm memOp imm 0 (fmap (:[]) [0xc6, 0xc7, 0xc7, 0xc7])
    _                                 -> error "Invalid operand combination for mov"
  where
    movRegImm :: IsDataSize s => X86Reg s -> Immediate s -> CodeWriter ()
    movRegImm reg@(Reg regNum) imm = case size reg of
        S8  -> rexForImm False >> writeByte (0xb0 + regMasked) >> writeImm imm
        S16 -> writeByte 0x66 >> rexForImm False >> writeByte (0xb8 + regMasked) >> writeImm imm
        S32 -> rexForImm False >> writeByte (0xb8 + regMasked) >> writeImm imm
        S64 -> rexForImm True >> writeByte (0xb8 + regMasked) >> writeImm imm
      where
        regMasked = regNum .&. 0b00000111
        rexForImm withW
            | isHiReg reg && size reg == S8 = writeByte (_rexPat .|. w)
            | isExtReg reg                  = writeByte (_rexPat .|. w .|. _rexB)
            | withW                         = writeByte (_rexPat .|. w)
            | otherwise                     = skip
          where
            w = if withW then _rexW else 0

add :: IsDataSize s => X86Op s -> X86Op s -> CodeWriter ()
add dest src = case (dest, src) of
    (rmOp@(RegOp _), regOp@(RegOp _))   -> writeRmReg rmOp regOp (fmap (:[]) [0x00, 0x01, 0x01, 0x01])
    (regOp@(RegOp _), rmOp@(MemOp _))   -> writeRmReg rmOp regOp (fmap (:[]) [0x02, 0x03, 0x03, 0x03])
    (rmOp@(MemOp _), regOp@(RegOp _))   -> writeRmReg rmOp regOp (fmap (:[]) [0x00, 0x01, 0x01, 0x01])
    (rmOp@(MemOp _), immOp@(ImmOp imm)) -> writeRmImmAdd rmOp imm
    (rmOp@(RegOp _), immOp@(ImmOp imm)) -> writeRmImmAdd rmOp imm
    _ -> error "Invalid operand combination for add"
  where
    writeRmImmAdd rmOp imm
        | isImm8 imm = writeRmCode rmOp 0 (fmap (:[]) [0x80, 0x83, 0x83, 0x83]) >> writeImm (Imm8 immVal)
        | otherwise  = writeRmImm rmOp imm 0 (fmap (:[]) [0x80, 0x81, 0x81, 0x81])
      where 
        immVal = extractImm imm

sub :: IsDataSize s => X86Op s -> X86Op s -> CodeWriter ()
sub dest src = case (dest, src) of
    (rmOp@(RegOp _), regOp@(RegOp _))   -> writeRmReg rmOp regOp (fmap (:[]) [0x28, 0x29, 0x29, 0x29])
    (regOp@(RegOp _), rmOp@(MemOp _))   -> writeRmReg rmOp regOp (fmap (:[]) [0x2a, 0x2b, 0x2b, 0x2b])
    (rmOp@(MemOp _), regOp@(RegOp _))   -> writeRmReg rmOp regOp (fmap (:[]) [0x28, 0x29, 0x29, 0x29])
    (rmOp@(MemOp _), immOp@(ImmOp imm)) -> writeRmImmSub rmOp imm
    (rmOp@(RegOp _), immOp@(ImmOp imm)) -> writeRmImmSub rmOp imm
    _ -> error "Invalid operand combination for sub"
  where
    writeRmImmSub rmOp imm
        | isImm8 imm = writeRmCode rmOp 5 (fmap (:[]) [0x80, 0x83, 0x83, 0x83]) >> writeImm (Imm8 immVal)
        | otherwise  = writeRmImm rmOp imm 5 (fmap (:[]) [0x80, 0x81, 0x81, 0x81])
      where 
        immVal = extractImm imm

jmp :: Int -> CodeWriter ()
jmp loc = do
    jumpDelta <- label <&> (`subtract`loc)
    if isInt8 (jumpDelta - 2)
      then writeBytes [0xeb, toW8 (jumpDelta - 2)]
      else writeBytes $ 0xe9:serialize (toW32 (jumpDelta - 5))

jcc :: JumpCond -> Int -> CodeWriter ()
jcc cond loc = do
    jumpDelta <- label <&> (`subtract`loc)
    if isInt8 (jumpDelta - 2)
      then writeBytes [0x70 + conditionVal cond, toW8 (jumpDelta - 2)]
      else writeBytes $ [0x0f, 0x80 + conditionVal cond] ++ serialize (toW32 (jumpDelta - 6))

call :: Int -> CodeWriter ()
call loc = do
    jumpDelta <- label <&> (`subtract`loc)
    writeBytes $ 0xe8 : serialize (toW32 (jumpDelta - 5))
    
jmpreg :: X86Op S64 -> CodeWriter ()
jmpreg rmOp@(RegOp _) = writeByte 0xff >> writeRmCode rmOp 4 (fmap (:[]) [0xff, 0xff, 0xff, 0xff])
jmpreg rmOp@(MemOp _) = writeByte 0xff >> writeRmCode rmOp 4 (fmap (:[]) [0xff, 0xff, 0xff, 0xff])
jmpreg _              = error "Invalid operand for indirect jump"

callreg :: X86Op S64 -> CodeWriter ()
callreg rmOp@(RegOp _) = writeByte 0xff >> writeRmCode rmOp 2 (fmap (:[]) [0xff, 0xff, 0xff, 0xff])
callreg rmOp@(MemOp _) = writeByte 0xff >> writeRmCode rmOp 2 (fmap (:[]) [0xff, 0xff, 0xff, 0xff])
callreg _              = error "Invalid operand for indirect jump"

cmp :: IsDataSize s => X86Op s -> X86Op s -> CodeWriter ()
cmp src1 src2 = case (src1, src2) of
    (rmOp@(RegOp _), regOp@(RegOp _)) -> writeRmReg rmOp regOp (fmap (:[]) [0x38, 0x39, 0x39, 0x39])
    (regOp@(RegOp _), rmOp@(MemOp _)) -> writeRmReg rmOp regOp (fmap (:[]) [0x3a, 0x3b, 0x3b, 0x3b])
    (rmOp@(MemOp _), regOp@(RegOp _)) -> writeRmReg rmOp regOp (fmap (:[]) [0x38, 0x39, 0x39, 0x39])
    (rmOp@(MemOp _), immOp@(ImmOp imm)) -> writeRmImmCmp rmOp imm
    (rmOp@(RegOp _), immOp@(ImmOp imm)) -> writeRmImmCmp rmOp imm
    _ -> error "Invalid operand combination for add"
  where
    writeRmImmCmp rmOp imm
        | isImm8 imm = writeRmCode rmOp 0 (fmap (:[]) [0x80, 0x83, 0x83, 0x83]) >> writeImm (Imm8 immVal)
        | otherwise  = writeRmImm rmOp imm 7 (fmap (:[]) [0x80, 0x81, 0x81, 0x81])
      where 
        immVal = extractImm imm

test :: IsDataSize s => X86Op s -> X86Op s -> CodeWriter ()
test src1 src2 = case (src1, src2) of
    (rmOp@(RegOp _), regOp@(RegOp _)) -> writeRmReg rmOp regOp (fmap (:[]) [0x84, 0x85, 0x85, 0x85])
    (regOp@(RegOp _), rmOp@(MemOp _)) -> writeRmReg rmOp regOp (fmap (:[]) [0x84, 0x85, 0x85, 0x85])
    (rmOp@(MemOp _), regOp@(RegOp _)) -> writeRmReg rmOp regOp (fmap (:[]) [0x84, 0x85, 0x85, 0x85])
    (rmOp@(RegOp _), immOp@(ImmOp imm)) -> writeRmImm rmOp imm 0 (fmap (:[]) [0xf6, 0xf7, 0xf7, 0xf7])
    (rmOp@(MemOp _), immOp@(ImmOp imm)) -> writeRmImm rmOp imm 0 (fmap (:[]) [0xf6, 0xf7, 0xf7, 0xf7])
    _ -> error "Invalid operand combination for test"

imul1 :: IsDataSize s => X86Op s -> CodeWriter()
imul1 src = case src of
    rmOp@(RegOp _) -> writeRmCode rmOp 5 (fmap (:[]) [0xf6, 0xf7, 0xf7, 0xf7])
    rmOp@(MemOp _) -> writeRmCode rmOp 5 (fmap (:[]) [0xf6, 0xf7, 0xf7, 0xf7])
    _ -> error "Invalid operand for imul1"

imul2 :: IsDataSize s => X86Op s -> X86Op s -> CodeWriter ()
imul2 dest src = case (dest, src) of
    (regOp@(RegOp _), rmOp@(RegOp _)) -> writeRmReg rmOp regOp (fmap ((0x0f:) . (:[])) [error "Invalid size for imul2", 0xaf, 0xaf, 0xaf])
    (regOp@(RegOp _), rmOp@(MemOp _)) -> writeRmReg rmOp regOp (fmap ((0x0f:) . (:[])) [error "Invalid size for imul2", 0xaf, 0xaf, 0xaf])
    _ -> error "Invalid operand for imul2"

imul3 :: IsDataSize s => X86Op s -> X86Op s -> X86Op s -> CodeWriter ()
imul3 dest src1 src2 = case (dest, src1, src2) of
    (regOp@(RegOp _), rmOp@(RegOp _), immOp@(ImmOp imm)) -> writeRmRegImmMul rmOp regOp imm
    (regOp@(RegOp _), rmOp@(MemOp _), immOp@(ImmOp imm)) -> writeRmRegImmMul rmOp regOp imm
    _ -> error "Invalid operand for imul3"
  where
    writeRmRegImmMul rmOp regOp imm
        | isImm8 imm = writeRmReg rmOp regOp (fmap (:[]) [error "Invalid size for imul3", 0x6b, 0x6b, 0x6b]) >> writeImm (Imm8 immVal)
        | otherwise  = writeRmReg rmOp regOp (fmap (:[]) [error "Invalid size for imul3", 0x6b, 0x6b, 0x6b]) >> writeImm imm
      where 
        immVal = extractImm imm

idiv :: IsDataSize s => X86Op s -> CodeWriter ()
idiv rmOp@(RegOp _) = writeRmCode rmOp 7 (fmap (:[]) [0xf6, 0xf7, 0xf7, 0xf7])
idiv rmOp@(MemOp _) = writeRmCode rmOp 7 (fmap (:[]) [0xf6, 0xf7, 0xf7, 0xf7])
idiv _              = error "Invalid operand for idiv"

cbw, cwde, cdqe, cwd, cdq, cqo :: CodeWriter ()
cbw = writeBytes [0x66, 0x98]
cwde = writeByte 0x98
cdqe = writeBytes [0x48, 0x98]
cwd = writeBytes [0x66, 0x99]
cdq = writeByte 0x99
cqo = writeBytes [0x48, 0x99]

data JumpCond
    = Overflow
    | NotOverflow
    | Below
    | AboveEqual
    | Equal
    | NotEqual
    | BelowEqual
    | Above
    | Signed
    | NotSigned
    | ParityEven
    | ParityOdd
    | Less
    | GreaterEqual
    | LessEqual
    | Greater

conditionVal :: Integral a => JumpCond -> a
conditionVal Overflow = 0
conditionVal NotOverflow = 1
conditionVal Below = 2
conditionVal AboveEqual = 3
conditionVal Equal = 4
conditionVal NotEqual = 5
conditionVal BelowEqual = 6
conditionVal Above = 7
conditionVal Signed = 8
conditionVal NotSigned = 9
conditionVal ParityEven = 10
conditionVal ParityOdd = 11
conditionVal Less = 12
conditionVal GreaterEqual = 13
conditionVal LessEqual = 14
conditionVal Greater = 15

jo, jno, jb, jae, je, jne, jbe, ja, js, jns, jp, jpo, jl, jge, jle, jg :: Int -> CodeWriter ()
jo = jcc Overflow
jno = jcc NotOverflow
jb = jcc Below
jae = jcc AboveEqual
je = jcc Equal
jne = jcc NotEqual
jbe = jcc BelowEqual
ja = jcc Above
js = jcc Signed
jns = jcc NotSigned
jp = jcc ParityEven
jpo = jcc ParityOdd
jl = jcc Less
jge = jcc GreaterEqual
jle = jcc LessEqual
jg = jcc Greater

label :: CodeWriter Int
label = asmIndex <$> get

getResult :: CodeWriter a -> [Word8]
getResult wr = appEndo (codeList $ execState wr (CodeState mempty 0)) []

showResult :: CodeWriter a -> String
showResult wr = unwords (map (until ((==2) . length) ('0':) . (`showHex` "")) (getResult wr))

instance Show f => Show (CodeWriter f) where
    show = showResult
