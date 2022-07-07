-- {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
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
    , blockDepth :: Int
    , loopLabel :: (String, String)
    } deriving Show

lookupStruct :: String -> GeneratorAction StructDefinition
lookupStruct structName = do
    structs <- structMap <$> get
    let struct = M.lookup structName structs
    return $ fromMaybe (error "Failed to lookup struct") struct

nameDepth :: String -> Int -> String
nameDepth name count = replicate count '$' ++ name

addDepth :: Int -> GeneratorAction ()
addDepth v = do
    GeneratorState lblCtr freeVars envMap structs depth lbls <- get 
    put $ GeneratorState lblCtr freeVars envMap structs (depth + v) lbls

setLabels :: (String, String) -> GeneratorAction (String, String)
setLabels newLbls = do
    GeneratorState lblCtr freeVars envMap structs depth oldLbls <- get 
    put $ GeneratorState lblCtr freeVars envMap structs depth newLbls
    return oldLbls

setEnvironment :: LocalEnv -> GeneratorAction ()
setEnvironment env = do
    GeneratorState lblCtr freeVars _ structs depth lbls <- get 
    put $ GeneratorState lblCtr freeVars env structs depth lbls

addLocal :: String -> DataType -> GeneratorAction ()
addLocal name dataType = do
    prependName <- nameDepth name <$> (blockDepth <$> get)
    addVar prependName (Local prependName $ getDNAType dataType)

addParam :: String -> DataType -> GeneratorAction ()
addParam name dataType = do
    prependName <- nameDepth name <$> (blockDepth <$> get)
    addVar prependName (Input prependName $ getDNAType dataType)

getLocal :: String -> GeneratorAction DNAVariable
getLocal name = do
    depth <- blockDepth <$> get
    let tryNames = map (nameDepth name) [depth,depth-1..1]
    map <- env <$> get
    let varName = head $ dropWhile (not . (`M.member` map)) tryNames
    let Just var = M.lookup varName map
    return var

getMemberOffset :: String -> StructDefinition -> Int
getMemberOffset name struct =
    let offsets = map (datatypeSize . fst) $ takeWhile ((/=name) . snd) (snd $ getStructDef struct)
    in  sum offsets

initialGeneratorState :: [StructDefinition] -> GeneratorState
initialGeneratorState defs = GeneratorState 0
                                  (M.empty, 0)
                                   M.empty
                                  (M.fromList (map (fst . getStructDef &&& id) defs))
                                   1
                                   ("", "")


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

addVar :: String -> DNAVariable -> GeneratorAction ()
addVar name var = do
    GeneratorState lblCtr freeVars envMap structs depth lbls <- get
    put $ GeneratorState lblCtr freeVars (M.insert name var envMap) structs depth lbls
getDNAType :: DataType -> DNAType
getDNAType (typeName, ptrList) =
    let baseTypeConstructor =
          if null ptrList || last ptrList > 0
            then parseDNAType typeName
            else Int64
        totalElems = product $ takeWhile (>0) ptrList
    in  baseTypeConstructor totalElems
  where
    parseDNAType :: String -> Int -> DNAType
    parseDNAType typename
        | typename == "char"  = Int8
        | typename == "short" = Int16
        | typename == "int"   = Int32
        | typename == "long"  = Int64
        | typename == "float" = Float
        | otherwise           = const InvalidType

getTempVar :: DNAType -> GeneratorAction DNAVariable
getTempVar typeName = do
    GeneratorState lblCtr (tmpList, tmpCount) envMap structs depth lbls <- get
    if M.member typeName tmpList
      then do
        let (Just freeVars) = M.lookup typeName tmpList
        if not $ null freeVars
          then do
            put $ GeneratorState lblCtr (M.insert typeName (tail freeVars) tmpList, tmpCount) envMap structs depth lbls
            return $ head freeVars
          else addNewTemp typeName
      else addNewTemp typeName
  where
    addNewTemp :: DNAType -> GeneratorAction DNAVariable
    addNewTemp typeName = do
        state (\(GeneratorState lblCtr (tmpMap, tmpCount) envMap structs depth lbls) ->
            let newVarName = 't' : show tmpCount
                newVar = Temp newVarName typeName
                newTmpList = M.findWithDefault [] typeName tmpMap
                newTmpMap = M.insert typeName newTmpList tmpMap
                newEnvMap = M.insert newVarName newVar envMap
            in (newVar, GeneratorState lblCtr (newTmpMap, tmpCount + 1) newEnvMap structs depth lbls))

freeTempVar :: DNAVariable -> GeneratorAction ()
freeTempVar var = do
    GeneratorState lblCtr (tmpList, tmpCount) envMap structs depth lbls <- get
    let result = insertVar var tmpList
    when
      (isJust result)
      (put $ GeneratorState lblCtr (fromJust result, tmpCount) envMap structs depth lbls)
  where
    insertVar :: DNAVariable -> TempFreeList -> Maybe TempFreeList
    insertVar var tmpMap = do
        let Temp _ varType = var
        freeList <- M.lookup varType tmpMap
        return $ M.insert varType (var:freeList) tmpMap

tryFreeOperand :: DNAOperand -> GeneratorAction ()
tryFreeOperand (Variable _ var) = case var of
    Temp _ _ -> freeTempVar var
    _ -> return ()
tryFreeOperand (MemoryRef _ var _ _) = case var of
    Temp _ _ -> freeTempVar var
    _ -> return ()
tryFreeOperand _ = return ()

createLabel :: GeneratorAction String
createLabel = do
    GeneratorState ctr temps env structs depth lbls <- get
    let newLbl = "l" ++ show ctr
    put $ GeneratorState (ctr + 1) temps env structs depth lbls
    return newLbl

resetState :: GeneratorAction ()
resetState = do
    GeneratorState lblCtr _ _ structs _ _ <- get
    put $ GeneratorState lblCtr (M.empty, 0) M.empty structs 1 ("", "")

generateProgram :: Program -> [DNAFunctionDefinition]
generateProgram (funcs, structs) =
    evalState (mapM generateFunction funcs) start
  where
    start = initialGeneratorState structs

generateFunction :: FunctionDefinition -> GeneratorAction DNAFunctionDefinition
generateFunction (FunctionDefinition rt name params root _) = do
    resetState
    forM_ params (uncurry $ flip addParam)
    (functionBody, _) <- generateIr root
    varsList <- map snd <$> (M.toList <$> (env <$> get))
    return (name, varsList, functionBody)

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
                    ++ [Label afterLbl], None)
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
                    ++ [Label elseLbl]
                    ++ falseBlock
                    ++ [Label afterLbl], None)
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
        afterLbl <- createLabel
        condLbl <- createLabel
        addDepth 1
        oldLbls <- setLabels (afterLbl, condLbl)
        (bodyBlock, _) <- generateIr body
        addDepth (-1)
        setLabels oldLbls
        let newBlock = ([Label condLbl]
                    ++ conditionBlock
                    ++ [Cmp resultOp (Immediate 0 (Int8 1)),
                        Jmp Eq afterLbl]
                    ++ bodyBlock
                    ++ [Jmp Always condLbl]
                    ++ [Label afterLbl], None)
        tryFreeOperand resultOp
        return newBlock
    generateIrHelper (ForNode init cond iter body) = do
        addDepth 1
        (initBlock, _) <- generateIr init -- This will leak
        (iterBlock, _) <- generateIr iter
        (conditionBlock, resultOp) <- generateIr cond
        afterLbl <- createLabel
        condLbl <- createLabel
        continueLbl <- createLabel
        oldLbls <- setLabels (afterLbl, continueLbl)
        (bodyBlock, _) <- generateIr body
        setLabels oldLbls
        addDepth (-1)
        let newBlock = (initBlock
                    ++ [Label condLbl]
                    ++  conditionBlock
                    ++ [Cmp resultOp (Immediate 0 (Int8 1))]
                    ++ [Jmp Eq afterLbl]
                    ++  bodyBlock
                    ++ [Label continueLbl]
                    ++  iterBlock
                    ++ [Jmp Always condLbl]
                    ++ [Label afterLbl], None)
        tryFreeOperand resultOp
        return newBlock
    generateIrHelper (DeclarationNode datatype id) = do
        localEnv <- env <$> get
        let dnaType = getDNAType datatype
            var = Local id dnaType

        setEnvironment (M.insert id var localEnv)
        return ([], None)
    generateIrHelper (DefinitionNode datatype id expr) = do
        (exprBlock, resultOp) <- generateIr expr
        localEnv <- env <$> get
        let dnaType = getDNAType datatype
            var = Local id dnaType
            varOp = Variable False var
        setEnvironment (M.insert id var localEnv)
        let newBlock = (exprBlock
                    ++ [Mov varOp resultOp], None)
        return newBlock
    generateIrHelper (BlockNode body) = do
        addDepth 1
        (bodyBlock, _) <- generateIr body
        addDepth (-1)
        return (bodyBlock, None)
    generateIrHelper ContinueNode = do
        GeneratorState lblCtr freeVars envMap structs depth (_, condLbl) <- get
        return ([Jmp Always condLbl], None)
    generateIrHelper BreakNode = do
        GeneratorState lblCtr freeVars envMap structs depth (afterLbl, _) <- get
        return ([Jmp Always afterLbl], None)
    generateIrHelper (ExprNode expr) = generateIrExpr expr
    -- fix this stuff above

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
                    ++ [Label equalLabel], eqVar)
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
                    ++ [Label equalLabel], neVar)
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
                    ++ [Label lessThanLabel], ltVar)
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
                    ++ [Label lessThanLabel], ltVar)
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
                    ++ [Label greaterThanLabel], gtVar)
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
                    ++ [Label greaterThanLabel], gtVar)
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
                    ++ [Label shortCircuit], resVar)
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
                    ++ [Label shortCircuit], resVar)
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
                          | otherwise -> []
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
        fixupTemp <- getTempVar $ Int64 1 -- Used to dereference a pointer on lhs
        struct <- lookupStruct $ fst $ typeOf lhs
        let fixedRhs = foldr (curry (first (fixupOperand fixupTemp struct structOp) >>> uncurry (++))) [] rhsBlock
        freeTempVar fixupTemp
        tryFreeOperand structOp
        return (lhsBlock ++ fixedRhs, valOp)
      where
        fixupOperand :: DNAVariable -> StructDefinition -> DNAOperand -> DNAInstruction -> [DNAInstruction]
        fixupOperand tempVar struct lhsOp (Mov dstOp (StructMemberFixup membName memType))
            | isPtr     = case lhsOp of
                Variable p v ->
                    if p
                      then [Mov dstOp (MemoryRef True v offset memType)]  -- (&v)->x
                      else [Mov dstOp (MemoryRef False v offset memType)] -- v->x
                MemoryRef p v offs dt ->
                    [Mov (Variable False tempVar) lhsOp, Mov dstOp (MemoryRef True tempVar offset memType)] -- (v[0])->x
                _ -> error "Bad lhs for member fixup"
            | otherwise = case lhsOp of
                Variable _ v            -> [Mov dstOp $ MemoryRef True v offset memType]
                MemoryRef p v offs dt   -> [Mov dstOp $ MemoryRef p v (offs + offset) memType]
                _                       -> error "Bad lhs for member fixup"
          where
            offset = getMemberOffset membName struct
        fixupOperand _ _ _ op = [op]