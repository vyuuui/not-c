-- {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module Generator where

import CompilerShared
import Control.Arrow
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State.Lazy ( runState, state, put, get, State )
import Data.Fix
import Data.Functor.Compose
import Data.Maybe
import Parser
import Validator
import qualified Data.Char as C
import qualified Data.List as L
import qualified Data.Map as M
import Debug.Trace

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
type GlobalsMap = M.Map String (DNAType, [Rational])

data GeneratorState = GeneratorState
    { labelIdx :: Int
    , freeVars :: TempVarList
    , env :: LocalEnv
    , structMap :: StructMap
    , blockDepth :: Int
    , loopLabel :: (String, String)
    , accessCtx :: AccessContext
    , globalEnv :: GlobalsMap
    } deriving Show

data AccessContext = AccessContext
    { sourceStruct :: StructDefinition
    , fromOperand :: DNAOperand
    , doDeref :: Bool
    } deriving Show

addGlobal :: (DNAType, [Rational]) -> GeneratorAction DNAOperand
addGlobal arr@(arrDt, arrVal) = do
    GeneratorState lblCtr freeVars envMap structs depth lbls aCtx gEnvMap <- get 
    let name = "glob" ++ show (M.size gEnvMap)
    put $ GeneratorState lblCtr freeVars envMap structs depth lbls aCtx (M.insert name arr gEnvMap)
    return $ GlobalArr name arrDt

lookupStruct :: String -> GeneratorAction StructDefinition
lookupStruct structName = do
    structs <- structMap <$> get
    let struct = M.lookup structName structs
    return $ fromMaybe (error "Failed to lookup struct") struct

nameDepth :: String -> Int -> String
nameDepth name count = replicate count '_' ++ name

addDepth :: Int -> GeneratorAction ()
addDepth v = do
    GeneratorState lblCtr freeVars envMap structs depth lbls aCtx gEnvMap <- get 
    put $ GeneratorState lblCtr freeVars envMap structs (depth + v) lbls aCtx gEnvMap

setLabels :: (String, String) -> GeneratorAction (String, String)
setLabels newLbls = do
    GeneratorState lblCtr freeVars envMap structs depth oldLbls aCtx gEnvMap <- get 
    put $ GeneratorState lblCtr freeVars envMap structs depth newLbls aCtx gEnvMap
    return oldLbls

setEnvironment :: LocalEnv -> GeneratorAction ()
setEnvironment env = do
    GeneratorState lblCtr freeVars _ structs depth lbls aCtx gEnvMap <- get 
    put $ GeneratorState lblCtr freeVars env structs depth lbls aCtx gEnvMap

setActiveContext :: AccessContext -> GeneratorAction AccessContext
setActiveContext nCtx = do
    GeneratorState lblCtr freeVars env structs depth lbls aCtx gEnvMap <- get 
    put $ GeneratorState lblCtr freeVars env structs depth lbls nCtx gEnvMap
    return aCtx

addLocal :: String -> DataType -> GeneratorAction ()
addLocal name dataType = do
    structs <- structMap <$> get
    prependName <- nameDepth name <$> (blockDepth <$> get)
    addVar prependName (Local prependName $ getDNAType structs dataType)

addParam :: String -> DataType -> GeneratorAction ()
addParam name dataType = do
    structs <- structMap <$> get
    let prependName = nameDepth name 1
    addVar prependName (Input prependName $ getDNAType structs dataType)

getLocal :: String -> GeneratorAction DNAVariable
getLocal name = do
    depth <- blockDepth <$> get
    let tryNames = map (nameDepth name) [depth,depth-1..1]
    map <- env <$> get
    let varName = head $ dropWhile (not . (`M.member` map)) tryNames
    let Just var = M.lookup varName map
    return var

sizeofStruct :: StructMap -> String -> Int
sizeofStruct structs name = case M.lookup name structs of
    Just (_, members) -> sum $ map (datatypeSize structs . fst) members
    Nothing           -> 0

basetypeSize :: StructMap -> String -> Int
basetypeSize structs typeName
    | typeName == "bool"  = 1
    | typeName == "char"  = 1
    | typeName == "short" = 2
    | typeName == "int"   = 4
    | typeName == "long"  = 8
    | typeName == "float" = 8
    | otherwise           = sizeofStruct structs typeName 

datatypeSize :: StructMap -> DataType -> Int
datatypeSize structs tp@(typeName, ptrList)
    | isArrayType tp   = arraySize
    | isPointerType tp = 8
    | otherwise        = basetypeSize structs typeName
  where
    (arrPart, ptrPart) = break (==0) ptrList
    arraySize :: Int
    arraySize = L.foldl' (*) (datatypeSize structs (typeName, ptrPart)) (takeWhile (>0) ptrList)

getMemberOffset :: StructMap -> String -> StructDefinition -> Int
getMemberOffset structs name struct =
    let offsets = map (datatypeSize structs . fst) $ takeWhile ((/=name) . snd) (snd struct)
    in  sum offsets

initialGeneratorState :: [StructDefinition] -> GeneratorState
initialGeneratorState defs = GeneratorState 0
                                  (M.empty, 0)
                                   M.empty
                                  (M.fromList (map (fst &&& id) defs))
                                   1
                                  ("", "")
                                  (AccessContext ("", []) None False)
                                  M.empty

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
getOperandType (GlobalArr _ tp) = tp
getOperandType _                = error "getOperandType on Operand with 'None', this should not have passed through the validator"

addVar :: String -> DNAVariable -> GeneratorAction ()
addVar name var = do
    GeneratorState lblCtr freeVars envMap structs depth lbls aCtx gEnvMap <- get
    put $ GeneratorState lblCtr freeVars (M.insert name var envMap) structs depth lbls aCtx gEnvMap
getDNAType :: StructMap -> DataType -> DNAType
getDNAType structs (typeName, ptrList)
    | null ptrList && M.member typeName structs = Int8 (sizeofStruct structs typeName)
    | otherwise =
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
        | typename == "bool"  = Int8
        | otherwise           = const InvalidType
getDNATypeForOperand :: StructMap -> DataType -> DNAType
getDNATypeForOperand structs dt@(typeName, ptrList)
    | null ptrList && M.member typeName structs = Int8 1
    | isArrayType dt = getDNATypeForOperand structs (typeName, dropWhile (>0) ptrList)
    | otherwise = getDNAType structs dt

getTempVar :: DNAType -> GeneratorAction DNAVariable
getTempVar typeName = do
    GeneratorState lblCtr (tmpList, tmpCount) envMap structs depth lbls aCtx gEnvMap <- get
    if M.member typeName tmpList
      then do
        let (Just freeVars) = M.lookup typeName tmpList
        if not $ null freeVars
          then do
            put $ GeneratorState lblCtr (M.insert typeName (tail freeVars) tmpList, tmpCount) envMap structs depth lbls aCtx gEnvMap
            return $ head freeVars
          else addNewTemp typeName
      else addNewTemp typeName
  where
    addNewTemp :: DNAType -> GeneratorAction DNAVariable
    addNewTemp typeName = do
        state (\(GeneratorState lblCtr (tmpMap, tmpCount) envMap structs depth lbls aCtx gEnvMap) ->
            let newVarName = 't' : show tmpCount
                newVar = Temp newVarName typeName
                newTmpList = M.findWithDefault [] typeName tmpMap
                newTmpMap = M.insert typeName newTmpList tmpMap
                newEnvMap = M.insert newVarName newVar envMap
            in (newVar, GeneratorState lblCtr (newTmpMap, tmpCount + 1) newEnvMap structs depth lbls aCtx gEnvMap))

freeTempVar :: DNAVariable -> GeneratorAction ()
freeTempVar var = do
    GeneratorState lblCtr (tmpList, tmpCount) envMap structs depth lbls aCtx gEnvMap <- get
    let result = insertVar var tmpList
    when
      (isJust result)
      (put $ GeneratorState lblCtr (fromJust result, tmpCount) envMap structs depth lbls aCtx gEnvMap)
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
    GeneratorState ctr temps env structs depth lbls aCtx gEnvMap <- get
    let newLbl = "l" ++ show ctr
    put $ GeneratorState (ctr + 1) temps env structs depth lbls aCtx gEnvMap
    return newLbl

resetState :: GeneratorAction ()
resetState = do
    GeneratorState lblCtr _ _ structs _ _ _ globs <- get
    put $ GeneratorState lblCtr (M.empty, 0) M.empty structs 1 ("", "") (AccessContext ("", []) None False) globs

generateProgram :: Program -> ([DNAFunctionDefinition], GlobalsMap)
generateProgram (funcs, structs) =
    (resultVal, globalEnv resultState)
  where
    start = initialGeneratorState structs
    (resultVal, resultState) = runState (mapM generateFunction funcs) start

generateFunction :: FunctionDefinition -> GeneratorAction DNAFunctionDefinition
generateFunction (FunctionDefinition rt name params root _) = do
    resetState
    forM_ params (uncurry $ flip addParam)
    functionBody <- generateIrSkipBlock root
    varsList <- map snd <$> (M.toList <$> (env <$> get))
    return (name, varsList, functionBody)

generateIr :: SyntaxNode -> GeneratorAction DNABlock
generateIr = generateIrHelper . snd . getCompose . unFix
  where
    generateIrHelper (IfNode condition block) = do
        (conditionBlock, resultOp) <- generateIrSyntaxExpr condition
        bodyBlock <- generateIr block
        afterLbl <- createLabel
        let newBlock = conditionBlock
                  ++ [ Cmp resultOp (Immediate 0 (Int8 1))
                     , Jmp Eq afterLbl
                ] ++   bodyBlock
                  ++ [ Label afterLbl
                ]
        tryFreeOperand resultOp
        return newBlock
    generateIrHelper (IfElseNode condition trueBody falseBody) = do
        (conditionBlock, resultOp) <- generateIrSyntaxExpr condition
        trueBlock <- generateIr trueBody
        falseBlock <- generateIr falseBody
        afterLbl <- createLabel
        elseLbl <- createLabel
        let newBlock = conditionBlock
                  ++ [ Cmp resultOp (Immediate 0 (Int8 1))
                     , Jmp Eq elseLbl
                ] ++   trueBlock
                  ++ [ Jmp Always afterLbl
                     , Label elseLbl
                ] ++   falseBlock
                  ++ [ Label afterLbl
                ]
        tryFreeOperand resultOp
        return newBlock
    generateIrHelper (ReturnNode expr) = do
        if isEmptyNode expr
          then return [ReturnVoid]
          else do
            (exprBlock, resultOp) <- generateIrSyntaxExpr expr
            tryFreeOperand resultOp
            return $ exprBlock ++ [ReturnVal resultOp]
    generateIrHelper EmptyNode = return []
    generateIrHelper (SeqNode first second) = do
        statement <- generateIr first
        statementTwo <- generateIr second
        return $ statement ++ statementTwo
    generateIrHelper (WhileNode cond body) = do
        (conditionBlock, resultOp) <- generateIrSyntaxExpr cond
        afterLbl <- createLabel
        condLbl <- createLabel
        addDepth 1
        oldLbls <- setLabels (afterLbl, condLbl)
        bodyBlock <- generateIr body
        addDepth (-1)
        setLabels oldLbls
        let newBlock = [ Label condLbl
                  ] ++   conditionBlock
                    ++ [ Cmp resultOp (Immediate 0 (Int8 1))
                       , Jmp Eq afterLbl
                  ] ++   bodyBlock
                    ++ [ Jmp Always condLbl
                       , Label afterLbl
                  ]
        tryFreeOperand resultOp
        return newBlock
    generateIrHelper (ForNode init cond iter body) = do
        addDepth 1
        initBlock <- generateIr init -- This will leak
        iterBlock <- generateIr iter
        (conditionBlock, resultOp) <- generateIrSyntaxExpr cond
        afterLbl <- createLabel
        condLbl <- createLabel
        continueLbl <- createLabel
        oldLbls <- setLabels (afterLbl, continueLbl)
        -- Because we add depth for the iterator, we skip the env-push
        bodyBlock <- generateIrSkipBlock body
        setLabels oldLbls
        addDepth (-1)
        let newBlock = initBlock
                  ++ [ Label condLbl
                ] ++   conditionBlock
                  ++ [ Cmp resultOp (Immediate 0 (Int8 1))
                     , Jmp Eq afterLbl
                ] ++   bodyBlock
                  ++ [ Label continueLbl
                ] ++   iterBlock
                  ++ [ Jmp Always condLbl
                     , Label afterLbl
                ]
        tryFreeOperand resultOp
        return newBlock
    generateIrHelper (DeclarationNode dataType id) = do
        addLocal id dataType
        return []
    generateIrHelper (BlockNode body) = do
        addDepth 1
        bodyBlock <- generateIr body
        addDepth (-1)
        return bodyBlock
    generateIrHelper ContinueNode = do
        GeneratorState _ _ _ _ _ (_, condLbl) _ _ <- get
        return [Jmp Always condLbl]
    generateIrHelper BreakNode = do
        GeneratorState _ _ _ _ _ (afterLbl, _) _ _ <- get
        return [Jmp Always afterLbl]
    -- In the case of ignoring the result, we shouldn't leak temps here
    generateIrHelper (ExprNode expr) = do
        (block, result) <- generateIrExpr expr
        tryFreeOperand result
        return block
    generateIrHelper (PrintNode expr) = do
        (exprBlock, resultOp) <- generateIrSyntaxExpr expr
        tryFreeOperand resultOp
        return $ exprBlock ++ [Print resultOp]

generateIrSkipBlock :: SyntaxNode -> GeneratorAction DNABlock
generateIrSkipBlock node = case snd $ getCompose $ unFix node of
    BlockNode sub -> generateIr sub
    _             -> error "Attempted generateIrSkipBlock on non-block node"

generateIrSyntaxExpr :: SyntaxNode -> GeneratorAction (DNABlock, DNAOperand)
generateIrSyntaxExpr node = case snd $ getCompose $ unFix node of
    ExprNode expr -> generateIrExpr expr
    _             -> error "Attempted generateIrSyntaxExpr on non-expr node"

generateIrExpr :: Expr -> GeneratorAction (DNABlock, DNAOperand)
generateIrExpr = uncurry generateIrExprHelper . first dataType . getCompose . unFix
  where
    generateIrExprHelper :: DataType -> ExprF Expr -> GeneratorAction (DNABlock, DNAOperand)
    generateIrExprHelper exprType (BinaryOpNode Addition left right)
        | isPointerType $ typeOf left = ptrIntSum left right False
        | isPointerType $ typeOf right = ptrIntSum right left True
        | otherwise = do
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
      where
        ptrIntSum ptrSide intSide swapOrder = do
            structs <- structMap <$> get
            (ptrBlock, ptrOp) <- generateIrExpr ptrSide
            (intBlock, intOp) <- generateIrExpr intSide
            sum <- getTempVar $ Int64 1
            let subBlock = if swapOrder
                             then intBlock ++ ptrBlock
                             else ptrBlock ++ intBlock
                newBlock = (subBlock
                        ++ [Mul (opVar sum) intOp (Immediate (toRational mulAmount) (Int64 1)),
                            Add (opVar sum) (opVar sum) ptrOp], opVar sum)
                  where
                    mulAmount = datatypeSize structs $ second (drop 1) (typeOf ptrSide)
            tryFreeOperand ptrOp
            tryFreeOperand intOp
            return newBlock
    generateIrExprHelper exprType (BinaryOpNode Subtraction left right)
        | isPointerType (typeOf left) && isPointerType (typeOf right) = do
            structs <- structMap <$> get
            (leftBlock, resultOp) <- generateIrExpr left
            (rightBlock, resultOp2) <- generateIrExpr right
            diff <- getTempVar $ Int64 1
            let newBlock = (leftBlock
                        ++  rightBlock
                        ++ [Sub (opVar diff) resultOp resultOp2,
                            Div (opVar diff) (opVar diff) (Immediate (toRational divAmount) (Int64 1))], opVar diff)
                  where
                    divAmount = datatypeSize structs $ second (drop 1) (typeOf left)
            tryFreeOperand resultOp
            tryFreeOperand resultOp2
            return newBlock
        | isPointerType $ typeOf left = do
            structs <- structMap <$> get
            (ptrBlock, ptrOp) <- generateIrExpr left
            (intBlock, intOp) <- generateIrExpr right
            diff <- getTempVar $ Int64 1
            let newBlock = (ptrBlock
                        ++  intBlock
                        ++ [Mul (opVar diff) intOp (Immediate (toRational mulAmount) (Int64 1)),
                            Sub (opVar diff) ptrOp (opVar diff)], opVar diff)
                  where
                    mulAmount = datatypeSize structs $ second (drop 1) (typeOf left)
            tryFreeOperand ptrOp
            tryFreeOperand intOp
            return newBlock
        | otherwise = do
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
                    ++ [Mov (opVar ptr) resultOp], ptrDeref)
        tryFreeOperand resultOp
        return newBlock
    generateIrExprHelper exprType node@(UnaryOpNode op expr)
        | op == PrefixInc = generateIrExpr $ annotExprType exprType (AssignmentNode PlusEq expr literal)
        | op == PrefixDec = generateIrExpr $ annotExprType exprType (AssignmentNode MinusEq expr literal)
        | otherwise       = error "Unhandled unary op"
      where
        literal
            | isIntegralType exprType = annotExprType longType (LiteralNode (IntConstant 1))
            | isPointerType exprType  = annotExprType longType (LiteralNode (IntConstant 1))
            | otherwise = annotExprType floatType (LiteralNode (FloatConstant 1))
    generateIrExprHelper exprType node@(PostfixOpNode op expr)
        | op == PostInc = generatePostfix True
        | op == PostDec = generatePostfix False
        | otherwise     = error "Unhandled postfix operator"
      where
        generatePostfix adds = do
            (subBlock, resultOp) <- generateIrExpr expr
            beforeChange <- getTempVar (getOperandType resultOp)
            let imm = Immediate (toRational 1) (getOperandType resultOp)
            assnBody <- generateAssign (if adds then PlusEq else MinusEq) resultOp imm exprType exprType
            return (subBlock ++ [Mov (opVar beforeChange) resultOp] ++ assnBody, opVar beforeChange)
    generateIrExprHelper exprType node@(IdentifierNode name) = do
        env <- env <$> get
        var <- getLocal name
        return ([], Variable (isArrayType exprType) var)
    generateIrExprHelper exprType node@(LiteralNode lit) = do
        case lit of
            IntConstant v    -> return ([], Immediate (toRational v) $ Int64 1)
            FloatConstant v  -> return ([], Immediate (toRational v) $ Float 1)
            BoolConstant v   -> return ([], Immediate (if v then 1 else 0) $ Int8 1)
            CharConstant v   -> return ([], Immediate (toRational $ C.ord v) $ Int8 1)
            StringConstant v -> do
                let flatten = map (toRational . C.ord) v ++ [0]
                newGlob <- addGlobal (Int8 (length flatten), flatten)
                return ([], newGlob)
            NullConstant     -> return ([], Immediate (toRational 0) $ Int64 1)
    generateIrExprHelper exprType node@(ArrayLiteralNode lit) = do
        structs <- structMap <$> get
        let flatten = foldFix (combineArray . snd . getCompose) (annotExprEmpty node)
            arrType = getDNAType structs (fst exprType, [])
        newGlob <- addGlobal (arrType, flatten)
        return ([], newGlob)
      where
        combineArray :: ExprF [Rational] -> [Rational]
        combineArray (ArrayLiteralNode sublits)       = join sublits
        combineArray (LiteralNode (IntConstant i))    = [toRational i]
        combineArray (LiteralNode (FloatConstant f))  = [toRational f]
        combineArray (LiteralNode (BoolConstant b))   = [toRational (if b then 1 else 0)] 
        combineArray (LiteralNode (StringConstant s)) = map (toRational . C.ord) s
        combineArray _                                = error "Can't generate for non-literal or non-array"
    generateIrExprHelper exprType node@(FunctionCallNode name args) = do
        instList <- mapM generateIrExpr args
        let paramInsts = zipWith ($) (map (Param . snd) instList) (map (exprToDNA . typeOf) args)
        let argBlocks  = concatMap fst instList
        returnOp <- if exprType == voidType
                      then return None
                      else opVar <$> getTempVar (exprToDNA exprType)
        let newBlock = (argBlocks
                     ++ paramInsts
                     ++ [Call name returnOp], returnOp)
        mapM_ (tryFreeOperand . snd) instList
        return newBlock
    generateIrExprHelper exprType node@(ArrayIndexNode arr idx) = do
        structs <- structMap <$> get
        (arrBlock, resultOp) <- generateIrExpr arr
        (idxBlock, resultOp2) <- generateIrExpr idx
        ptr <- getTempVar (Int64 1)
        idxResult <- getTempVar (Int64 1)
        let ptrDerefType = exprToDNA exprType
            ptrDeref = MemoryRef False ptr 0 ptrDerefType
            ptrRaw = opVar ptr
            idxRaw = opVar idxResult
        let newIdxBlock = idxBlock ++ [Mul idxRaw resultOp2 (Immediate (toRational mulSize) (Int64 1))]
             where mulSize = datatypeSize structs $ second (drop 1) (typeOf arr)
        let newBlock = (arrBlock
                     ++ newIdxBlock
                     ++ [Add ptrRaw resultOp idxRaw], if isArrayType exprType then ptrRaw else ptrDeref)
        tryFreeOperand resultOp
        tryFreeOperand resultOp2
        freeTempVar idxResult
        return newBlock
    generateIrExprHelper exprType node@(ParenthesisNode sub) = generateIrExpr sub
    generateIrExprHelper exprType node@(AssignmentNode op lhs rhs) = do
        (rightBlock, resultOp2) <- generateIrExpr rhs
        (leftBlock, resultOp) <- generateIrExpr lhs
        assnBlock <- generateAssign op resultOp resultOp2 exprType (typeOf rhs)
        tryFreeOperand resultOp2
        return (rightBlock ++ leftBlock ++ assnBlock, resultOp)
    generateIrExprHelper exprType node@(CastNode toType expr) = do
        let castType = exprToDNA toType
        (exprBlock, resultOp) <- generateIrExpr expr
        let resultOpType = getOperandType resultOp
        outVar <- getTempVar castType
        let outOperand = opVar outVar
        let castInst = if | resultOpType == Float 1 && castType /= Float 1 -> [FloatToInt outOperand resultOp]
                          | resultOpType /= Float 1 && castType == Float 1 -> [IntToFloat outOperand resultOp]
                          | resultOpType /= Float 1 && castType /= Float 1 -> [Mov outOperand resultOp]
                          | otherwise -> []
        let newBlock = (exprBlock
                     ++ castInst, outOperand)
        tryFreeOperand resultOp
        return newBlock
    generateIrExprHelper exprType node@(StructMemberNode id) = do
        structs <- structMap <$> get
        (AccessContext struct srcOp doDeref) <- accessCtx <$> get
        let memberOffset = getMemberOffset structs id struct
            dnaType = getDNATypeForOperand structs exprType
        if doDeref
          then case srcOp of -- a->b
              Variable isRef var         -> return ([], MemoryRef isRef var memberOffset dnaType)
              MemoryRef isRef var offs _ -> do
                scratchVar <- getTempVar $ Int64 1
                tryFreeOperand srcOp
                return ([Mov (opVar scratchVar) srcOp], MemoryRef False scratchVar memberOffset dnaType)
              _                          -> error "Invalid source operand for struct access"
          else case srcOp of -- a.b
              Variable _ var             -> return ([], MemoryRef True var memberOffset dnaType)
              MemoryRef isRef var offs _ -> return ([], MemoryRef isRef var (offs + memberOffset) dnaType)
              _                          -> error "Invalid source operand for struct access"
    generateIrExprHelper exprType node@(MemberAccessNode isPtr lhs rhs) = do
        structs <- structMap <$> get
        struct <- lookupStruct $ fst $ typeOf lhs
        (lhsBlock, structOp) <- generateIrExpr lhs

        oldCtx <- setActiveContext $ AccessContext struct structOp isPtr
        (rhsBlock, valOp) <- generateIrExpr rhs
        setActiveContext oldCtx

        tryFreeOperand structOp
        return (lhsBlock ++ rhsBlock, valOp)

generateAssign :: AssignmentOp -> DNAOperand -> DNAOperand -> DataType -> DataType -> GeneratorAction DNABlock
generateAssign op to from toType fromType
    | isPointerType toType = do
        structs <- structMap <$> get
        temp <- getTempVar $ Int64 1
        let copySize = datatypeSize structs fromType
            copyOp = if isArrayType toType
                then ArrayCopy to tempVar copySize
                else Mov to tempVar
            tempVar = opVar temp
            assnInsts = case op of
                NoOp     
                    | isArrayType toType -> [ArrayCopy to from copySize]
                    | otherwise -> [Mov to from]
                PlusEq  -> [Mul tempVar from (Immediate (toRational copySize) (Int64 1)),
                            Add tempVar to tempVar,
                            copyOp]
                MinusEq -> [Mul tempVar from (Immediate (toRational copySize) (Int64 1)),
                            Sub tempVar to tempVar,
                            copyOp]
                _       -> error "Invalid pointer/assignop provided to generator"
        freeTempVar temp
        return assnInsts
    | otherwise = do
        return $ case op of
            NoOp -> [Mov to from]
            PlusEq -> [Add to to from]
            MinusEq -> [Sub to to from]
            MulEq -> [Mul to to from]
            DivEq -> [Div to to from]
            ModEq -> [Mod to to from]
