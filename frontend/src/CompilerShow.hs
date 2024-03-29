module CompilerShow
( showExprTree
, showSyntaxTree
, showDt
, showFunction
, showArrayConsts
, showGlobals
, showInst
) where

import CompilerShared
import Data.Functor.Compose
import Data.Fix
import Control.Arrow
import qualified Data.List as L
import qualified Data.Map as M

rewriteHead :: String -> [String] -> [String]
rewriteHead str (h:t) = (str ++ drop (length str) h):t
rewriteHead _   _   = []

showExprTreeLn :: Expr -> [String]
showExprTreeLn expr = case getCompose $ unFix expr of
    (annot, IdentifierNode id) -> ["Id " ++ id ++ " : " ++ show annot]
    (annot, StructMemberNode id) -> ["Member " ++ id ++ " : " ++ show annot]
    (annot, LiteralNode ct) -> ["Literal " ++ show ct ++ " : " ++ show annot]
    (annot, ArrayLiteralNode sub)
        | null sub  -> ["ArrayLit : " ++ show annot]
        | otherwise -> 
            let header = ["ArrayLit : " ++ show annot]
                children = (arr init &&& arr last) (map showExprTreeLn (reverse sub))
                childrenShift = (arr (map . map) ("│ " ++) *** arr (map ("  "++))) children
                markedHeads = (first (arr (fmap (rewriteHead "├─"))) >>> second (arr (rewriteHead "└─"))) childrenShift
                combined = arr (\(hds, tl) -> concat hds ++ tl) markedHeads
            in  header ++ combined
    (annot, FunctionCallNode name args)
        | null args -> ["Call " ++ name ++ " : " ++ show annot]
        | otherwise -> 
            let header = ["Call " ++ name ++ " : " ++ show annot]
                children = (arr init &&& arr last) (map showExprTreeLn (reverse args))
                childrenShift = (arr (map . map) ("│ " ++) *** arr (map ("  "++))) children
                markedHeads = (first (arr (fmap (rewriteHead "├─"))) >>> second (arr (rewriteHead "└─"))) childrenShift
                combined = arr (\(hds, tl) -> concat hds ++ tl) markedHeads
            in  header ++ combined
    (annot, ArrayIndexNode arr idx) ->
        let header = ["ArrIndex : " ++ show annot]
            arrLns = rewriteHead "├─" $ map ("│ " ++) $ showExprTreeLn arr
            idxLns = rewriteHead "└─" $ map ("  "++) $ showExprTreeLn idx
        in  header ++ (arrLns ++ idxLns)
    (annot, ParenthesisNode sub) ->
        let header = ["Paren : " ++ show annot]
            subLns = rewriteHead "└─" $ map ("  " ++) $ showExprTreeLn sub
        in  header ++ subLns
    (annot, BinaryOpNode op lhs rhs) ->
        let header = ["BinOp " ++ show op ++ " : " ++ show annot]
            rhsLns = rewriteHead "├─" $ map ("│ " ++) $ showExprTreeLn rhs
            lhsLns = rewriteHead "└─" $ map ("  "++) $ showExprTreeLn lhs
        in  header ++ (rhsLns ++ lhsLns)
    (annot, UnaryOpNode op sub) ->
        let header = ["UnOp : " ++ show op ++ " : " ++ show annot]
            subLns = rewriteHead "└─" $ map ("  " ++) $ showExprTreeLn sub
        in  header ++ subLns
    (annot, AssignmentNode op lhs rhs) ->
        let header = ["AssignOp " ++ show op ++ " : " ++ show annot]
            rhsLns = rewriteHead "├─" $ map ("│ " ++) $ showExprTreeLn rhs
            lhsLns = rewriteHead "└─" $ map ("  "++) $ showExprTreeLn lhs
        in  header ++ (rhsLns ++ lhsLns)
    (annot, PostfixOpNode op sub) ->
        let header = ["PostfixOp : " ++ show op ++ " : " ++ show annot]
            subLns = rewriteHead "└─" $ map ("  " ++) $ showExprTreeLn sub
        in  header ++ subLns
    (annot, MemberAccessNode op str mem) ->
        let header = ["MemberAccess " ++ show op ++ " : " ++ show annot]
            memLns = rewriteHead "├─" $ map ("│ " ++) $ showExprTreeLn mem
            strLns = rewriteHead "└─" $ map ("  "++) $ showExprTreeLn str
        in  header ++ (memLns ++ strLns)
    (annot, CastNode tp sub) ->
        let header = ["Cast (" ++ showDt tp ++ ") : " ++ show annot]
            subLns = rewriteHead "└─" $ map ("  " ++) $ showExprTreeLn sub
        in  header ++ subLns
    (annot, DynamicAllocationNode tp sub) ->
        let header = ["DynamicAlloc (" ++ showDt tp ++ ") : " ++ show annot]
            subLns = rewriteHead "└─" $ map ("  " ++) $ showExprTreeLn sub
        in  header ++ subLns
    (annot, DynamicFreeNode sub) ->
        let header = ["DynamicFree : " ++ show annot]
            subLns = rewriteHead "└─" $ map ("  " ++) $ showExprTreeLn sub
        in  header ++ subLns


showExprTree :: Expr -> String
showExprTree = unlines . showExprTreeLn

showSyntaxTree :: SyntaxNode -> String
showSyntaxTree = unlines . showTreeR
  where
    rewriteHead :: String -> [String] -> [String]
    rewriteHead str (h:t) = (str ++ drop (length str) h):t
    rewriteHead _   _   = []

    showTreeR :: SyntaxNode -> [String]
    showTreeR expr = case getCompose $ unFix expr of
        (annot, EmptyNode) -> ["Empty : " ++ show annot]
        (annot, SeqNode lhs rhs) ->
            let header = ["Seq : " ++ show annot]
                rhsLns = rewriteHead "├─" $ map ("│ " ++) $ showTreeR rhs
                lhsLns = rewriteHead "└─" $ map ("  "++) $ showTreeR lhs
            in  header ++ rhsLns ++ lhsLns
        (annot, WhileNode cond body) ->
            let header = ["While : " ++ show annot]
                bodyLns = rewriteHead "├─" $ map ("│ " ++) $ showTreeR body
                condLns = rewriteHead "└─" $ map ("  "++) $ showTreeR cond
            in  header ++ bodyLns ++ condLns
        (annot, ForNode init cond expr body or) ->
            let header = ["For : " ++ show annot]
                orLns   = rewriteHead "├─" $ map ("│ " ++) $ showTreeR or
                bodyLns = rewriteHead "├─" $ map ("│ " ++) $ showTreeR body
                exprLns = rewriteHead "├─" $ map ("│ " ++) $ showTreeR expr
                condLns = rewriteHead "├─" $ map ("│ " ++) $ showTreeR cond
                initLns = rewriteHead "└─" $ map ("  "++) $ showTreeR init
            in  header ++ bodyLns ++ exprLns ++ condLns ++ initLns
        (annot, IfNode cond body) ->
            let header = ["If : " ++ show annot]
                bodyLns = rewriteHead "├─" $ map ("│ " ++) $ showTreeR body
                condLns = rewriteHead "└─" $ map ("  "++) $ showTreeR cond
            in  header ++ bodyLns ++ condLns
        (annot, IfElseNode cond trueBody falseBody) ->
            let header = ["IfElse : " ++ show annot]
                falseLns = rewriteHead "├─" $ map ("│ " ++) $ showTreeR falseBody
                trueLns = rewriteHead "├─" $ map ("│ " ++) $ showTreeR trueBody
                condLns = rewriteHead "└─" $ map ("  "++) $ showTreeR cond
            in  header ++ falseLns ++ trueLns ++ condLns
        (annot, ReturnNode sub) ->
            let header = ["Return : " ++ show annot]
                subLns = rewriteHead "└─" $ map ("  "++) $ showTreeR sub
            in  header ++ subLns
        (annot, ContinueNode) -> ["Continue : " ++ show annot]
        (annot, BreakNode) -> ["Break : " ++ show annot]
        (annot, BlockNode block) ->
            let header = ["Blocks : " ++ show annot]
                subLns = rewriteHead "└─" $ map ("  "++) $ showTreeR block
            in  header ++ subLns
        (annot, DeclarationNode dt id) -> ["Declaration " ++ showDt dt ++ " " ++ show id ++ " : " ++ show annot]
        (annot, ExprNode e) -> showExprTreeLn e
        (annot, PrintNode e) ->
            let header = ["Print : " ++ show annot]
                subLns = rewriteHead "└─" $ map ("  "++) $ showTreeR e
            in  header ++ subLns

showDeclList :: String -> DeclList -> String
showDeclList inter = L.intercalate inter . map (\ (t, n) -> showDt t ++ (' ':n))

instance Show ExprInfo where
    show (ExprInfo tp hd sl) = showDt tp ++ " (" ++ show hd ++ ") @ " ++ show sl

instance Show FunctionDefinition where
    show (FunctionDefinition rt name params root locs) =
        showDt rt ++ (' ':name ++ ('(':paramsStr ++ (")\n" ++ showSyntaxTree root)))
      where
        paramsStr = showDeclList ", " params

-- instance Show StructDefinition where
--     show (name, members) =
--         "struct " ++ (name ++ (" {\n  " ++ (membersStr ++ "}")))
--       where
--         membersStr = showDeclList ";\n  " members

instance Show Token where
    show (Identifier id) = "id '" ++ id ++ "'"
    show (Constant ct) = "constant '" ++ show ct ++ "'"
    show (Operator op) = op
    show (Control cnt) = cnt
    show (Punctuation p) = p
    show (Keyword kw) = kw
    show Eof = "eof"
    show (Invalid _ UntermString) = "Unterminated string"
    show (Invalid s UnknownChar) = "Unknown character " ++ s
    show (Invalid s BadOperator) = "Invalid operator " ++ s
    show (Invalid s BadCharStr) = "Invalid character literal " ++ s

showDt :: DataType -> String
showDt (dataTypeName, ptrList) = dataTypeName ++ concatMap (\x -> if x > 0 then "[" ++ show x ++ "]" else "*") ptrList

instance Show DNAType where
    show (Int8 c) = if c == 1 then "int8" else "int8 " ++ show c
    show (Int16 c) = if c == 1 then "int16" else "int16 " ++ show c
    show (Int32 c) = if c == 1 then "int32" else "int32 " ++ show c
    show (Int64 c) = if c == 1 then "int64" else "int64 " ++ show c
    show (Float c) = if c == 1 then "float" else "float " ++ show c
    show _         = "(Invalid Type)"
    

instance Show DNAOperand where
    show (Variable isRef var) = varWithRef
      where
        varWithRef
            | isRef = '&':show var
            | otherwise = show var
    show (MemoryRef isRef var off tp)
        | off > 0   = "[" ++ varWithRef ++ " + " ++ show off ++ "]::" ++ show tp
        | otherwise = "[" ++ varWithRef ++ "]::" ++ show tp
      where
        varWithRef
            | isRef = '&':show var
            | otherwise = show var
    show (Immediate val tp) = show (round val) ++ "::" ++ show tp
    show (GlobalArr nm _) = '%':nm
    show None = "$nil"

instance Show JmpCondition where
    show Always = "mp"
    show Eq = "eq"
    show Ne = "ne"
    show Gt = "gt"
    show Lt = "lt"
    show Ge = "ge"
    show Le = "le"

instance Show DNAVariable where
    show (Temp name tp)  = name
    show (Input name tp) = name
    show (Local name tp) = name

showVarHdr :: DNAVariable -> [Char]
showVarHdr (Temp name tp)  = "temp " ++ name ++ ' ':show tp
showVarHdr (Input name tp) = "in " ++ name ++ ' ':show tp
showVarHdr (Local name tp) = "local " ++ name ++ ' ':show tp

showInst :: (Show a, Show b) => DNAInstructionF a b -> String
showInst (Mov dst src) = "mov" ++ (' ':show dst) ++ (' ':show src)
showInst (Add dst src1 src2) = "add" ++ (' ':show dst) ++ (' ':show src1) ++ (' ':show src2)
showInst (Sub dst src1 src2) = "sub" ++ (' ':show dst) ++ (' ':show src1) ++ (' ':show src2)
showInst (Mul dst src1 src2) = "mul" ++ (' ':show dst) ++ (' ':show src1) ++ (' ':show src2)
showInst (Div dst src1 src2) = "div" ++ (' ':show dst) ++ (' ':show src1) ++ (' ':show src2)
showInst (Mod dst src1 src2) = "mod" ++ (' ':show dst) ++ (' ':show src1) ++ (' ':show src2)
showInst (Cmp lhs rhs) = "cmp" ++ (' ':show lhs) ++ (' ':show rhs)
showInst (Jmp cond lbl) = "j" ++ show cond ++ (' ':lbl)
showInst (Param op tp) = "param" ++ (' ':show op) ++ (' ':show tp)
showInst (Call name output) = "call" ++ (' ':name) ++ (' ':show output)
showInst (ReturnVal value) = "return" ++ (' ':show value)
showInst ReturnVoid = "return $nil"
showInst (ArrayCopy op1 op2 count) = "arraycopy" ++ (' ':show op1) ++ (' ':show op2) ++ (' ':show count)
showInst (IntToFloat op1 op2) = "inttofloat" ++ (' ':show op1) ++ (' ':show op2)
showInst (FloatToInt op1 op2) = "floattoint" ++ (' ':show op1) ++ (' ':show op2)
showInst (Label lbl) = ".label" ++ (' ':lbl)
showInst (Print op) = "print" ++ (' ':show op)
showInst (Allocate op count) = "dynalloc" ++ (' ':show op) ++ (' ':show count)
showInst (Deallocate op) = "dynfree" ++ (' ':show op)

showFunction :: DNAFunctionDefinition -> String
showFunction (name, vars, body) =
    let header = [".sub " ++ name]
        var = map showVarHdr vars
        bod = map showInst body
        things = [header, var, [".endframe", ".label " ++ name], bod, [".endsub"]]
    in unlines $ concat things

showArrayConsts :: M.Map String (DNAType, [Rational]) -> String
showArrayConsts m = concatMap showGlobal $ M.toList m
  where
    showGlobal :: (String, (DNAType, [Rational])) -> String
    showGlobal (name, (tp, vals)) =
        let header = [".array " ++ name ++ " " ++ show tp]
            vals = L.intercalate "," convertedVals
        in  unlines $ header ++ [vals] ++ [".endarray"]
      where
        convertedVals = case tp of
            Int8 _  -> map (show . round) vals
            Int16 _ -> map (show . round) vals
            Int32 _ -> map (show . round) vals
            Int64 _ -> map (show . round) vals
            Float _ -> map (show . realToFrac) vals
            _       -> error "Invalid type for array"

showGlobals :: M.Map String DNAVariable -> String
showGlobals m =
    let gvars = map snd $ M.toList m 
        varsStr = map (\(Local name tp) -> ".glob " ++ name ++ ' ':show tp) gvars
    in unlines varsStr