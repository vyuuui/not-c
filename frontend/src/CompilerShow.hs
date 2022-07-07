module CompilerShow
( showExprTree
, showSyntaxTree
, showDt
, showFunction
) where

import CompilerShared
import Data.Functor.Compose
import Data.Fix
import Control.Arrow
import qualified Data.List as L

rewriteHead :: String -> [String] -> [String]
rewriteHead str (h:t) = (str ++ drop (length str) h):t
rewriteHead _   _   = []

showExprTreeLn :: Expr -> [String]
showExprTreeLn expr = case getCompose $ unFix expr of
    (annot, IdentifierNode id) -> ["Id " ++ id ++ " : " ++ show annot]
    (annot, StructMemberNode id) -> ["Member " ++ id ++ " : " ++ show annot]
    (annot, LiteralNode ct) -> ["Literal " ++ show ct ++ " : " ++ show annot]
    (annot, FunctionCallNode name args) ->
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
    (annot, MemberAccessNode op str mem) ->
        let header = ["MemberAccess " ++ show op ++ " : " ++ show annot]
            memLns = rewriteHead "├─" $ map ("│ " ++) $ showExprTreeLn mem
            strLns = rewriteHead "└─" $ map ("  "++) $ showExprTreeLn str
        in  header ++ (memLns ++ strLns)
    (annot, CastNode tp sub) ->
        let header = ["Cast (" ++ showDt tp ++ ") : " ++ show annot]
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
        (annot, ForNode init cond expr body) ->
            let header = ["For : " ++ show annot]
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
        (annot, DefinitionNode dt id expr) ->
            let header = ["Definition " ++ showDt dt ++ " " ++ show id ++ " : " ++ show annot]
                exprLns = rewriteHead "└─" $ map ("  "++) $ showTreeR expr
            in  header ++ exprLns
        (annot, ExprNode e) -> showExprTreeLn e

showDeclList :: String -> DeclList -> String
showDeclList inter = L.intercalate inter . map (\ (t, n) -> showDt t ++ (' ':n))

instance Show ExprInfo where
    show (ExprInfo tp hd sl) = showDt tp ++ " (" ++ show hd ++ ") @ " ++ show sl

instance Show FunctionDefinition where
    show (FunctionDefinition rt name params root locs) =
        showDt rt ++ (' ':name ++ ('(':paramsStr ++ (")\n" ++ showSyntaxTree root)))
      where
        paramsStr = showDeclList ", " params

instance Show StructDefinition where
    show (StructDefinition (name, members)) =
        "struct " ++ (name ++ (" {\n  " ++ (membersStr ++ "}")))
      where
        membersStr = showDeclList ";\n  " members

instance Show Token where
    show (Identifier id) = "id '" ++ id ++ "'"
    show (Constant ct) = "constant '" ++ show ct ++ "'"
    show (Operator op) = op
    show (Control cnt) = cnt
    show (Punctuation p) = p
    show (Keyword kw) = kw
    show Eof = "eof"
    show (Invalid s) = s

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
    show _ = "(Invalid Operand)"

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
showVarHdr (Input name tp) = "input " ++ name ++ ' ':show tp
showVarHdr (Local name tp) = "local " ++ name ++ ' ':show tp

instance Show DNAInstruction where
    show (Mov dst src) = "mov" ++ (' ':show dst) ++ (' ':show src)
    show (Add dst src1 src2) = "add" ++ (' ':show dst) ++ (' ':show src1) ++ (' ':show src2)
    show (Sub dst src1 src2) = "sub" ++ (' ':show dst) ++ (' ':show src1) ++ (' ':show src2)
    show (Mul dst src1 src2) = "mul" ++ (' ':show dst) ++ (' ':show src1) ++ (' ':show src2)
    show (Div dst src1 src2) = "div" ++ (' ':show dst) ++ (' ':show src1) ++ (' ':show src2)
    show (Mod dst src1 src2) = "mov" ++ (' ':show dst) ++ (' ':show src1) ++ (' ':show src2)
    show (Cmp lhs rhs) = "cmp" ++ (' ':show lhs) ++ (' ':show rhs)
    show (Jmp cond lbl) = "j" ++ show cond ++ (' ':lbl)
    show (Param op) = "param" ++ (' ':show op)
    show (Call name output) = "call" ++ (' ':name) ++ (' ':show output)
    show (ReturnVal value) = "return" ++ (' ':show value)
    show ReturnVoid = "return"
    show ArrayCopy {} = error "implement me later"
    show (IntToFloat op1 op2) = "inttofloat " ++ (' ':show op1) ++ (' ':show op2)
    show (FloatToInt op1 op2) = "floattoint " ++ (' ':show op1) ++ (' ':show op2)
    show (Label lbl) = ".label " ++ (' ':lbl)

showFunction :: DNAFunctionDefinition -> String
showFunction (name, vars, body) =
    let header = [".sub " ++ name]
        var = map showVarHdr vars
        bod = map show body
        things = [header, var, [".endframe", ".label " ++ name], bod, [".endsub"]]
    in unlines $ concat things