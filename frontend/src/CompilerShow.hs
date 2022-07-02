module CompilerShow
( showExprTree
, showSyntaxTree
, FunctionDefinition(..)
, StructDefinition(..)
, ExprType(..)
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
        let header = ["Cast (" ++ show (ExprType tp) ++ ") : " ++ show annot]
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
        (annot, DeclarationNode dt id) -> ["Declaration " ++ show (ExprType dt) ++ " " ++ show id ++ " : " ++ show annot]
        (annot, DefinitionNode dt id expr) ->
            let header = ["Definition " ++ show (ExprType dt) ++ " " ++ show id ++ " : " ++ show annot]
                exprLns = rewriteHead "└─" $ map ("  "++) $ showTreeR expr
            in  header ++ exprLns
        (annot, ExprNode e) -> showExprTreeLn e

showDeclList :: String -> [(DataType, String)] -> String
showDeclList inter = L.intercalate inter . map (\ (t, n) -> show (ExprType t) ++ (' ':n))

instance Show FunctionDefinition where
    show (FunctionDefinition rt name params root) =
        show (ExprType rt) ++ (' ':name ++ ('(':paramsStr ++ (")\n" ++ showSyntaxTree root)))
      where
        paramsStr = showDeclList ", " params

instance Show StructDefinition where
    show (StructDefinition (name, members)) =
        "struct " ++ (name ++ (" {\n  " ++ (membersStr ++ "}")))
      where
        membersStr = showDeclList ";\n  " members

instance Show ExprType where
    show (ExprType (tp, pList)) = tp ++ concatMap (\i -> if i == 0 then "*" else "[" ++ show i ++ "]") pList
