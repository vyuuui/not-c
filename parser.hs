module Parser
(

) where

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L
import Lexer

data VarInfo = FunctionVar [(String, String)] | PrimitiveVar String String
type StatementBlock = [StatementNode]
data Environment = EnvLink (M.Map String VarInfo) Environment | EnvBase (M.Map String VarInfo)

data ProgNode 
    = FunctionDefinitionNode String String [(String, String)] StatementBlock

data StatementNode
    = ControlNode
    | ExpressionNode
    | DeclarationNode String String
    | DefinitionNode String String ExpressionNode

data ControlNode
    = WhileNode ExpressionNode StatementBlock
    | IfNode ExpressionNode StatementBlock 
    | IfElseNode ExpressionNode StatementBlock StatementBlock
    | ReturnNode ExpressionNode

data BinaryOp
    = Addition
    | Multiplication
    | Subtraction
    | Division
    | Mod
    | Equal
    | NotEqual
    | LessThan
    | GreaterThan
    | GreaterThanOrEqual
    | LessThanOrEqual
    | Or
    | And

data AssignmentOp
    = NoOp
    | PlusEq
    | MinusEq
    | MulEq
    | DivEq
    | ModEq

data UnaryOp = Negate

data ExpressionNode
    = IdentifierNode String String
    | LiteralNode ConstantType
    | FunctionCallNode String [ExpressionNode]
    | ParenthesisNode ExpressionNode
    | BinaryOpNode BinaryOp ExpressionNode ExpressionNode
    | UnaryOpNode UnaryOp ExpressionNode
    | AssignmentNode String AssignmentOp ExpressionNode



{-
prog = function+
function = type identifier '(' paramlist ')' block
paramlist = type identifier (',' type identifier)* | ε
block = '{' stmt* '}'
stmt = declaration ';' | block | expression ';' | conditional | loop | ret ';'
declaration = type identifier optassign
optassign = '=' expression | ε
loop = 'while' '(' expression ')' block
conditional = 'if' '(' expression ')' block elseconditional
elseconditional = 'else' block | ε
ret = 'return' expression
expression = assignment
assignment = identifier '=' assignment  | identifier '+=' assignment |
             identifier '-=' assignment | identifier '*=' assignment |
             identifier '/=' assignment | identifier '%=' assignment | logicor
logicor = logicand ('||' logicand)*
logicand = eqcomp ('&&' eqcomp)*
eqcomp = ordcomp ('==' ordcomp)* | ordcomp ('!=' orcomp)*
ordcomp = addition ('<' addition)* | addition ('>' addition)* | addition ('<=' addition)* | addition ('>=' addition)*
addition = multiplication ('+' multiplication)* | multiplication ('-' multiplication)*
multiplication = uneg ('*' uneg)* | uneg ('/' uneg)* | uneg ('%' uneg)*
uneg = '-' baseexpr | baseexpr
baseexpr = identifier '(' arglist ')' | identifier | constant | '(' expression ')'
arglist = expression (',' arglist)* | ε

type = 'void' | 'char' | 'short' | 'int' | 'long' | 'float' | 'double' | 'bool'
constant = 'true' | 'false' | number
number = -?[0-9]+\.[0-9]*
identifier = [A-Za-z][A-Za-z0-9_]*
-}