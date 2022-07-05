# Not C

Compiler for an approximate of C written in Haskell without usage of parsec.

Approximate grammar below
```
prog = toplevel
toplevel = function | structdecl
function = type identifier '(' paramlist ')' block
structdecl = 'struct' identifier '{' member* '}'
member = type identifier arrayspec ';'
paramlist = type identifier (',' type identifier)* | ε
block = '{' stmt* '}'
stmt = declaration ';' | block | expression ';' | conditional | forloop | whileloop | ret ';' | 'continue' ';' | 'break' ';'
declaration = type identifier arrayspec optassign
optassign = '=' expression | ε
whileloop = 'while' '(' expression ')' block
forinit = declaration | assignment | ε
forexpr = expression | ε
forloop = 'for' '(' forinit ';' forexpr ';' forexpr ')' block
conditional = 'if' '(' expression ')' block elseconditional
elseconditional = 'else' block | ε
ret = 'return' expression
expression = assignment
assignment = lvalue '=' assignment  | lvalue '+=' assignment |
             lvalue '-=' assignment | lvalue '*=' assignment |
             lvalue '/=' assignment | lvalue '%=' assignment | logicor
lvalue = '*' lvalue | indirection
logicor = logicand ('||' logicand)*
logicand = eqcomp ('&&' eqcomp)*
eqcomp = ordcomp ('==' ordcomp)* | ordcomp ('!=' orcomp)*
ordcomp = addition ('<' addition)* | addition ('>' addition)* | addition ('<=' addition)* | addition ('>=' addition)*
addition = multiplication ('+' multiplication)* | multiplication ('-' multiplication)*
multiplication = unary ('*' unary)* | unary ('/' unary)* | unary ('%' unary)*
unary = '-' unary | '!' unary | '&' unary | '*' unary | '(' type ')' | indirection
indirection = identifier '(' arglist ')' ('[' expression ']')* memberaccess*
            | baseexpr ('[' expression ']')* memberaccess* 
memberaccess = '.' identifier ('[' expression ']')*
baseexpr = identifier | constant | '(' expression ')'
arglist = expression (',' expression)* | ε
type = identifier qualifier
qualifier = '*'*
arrayspec = '[' constant ']'*
constant = 'true' | 'false' | number
number = -?[0-9]+\.[0-9]*
identifier = [A-Za-z][A-Za-z0-9_]*
```
