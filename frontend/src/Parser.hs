module Parser where

import CompilerShared
import CompilerShow
import Control.Arrow
import Control.Monad
import Control.Monad.Loops (iterateUntilM, whileM_, whileM, untilM)
import Control.Monad.Trans
import Control.Monad.Trans.State.Lazy
import Data.Either
import Data.Functor
import Debug.Trace
import Lexer
import Data.Fix
import Data.Functor.Compose
import Data.Maybe (maybe)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

-- Raise a failure from the current node's start lex position to the last lexed position
raiseFailureHere :: String -> ParseAction a
raiseFailureHere why = join $ raiseFailurePrecise why <$> (currentNodeLexStart <$> get) <*> getPrevLexPosition <*> getLexPosition

getTypeEnv :: ParseAction TypeEnv
getTypeEnv = typeEnv <$> get
getLexerState :: ParseAction LexerState
getLexerState = lexerState <$> get
getSymbolMap :: ParseAction SymbolMap
getSymbolMap = symbolMap <$> get

pushSymbolEnv, popSymbolEnv :: ParseAction ()
pushSymbolEnv = do
    ParseState lexer typeEnv globals structs syms lp <- get
    put $ ParseState lexer typeEnv globals structs (M.empty:syms) lp
popSymbolEnv = do
    ParseState lexer typeEnv globals structs syms lp <- get
    put $ ParseState lexer typeEnv globals structs (tail syms) lp

getLexPosition, getPrevLexPosition :: ParseAction Int
getLexPosition = do
    (_, _, (clt, _)) <- getLexerState
    return clt
getPrevLexPosition = do
    (_, _, (_, plt)) <- getLexerState
    return plt

setCurrentLexStart :: Int -> ParseAction ()
setCurrentLexStart pos = do
    ParseState lexer typeEnv globals structs syms _ <- get
    put $ ParseState lexer typeEnv globals structs syms pos

insertSymbol :: String -> SymbolType -> ParseAction ()
insertSymbol symName sym = do
    when (S.member symName baseTypes) (raiseFailureHere $ "Can't declare reserved typename " ++ symName)
    ParseState lexer typeEnv globals structs syms lp <- get
    put $ ParseState lexer typeEnv globals structs (M.insert symName sym (head syms) : tail syms) lp

-- Lexes a new token, adding it to the LexerState
-- Returns the newly lexed token
lexNewToken :: ParseAction Token
lexNewToken = do
    ParseState (cacheTok, progStr, clt) typeEnv globals structs  syms lp <- get
    let (newTok, numParsed, restProg) = lexStringSingle typeEnv progStr
    put $ ParseState (cacheTok ++ [(newTok, numParsed)], restProg, clt) typeEnv globals structs syms lp
    return newTok

scanToken :: ParseAction Token
scanToken = do
    ParseState (cacheTok, progStr, clt) typeEnv globals structs  syms _ <- get
    when (null cacheTok) (void lexNewToken)
    state popToken

eatToken :: ParseAction ()
eatToken = void scanToken

peekToken :: ParseAction Token
peekToken = do
    (cacheTok, _, _) <- getLexerState
    if null cacheTok
      then lexNewToken
      else return $ fst (head cacheTok)

peekTwoToken :: ParseAction (Token, Token)
peekTwoToken = do
    (cacheTok, _, _) <- getLexerState
    case cacheTok of
        tok1:tok2:restTok -> return (fst tok1, fst tok2)
        [tok1]            -> (,) (fst tok1) <$> lexNewToken
        _                 -> (,) <$> lexNewToken <*> lexNewToken

peekThreeToken :: ParseAction (Token, Token, Token)
peekThreeToken = do
    (cacheTok, _, _) <- getLexerState
    case cacheTok of
        tok1:tok2:tok3:restTok -> return (fst tok1, fst tok2, fst tok3)
        [tok1, tok2]      -> (,,) (fst tok1) (fst tok2) <$> lexNewToken
        [tok1]            -> (,,) (fst tok1) <$> lexNewToken <*> lexNewToken
        _                 -> (,,) <$> lexNewToken <*> lexNewToken <*> lexNewToken

-- Generic helpers to validate a token given a predicate (and extract)
extractStrIfValid :: (Token -> Bool) -> String -> Token -> ParseAction String
extractStrIfValid check tokenClass token@(Invalid _ _) =
    raiseFailureHere $ show token ++ " when trying to get " ++ tokenClass
extractStrIfValid check tokenClass Eof =
    raiseFailureHere $ "Unexpected EOF when trying to get " ++ tokenClass
extractStrIfValid check tokenClass token =
    if check token
      then return (extractInner token)
      else raiseFailureHere $ "Tried to extract " ++ tokenClass ++ ", but got " ++ show token
  where
    extractInner :: Token -> String
    extractInner (Identifier s)  = s
    extractInner (Operator s)    = s
    extractInner (Control s)     = s
    extractInner (Punctuation s) = s
    extractInner _               = ""

checkTokenPredicate :: (Token -> Bool) -> String -> Token -> ParseAction ()
checkTokenPredicate check expected token@(Invalid _ _) =
    raiseFailureHere $ show token ++ " when trying to get token " ++ show expected
checkTokenPredicate check expected Eof =
    raiseFailureHere $ "Unexpected EOF when trying to get token " ++ show expected
checkTokenPredicate check expected token =
    unless
      (check token)
      (raiseFailureHere $ "Expected \"" ++ expected ++ "\" but got " ++ show token)

-- Helpers to validate several tokens, raises error if validation fails
extractIdentifierIfValid :: Token -> ParseAction String
extractIdentifierIfValid = extractStrIfValid isIdentifier "identifier"
extractOperatorIfValid :: Token -> ParseAction String
extractOperatorIfValid = extractStrIfValid isOperator "operator"
extractConstantIfValid :: Token -> ParseAction ConstantType
extractConstantIfValid (Constant val) = return val
extractConstantIfValid val              = raiseFailureHere $ "Expected constant but got " ++ show val
validatePunctuation :: String -> Token -> ParseAction ()
validatePunctuation val = checkTokenPredicate (punctuationMatches val) val
validateControl :: String -> Token -> ParseAction ()
validateControl val = checkTokenPredicate (controlMatches val) val
validateOperator :: String -> Token -> ParseAction ()
validateOperator val = checkTokenPredicate (operatorMatches val) val
validateKeyword :: String -> Token -> ParseAction ()
validateKeyword val = checkTokenPredicate (keywordMatches val) val

-- Helpers to consume a specific token (and extract contents for id/type)
scanIdentifier :: ParseAction String
scanIdentifier = scanToken >>= extractIdentifierIfValid
scanOperator :: ParseAction String
scanOperator = scanToken >>= extractOperatorIfValid
scanConstant :: ParseAction ConstantType
scanConstant = scanToken >>= extractConstantIfValid
eatPunctuation :: String -> ParseAction ()
eatPunctuation val = scanToken >>= validatePunctuation val
eatControl :: String -> ParseAction ()
eatControl val = scanToken >>= validateControl val
eatOperator :: String -> ParseAction ()
eatOperator val = scanToken >>= validateOperator val
eatKeyword :: String -> ParseAction ()
eatKeyword val = scanToken >>= validateKeyword val

parseProg :: String -> Either FailureInfo Program
parseProg progStr = fmap (globalsList &&& structList) (execStateT parseLoop (initialState progStr))
  where
    parseLoop = whileM_ (not . isEof <$> peekToken) parseTopLevel

parseTopLevel :: ParseAction ()
parseTopLevel = do
    (tok1, tok2, tok3) <- peekThreeToken
    case tok1 of 
        Keyword "struct" -> parseAndInsertStruct
        Identifier _ -> parseAndInsertGlobal tok3
        _ -> eatToken >> raiseFailureHere ("Unexpected top level token " ++ show tok1)
  where
    parseAndInsertGlobal :: Token -> ParseAction ()
    parseAndInsertGlobal tok3 =
        if punctuationMatches "(" tok3
          then do
            func <- parseFunction
            ParseState lexer env globals structs syms lp <- get
            put $ ParseState lexer env (globals ++ [Function func]) structs syms lp
          else do
            decl <- doAnnotateSyntax parseDeclaration
            ParseState lexer env globals structs syms lp <- get
            put $ ParseState lexer env (globals ++ [GlobalVar decl]) structs syms lp
            eatPunctuation ";"
                
    parseAndInsertStruct :: ParseAction ()
    parseAndInsertStruct = do
        lp <- getLexPosition
        setCurrentLexStart lp
        struct@(name, _) <- parseStruct
        lp <- getLexPosition
        setCurrentLexStart lp
        ParseState lexer env globals structs  syms lp <- get
        put $ ParseState lexer (S.insert name env) globals (structs ++ [struct])  syms lp

parseStruct :: ParseAction StructDefinition
parseStruct = do
    syms <- getSymbolMap
    eatKeyword "struct"
    id <- scanIdentifier
    insertSymbol id TypeSym
    eatPunctuation "{"
    structMembers <- whileM (isTypeName <$> getSymbolMap <*> peekToken) parseStructMember
    eatPunctuation "}"
    return (id, structMembers)
  where
    parseStructMember :: ParseAction (DataType, String)
    parseStructMember = do
        (memberTypeName, memberPtrList) <- parseType
        id <- scanIdentifier
        arrayList <- parseArraySpec
        eatPunctuation ";"
        return ((memberTypeName, arrayList ++ memberPtrList), id)

-- Return a parsed function as a SyntaxNode
parseFunction :: ParseAction FunctionDefinition 
parseFunction = do
    (typeBegin, typeName) <- seqPair (getLexPosition, parseType)
    (idBegin, id, idEnd) <- seqTrip (getLexPosition, scanIdentifier, getLexPosition)
    insertSymbol id FuncSym 
    pushSymbolEnv
    eatPunctuation "("
    (paramList, paramLocs) <- parseParamList
    eatPunctuation ")"
    blockNode <- doAnnotateSyntax parseBlock
    popSymbolEnv
    let fAnnot = FunctionAnnotation
         { returnTypeLoc = SourceLoc typeBegin idBegin
         , funcNameLoc = SourceLoc idBegin idEnd
         , paramsLoc = paramLocs
         }
    return $ FunctionDefinition typeName id paramList blockNode fAnnot


parseParamList :: ParseAction (DeclList, [SourceLoc])
parseParamList = do
    typeToken <- peekToken
    syms <- getSymbolMap
    if isTypeName syms typeToken
      then doActualParseParamList
      else return ([], [])
  where
    -- Parses the full param list, given there is at least one parameter
    doActualParseParamList :: ParseAction (DeclList, [SourceLoc])
    doActualParseParamList = do
        paramBeg <- getLexPosition
        typeName <- parseType
        id <- scanIdentifier
        paramEnd <- getLexPosition
        let loc = SourceLoc paramBeg paramEnd
        -- Prepend the first parameter (type, id, loc) onto the remaining parameters
        unzip . (((typeName, id), loc):) <$> whileM (punctuationMatches "," <$> peekToken) parseCommaParam
      where
        -- Parses a single ", typename identifier"
        parseCommaParam :: ParseAction ((DataType, String), SourceLoc)
        parseCommaParam = do
            eatToken
            paramBeg <- getLexPosition
            typeName <- parseType
            id <- scanIdentifier
            paramEnd <- getLexPosition
            let loc = SourceLoc paramBeg paramEnd
            return ((typeName, id), loc)

-- block = '{' stmt* '}'
parseBlock :: ParseAction (SyntaxNodeF SyntaxNode)
parseBlock = do
    eatPunctuation "{"
    pushSymbolEnv
    statementList <- whileM (peekToken <&> not . punctuationMatches "}") (doAnnotateSyntax parseStatement)
    popSymbolEnv
    eatPunctuation "}"
    return $ BlockNode $ sequenceStatements statementList
  where
    -- foldl ensures that sequence nodes are built in forward order
    sequenceStatements :: [SyntaxNode] -> SyntaxNode
    sequenceStatements = L.foldl' (\a x -> copyAnnot x $ SeqNode a x) (annotSyntaxEmpty EmptyNode)

isTypeName :: SymbolMap -> Token -> Bool
isTypeName smap (Identifier id) = getIdentifierType id smap == TypeSym
isTypeName _ _                  = False
-- For use to determine statement option, based on the START list for each
isBlock, isExpression, isLvalue, isConditional, isWhileLoop, isForLoop, isReturn, isEmpty, isContinue, isBreak, isPrint :: Token -> Bool
isBlock = punctuationMatches "{"
isExpression tok = any ($ tok) [isIdentifier, isConstant, punctuationMatches "(",
                                operatorMatches "!", operatorMatches "&", operatorMatches "*",
                                operatorMatches "-", operatorMatches "++", operatorMatches "--",
                                keywordMatches "bloat", keywordMatches "unbloat"]
isLvalue tok = any ($ tok) [isIdentifier, isConstant, punctuationMatches "(", punctuationMatches "*" ]
isConditional = controlMatches "if"
isWhileLoop = controlMatches "while"
isForLoop = controlMatches "for"
isReturn = controlMatches "return"
isEmpty = punctuationMatches ";"
isContinue = controlMatches "continue"
isBreak = controlMatches "break"
isPrint = keywordMatches "print"

parseStatement :: ParseAction (SyntaxNodeF SyntaxNode)
parseStatement = do
    tok <- peekToken
    smap <- getSymbolMap
    env <- getTypeEnv
    if isTypeName smap tok
      then parseDeclaration >>= (eatPunctuation ";" $>)
      else parseStatementLookahead env tok
  where
    parseStatementLookahead :: TypeEnv -> Token -> ParseAction (SyntaxNodeF SyntaxNode)
    parseStatementLookahead env lookahead
        | isBlock lookahead       = parseBlock
        | isExpression lookahead  = parseWrapExpression >>= (eatPunctuation ";" $>)
        | isConditional lookahead = parseCondition
        | isWhileLoop lookahead   = parseWhileLoop
        | isForLoop lookahead     = parseForLoop
        | isReturn lookahead      = parseReturn >>= (eatPunctuation ";" $>)
        | isEmpty lookahead       = eatPunctuation ";" $> EmptyNode
        | isContinue lookahead    = eatControl "continue" >> eatPunctuation ";" $> ContinueNode
        | isBreak lookahead       = eatControl "break" >> eatPunctuation ";" $> ContinueNode
        | isPrint lookahead       = do
            eatKeyword "print"
            expressionNode <- doAnnotateSyntax parseWrapExpression
            eatPunctuation ";"
            return $ PrintNode expressionNode
        | isInvalid lookahead     = raiseFailureHere $ show lookahead ++ " when parsing statement"
        | otherwise               = raiseFailureHere $ "Unexpected token " ++ show lookahead ++ " when parsing statement"

doAnnotateSyntax :: ParseAction (SyntaxNodeF SyntaxNode) -> ParseAction SyntaxNode
doAnnotateSyntax action = do
    startPos <- getLexPosition
    setCurrentLexStart startPos
    rawNode <- action
    endPos <- getLexPosition
    return $ annotSyntax startPos endPos rawNode

doAnnotateExpr :: ParseAction (ExprF Expr) -> ParseAction Expr
doAnnotateExpr action = do
    startPos <- getLexPosition
    setCurrentLexStart startPos
    rawNode <- action
    endPos <- getLexPosition
    return $ annotExprLoc (SourceLoc startPos endPos) rawNode

parseCondition :: ParseAction (SyntaxNodeF SyntaxNode)
parseCondition = do
    eatControl "if"
    eatPunctuation "("
    expressionNode <- doAnnotateSyntax parseWrapExpression
    eatPunctuation ")"
    block <- doAnnotateSyntax parseBlock
    (maybeElse, maybeIf) <- peekTwoToken
    if | controlMatches "else" maybeElse && controlMatches "if" maybeIf -> do
           eatControl "else"
           elseBlock <- doAnnotateSyntax parseCondition
           return $ IfElseNode expressionNode block elseBlock
       | controlMatches "else" maybeElse -> do
           eatControl "else"
           elseBlock <- doAnnotateSyntax parseBlock
           return $ IfElseNode expressionNode block elseBlock
       | otherwise -> return $ IfNode expressionNode block

parseWhileLoop :: ParseAction (SyntaxNodeF SyntaxNode)
parseWhileLoop = do
    eatControl "while"
    eatPunctuation "("
    expressionNode <- doAnnotateSyntax parseWrapExpression
    eatPunctuation ")"
    block <- doAnnotateSyntax parseBlock
    return $ WhileNode expressionNode block

parseForInit :: ParseAction (SyntaxNodeF SyntaxNode)
parseForInit = getSymbolMap >>= \syms -> peekToken >>= parseForInitLookahead syms
  where
    parseForInitLookahead :: SymbolMap -> Token -> ParseAction (SyntaxNodeF SyntaxNode)
    parseForInitLookahead syms lookahead
        | isTypeName syms lookahead        = parseDeclaration
        | isExpression lookahead           = parseWrapExpression
        | punctuationMatches ";" lookahead = return EmptyNode
        | isInvalid lookahead              = raiseFailureHere $ show lookahead ++ " when parsing statement"
        | otherwise                        = raiseFailureHere $ "Unexpected token " ++ show lookahead ++ " in for loop init"

parseForExpr :: ParseAction (SyntaxNodeF SyntaxNode)
parseForExpr = peekToken >>= parseForExprLookahead
  where
    parseForExprLookahead :: Token -> ParseAction (SyntaxNodeF SyntaxNode)
    parseForExprLookahead lookahead
        | isExpression lookahead           = parseWrapExpression
        | punctuationMatches ";" lookahead ||
          punctuationMatches ")" lookahead = return EmptyNode
        | isInvalid lookahead              = raiseFailureHere $ show lookahead ++ " in for loop"
        | otherwise                        = raiseFailureHere $ "Unexpected token " ++ show lookahead ++ " in for loop"

parseForLoop :: ParseAction (SyntaxNodeF SyntaxNode)
parseForLoop = do
    pushSymbolEnv
    eatControl "for"
    eatPunctuation "("
    forInit <- doAnnotateSyntax parseForInit
    eatPunctuation ";"
    forCond <- doAnnotateSyntax parseForExpr
    eatPunctuation ";"
    forExpr <- doAnnotateSyntax parseForExpr
    eatPunctuation ")"
    block <- doAnnotateSyntax parseBlock
    lookahead <- peekToken
    orBlock <- if controlMatches "or" lookahead
    then do
        eatToken
        doAnnotateSyntax parseBlock
    else return $ annotSyntaxEmpty EmptyNode
    popSymbolEnv
    return $ ForNode forInit forCond forExpr block orBlock

parseDeclaration :: ParseAction (SyntaxNodeF SyntaxNode)
parseDeclaration = do
    declBegin <- getLexPosition
    typeName <- parseTypename
    firstDeclaration <- doAnnotateSyntax $ parseDecltrail declBegin typeName
    declList <- (firstDeclaration:) <$> whileM (punctuationMatches "," <$> peekToken)
                                               (eatToken >> doAnnotateSyntax (parseDecltrail declBegin typeName))
    let root = L.foldl1' (\a x -> copyAnnot x $ SeqNode a x) declList
    return $ SeqNode root (annotSyntaxEmpty EmptyNode)
  where
    parseDecltrail :: Int -> String -> ParseAction (SyntaxNodeF SyntaxNode)
    parseDecltrail declBegin typeName = do
        ptrList <- parseQualifier
        id <- scanIdentifier
        arrayList <- parseArraySpec
        nextTok <- peekToken
        case nextTok of
            Operator "=" -> do 
                eatToken
                expressionNode <- parseExpression
                declEnd <- getLexPosition
                insertSymbol id VarSym
                let exprAnn = annotExprLoc (SourceLoc declBegin declEnd) expressionNode
                    assnAnn = copyAnnot exprAnn $ AssignmentNode NoOp (annotExprEmpty $ IdentifierNode id) exprAnn
                    assnExprAnn = annotSyntax declBegin declEnd (ExprNode assnAnn)
                    declAnn  = copyAnnot assnExprAnn (DeclarationNode (typeName, arrayList ++ ptrList) id)
                return $ SeqNode declAnn assnExprAnn
            _            -> do 
                insertSymbol id VarSym
                return $ DeclarationNode (typeName, arrayList ++ ptrList) id


parseReturn :: ParseAction (SyntaxNodeF SyntaxNode)
parseReturn = do
    eatControl "return"
    lookahead <- peekToken
    if punctuationMatches ";" lookahead
      then return $ ReturnNode $ annotSyntaxEmpty EmptyNode
      else ReturnNode <$> doAnnotateSyntax parseWrapExpression

parseWrapExpression :: ParseAction (SyntaxNodeF SyntaxNode)
parseWrapExpression = ExprNode <$> doAnnotateExpr parseExpression

parseExpression :: ParseAction (ExprF Expr)
parseExpression = parseAssignment
    
assignOpsList :: S.Set String
assignOpsList = S.fromList ["=", "+=", "-=", "*=", "/=", "%="]

isAssignmentOperator :: Token -> Bool
isAssignmentOperator (Operator op) = S.member op assignOpsList
isAssignmentOperator _             = False

scanAssignmentOperator :: ParseAction ()
scanAssignmentOperator = scanToken >>= \x -> unless (isAssignmentOperator x) (raiseFailureHere "Expected assignment token operator")

parseAssignment :: ParseAction (ExprF Expr)
parseAssignment = do
    startState <- get
    let dryRun = runStateT (parseLvalue >> scanAssignmentOperator) startState
    if isRight dryRun
      then do
        lhs <- doAnnotateExpr parseLvalue
        assignOp <- scanToken
        AssignmentNode (getAssignOp assignOp) lhs <$> doAnnotateExpr parseAssignment
      else parseLogicOr
  where
    getAssignOp (Operator o)
        | o == "="  = NoOp
        | o == "+=" = PlusEq
        | o == "-=" = MinusEq
        | o == "*=" = MulEq
        | o == "/=" = DivEq
        | o == "%=" = ModEq
        | otherwise = error "getAssignOp should never receive an invalid assign operator"
    getAssignOp _ = error "getAssignOp should never receive an invalid assign operator"

parseLvalue :: ParseAction (ExprF Expr)
parseLvalue = do
    token <- peekToken
    if operatorMatches "*" token
    then do
        eatToken
        UnaryOpNode Dereference <$> doAnnotateExpr parseLvalue
    else
        parseIndirection

type BinaryNodeCombinator = Expr -> Expr -> ExprF Expr

parseOpPrecedence
    :: ParseAction (ExprF Expr) -- Subexpr parser action
    -> [(String, BinaryNodeCombinator)] -- (Operator, combinator) pairs
    -> ParseAction (ExprF Expr) -- Root node
parseOpPrecedence parseAction opCombine = do
    init <- doAnnotateExpr parseAction
    equalPrecedenceList <- whileM shouldContinue execMatched
    let rootNode = L.foldl' (\a (node, combine) -> annotExprLoc (getBounds a node) (combine a node)) init equalPrecedenceList
    -- Sorry for this future me
    return $ getExprF rootNode
  where
    checks = map (first operatorMatches) opCombine
    shouldContinue :: ParseAction Bool
    shouldContinue = do
        nextTok <- peekToken
        return $ any (($ nextTok) . fst) checks
    execMatched :: ParseAction (Expr, BinaryNodeCombinator)
    execMatched = do
        nextTok <- scanToken
        let combineFn = snd $ head $ filter (($ nextTok) . fst) checks
        nextExpr <- doAnnotateExpr parseAction
        return (nextExpr, combineFn) 

getBounds :: Expr -> Expr -> SourceLoc
getBounds left right = SourceLoc (srcBegin $ sourceLocOf left) (srcEnd $ sourceLocOf right)

parseLogicOr :: ParseAction (ExprF Expr)
parseLogicOr = parseOpPrecedence parseLogicAnd [("||", BinaryOpNode Or)]

parseLogicAnd :: ParseAction (ExprF Expr)
parseLogicAnd = parseOpPrecedence parseEqComp [("&&", BinaryOpNode And)]

parseEqComp :: ParseAction (ExprF Expr)
parseEqComp = parseOpPrecedence parseOrdComp [("==", BinaryOpNode Equal),
                                              ("!=", BinaryOpNode NotEqual)]

parseOrdComp :: ParseAction (ExprF Expr)
parseOrdComp = parseOpPrecedence parseAddition [(">", BinaryOpNode GreaterThan),
                                                ("<", BinaryOpNode LessThan),
                                                (">=", BinaryOpNode GreaterThanOrEqual),
                                                ("<=", BinaryOpNode LessThanOrEqual)]

parseAddition :: ParseAction (ExprF Expr)
parseAddition = parseOpPrecedence parseMultiplication [("+", BinaryOpNode Addition),
                                                       ("-", BinaryOpNode Subtraction)]

parseMultiplication :: ParseAction (ExprF Expr)
parseMultiplication = parseOpPrecedence parseUnary [("*", BinaryOpNode Multiplication),
                                                    ("/", BinaryOpNode Division),
                                                    ("%", BinaryOpNode Modulus)]

parseUnary :: ParseAction (ExprF Expr)
parseUnary = do
    smap <- symbolMap <$> get
    (op, secondTok) <- peekTwoToken
    if  | operatorMatches "-" op  -> eatToken >> UnaryOpNode Negate <$> doAnnotateExpr parseUnary
        | operatorMatches "!" op  -> eatToken >> UnaryOpNode Not <$> doAnnotateExpr parseUnary
        | operatorMatches "&" op  -> eatToken >> UnaryOpNode Reference <$> doAnnotateExpr parseUnary
        | operatorMatches "*" op  -> eatToken >> UnaryOpNode Dereference <$> doAnnotateExpr parseUnary
        | operatorMatches "++" op -> eatToken >> UnaryOpNode PrefixInc <$> doAnnotateExpr parseUnary
        | operatorMatches "--" op -> eatToken >> UnaryOpNode PrefixDec <$> doAnnotateExpr parseUnary
        | punctuationMatches "(" op && isTypeName smap secondTok-> do
            eatToken
            dataType <- parseType
            eatPunctuation ")"
            CastNode dataType <$> doAnnotateExpr parseUnary
        | otherwise -> parseIndirection

parseIndirection :: ParseAction (ExprF Expr)
parseIndirection = do
    (lookahead, lookahead2) <- peekTwoToken
    rootExpr <- if isIdentifier lookahead && punctuationMatches "(" lookahead2
                  then doAnnotateExpr parseCall
                  else doAnnotateExpr parseBaseExpr
    parseIndirectionTrail rootExpr
  where
    parseCall :: ParseAction (ExprF Expr)
    parseCall = do
        id <- scanIdentifier
        eatPunctuation "("
        argList <- parseArgList
        eatPunctuation ")"
        return $ FunctionCallNode id argList

parseIndirectionTrail :: Expr -> ParseAction (ExprF Expr)
parseIndirectionTrail root = do
    lookahead <- peekToken
    if | operatorMatches "++" lookahead -> parsePost PostInc
       | operatorMatches "--" lookahead ->  parsePost PostDec
       | operatorMatches "." lookahead -> parseMemberAccess False
       | operatorMatches "->" lookahead -> parseMemberAccess True
       | punctuationMatches "[" lookahead ->  parseSubscript
       | otherwise -> return $ getExprF root
  where
    parsePost :: PostfixOp -> ParseAction (ExprF Expr)
    parsePost op = do
        eatToken
        doAnnotateExpr (return $ PostfixOpNode op root) >>= parseIndirectionTrail 
    parseMemberAccess :: Bool -> ParseAction (ExprF Expr)
    parseMemberAccess isPtr = do
        eatToken
        member <- doAnnotateExpr $ StructMemberNode <$> scanIdentifier
        doAnnotateExpr (return $ MemberAccessNode isPtr root member) >>= parseIndirectionTrail
    parseSubscript :: ParseAction (ExprF Expr)
    parseSubscript = do
        eatToken
        idx <- doAnnotateExpr parseExpression
        eatPunctuation "]"
        doAnnotateExpr (return $ ArrayIndexNode root idx) >>= parseIndirectionTrail

parseBaseExpr :: ParseAction (ExprF Expr)
parseBaseExpr = do
    lookahead <- peekToken
    if  | isIdentifier lookahead             -> parseId
        | isConstant lookahead               -> parseConstant
        | keywordMatches "no" lookahead      -> eatToken >> return (LiteralNode NullConstant)
        | punctuationMatches "(" lookahead   -> parseParenthesis
        | punctuationMatches "[" lookahead   -> parseArrayLit
        | isInvalid lookahead                -> raiseFailureHere $ show lookahead ++ " in base expression"
        | keywordMatches "bloat" lookahead   -> parseBloat
        | keywordMatches "unbloat" lookahead -> parseUnbloat
        | otherwise                          -> raiseFailureHere $ "Unexpected token " ++ show lookahead ++ " in base expression"
  where
    parseId :: ParseAction (ExprF Expr)
    parseId = IdentifierNode <$> scanIdentifier
    parseConstant :: ParseAction (ExprF Expr)
    parseConstant = LiteralNode <$> scanConstant 
    parseParenthesis :: ParseAction (ExprF Expr)
    parseParenthesis = do
        eatPunctuation "("
        expr <- doAnnotateExpr parseExpression
        eatPunctuation ")"
        return $ ParenthesisNode expr
    parseArrayLit :: ParseAction (ExprF Expr)
    parseArrayLit = do
        arrayBegin <- getLexPosition
        eatPunctuation "["
        check <- peekToken
        if | isConstant check -> parseArrayLitHelper arrayBegin parseConstant
           | punctuationMatches "[" check -> parseArrayLitHelper arrayBegin parseArrayLit
           | otherwise -> raiseFailureHere $ "Unexpected token in array parse " ++ show check
      where
        parseArrayLitHelper arrayBegin parser = do
            firstElem <- parseConstant
            listOut <- (firstElem:) <$> whileM (punctuationMatches "," <$> peekToken) (eatToken >> parser)
            eatPunctuation "]"
            arrayEnd <- getLexPosition
            let annotOut = map (annotExprLoc (SourceLoc arrayBegin arrayEnd)) listOut
            return $ ArrayLiteralNode annotOut
    parseBloat :: ParseAction (ExprF Expr)
    parseBloat = do
        eatKeyword "bloat"
        eatPunctuation "("
        dataType <- parseType
        eatPunctuation ","
        expr <- doAnnotateExpr parseExpression
        eatPunctuation ")"
        return $ DynamicAllocationNode dataType expr
    parseUnbloat :: ParseAction (ExprF Expr)
    parseUnbloat = do
        eatKeyword "unbloat"
        eatPunctuation "("
        expr <- doAnnotateExpr parseExpression
        eatPunctuation ")"
        return $ DynamicFreeNode expr

parseArgList :: ParseAction [Expr]
parseArgList = do
    maybeExpr <- peekToken
    if isExpression maybeExpr
        then doActualParseArgList
        else return []
  where
    doActualParseArgList :: ParseAction [Expr]
    doActualParseArgList = do
        firstArg <- doAnnotateExpr parseExpression
        (firstArg:) <$> whileM (punctuationMatches "," <$> peekToken) parseCommaArg
      where
        parseCommaArg :: ParseAction Expr
        parseCommaArg = do
            eatToken
            doAnnotateExpr parseExpression

evalConstExpression :: Expr -> Maybe ConstantType
evalConstExpression = foldFixM (alg . snd . getCompose)
  where
    alg :: ExprF ConstantType -> Maybe ConstantType
    alg (LiteralNode val)         = Just val
    alg (ParenthesisNode sub)     = Just sub
    alg (BinaryOpNode op lhs rhs) = computeBOp op lhs rhs
    alg (UnaryOpNode op sub)      = computeUOp op sub
    alg (CastNode tp sub)         = computeCast tp sub
    alg _ = Nothing
    computeCast :: DataType -> ConstantType -> Maybe ConstantType
    computeCast tp val
        | tp == charType  = Just val
        | tp == shortType = Just val
        | tp == intType   = Just val
        | tp == longType  = Just val
        | tp == floatType = Just val
        | tp == boolType  = Just val
        | otherwise = Nothing
    computeUOp :: UnaryOp -> ConstantType -> Maybe ConstantType
    computeUOp Negate val = case val of
        FloatConstant f1 -> Just $ FloatConstant (negate f1)
        IntConstant i1   -> Just $ IntConstant (negate i1)
        CharConstant c1  -> Just $ CharConstant (negate c1)
        _ -> Nothing
    computeUOp Not val = case val of
        BoolConstant b1 -> Just $ BoolConstant (not b1)
        _ -> Nothing
    computeUOp _ _ = error "Bad UOp fuck"
    computeBOp :: BinaryOp -> ConstantType -> ConstantType -> Maybe ConstantType
    computeBOp Addition lhs rhs = numCall (+) lhs rhs
    computeBOp Subtraction lhs rhs = numCall (-) lhs rhs
    computeBOp Multiplication lhs rhs = numCall (*) lhs rhs
    computeBOp Division lhs rhs = case (lhs, rhs) of
        (FloatConstant f1, FloatConstant f2) -> Just $ FloatConstant (f1 / f2)
        (IntConstant i1, IntConstant i2)     -> Just $ IntConstant (i1 `div` i2)
        (CharConstant c1, CharConstant c2)   -> Just $ CharConstant (c1 `div` c2)
        _ -> Nothing
    computeBOp Modulus lhs rhs = case (lhs, rhs) of
        (IntConstant i1, IntConstant i2)   -> Just $ IntConstant (i1 `mod` i2)
        (CharConstant c1, CharConstant c2) -> Just $ CharConstant (c1 `mod` c2)
        _ -> Nothing
    computeBOp Equal lhs rhs = cmpCall (==) lhs rhs
    computeBOp NotEqual lhs rhs = cmpCall (/=) lhs rhs
    computeBOp LessThan lhs rhs = cmpCall (<) lhs rhs
    computeBOp GreaterThan lhs rhs = cmpCall (>) lhs rhs
    computeBOp GreaterThanOrEqual lhs rhs = cmpCall (>=) lhs rhs
    computeBOp LessThanOrEqual lhs rhs = cmpCall (<=) lhs rhs
    computeBOp Or lhs rhs = boolCall (||) lhs rhs
    computeBOp And lhs rhs = boolCall (&&) lhs rhs

parseConstantExpression :: ParseAction ConstantType
parseConstantExpression = do
    expr <- doAnnotateExpr parseExpression
    maybe (raiseFailureLoc "Invalid constant expression" (sourceLocOf expr)) return (evalConstExpression expr) 
    

parseArraySpec :: ParseAction [Int]
parseArraySpec = do
    whileM (punctuationMatches "[" <$> peekToken) parseArrayDecl
  where
    parseArrayDecl :: ParseAction Int
    parseArrayDecl = do
        eatPunctuation "["
        constant <- parseConstantExpression
        case constant of
            IntConstant v -> do
                eatPunctuation "]"
                when (v <= 0) (raiseFailureHere "Array sizes must be greater than 0")
                return (fromIntegral v)
            _             -> raiseFailureHere "Non-constant/integral size used in array declaration"

parseTypename :: ParseAction String
parseTypename = scanIdentifier

parseQualifier :: ParseAction [Int]
parseQualifier = whileM (operatorMatches "*" <$> peekToken) (eatToken $> 0)

parseType :: ParseAction DataType
parseType = do
    typeName <- scanIdentifier
    ptrLevels <- parseQualifier
    return (typeName, ptrLevels)
  
{-
prog = toplevel
toplevel = function | structdecl | declaration
function = type identifier '(' paramlist ')' block
structdecl = 'struct' identifier '{' member* '}'
member = type identifier arrayspec ';'
paramlist = type identifier (',' type identifier)* | ε
block = '{' stmt* '}'
stmt = declaration ';' | block | expression ';' | conditional |
       forloop | whileloop | ret ';' | 'continue' ';' | 'break' ';' | print expression ';'
declaration = typename decl_trail (',' decl_trail)*
decl_trail = qualifier identifier arrayspec optassign
optassign = '=' expression | ε
whileloop = 'while' '(' expression ')' block
forinit = declaration | assignment | ε
forexpr = expression | ε
forloop = 'for' '(' forinit ';' forexpr ';' forexpr ')' block
conditional = 'if' '(' expression ')' block elseconditional
elseconditional = 'else' 'if' block elseconditional | 'else' block | ε
ret = 'return' expression
constant_expression = expression
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
unary = '-' unary | '!' unary | '&' unary | '*' unary | '(' type ')' |
        '++' unary | '--' unary | '(' type ')' unary | indirection
indirection = identifier '(' arglist ')' indirection_rest |
              baseexpr indirection_rest 
indirection_trail = '++' indirection_trail |
                    '--' indirection_trail |
                    '.' identifier indirection_trail |
                    '[' expression ']' indirection_trail |
                    ε
baseexpr = identifier | constant | arraylit | '(' expression ')' |
           'bloat' '(' type ',' number ')' | 'unbloat' '(' expression ')'
arglist = expression (',' expression)* | ε
type = identifier qualifier
qualifier = '*'*
arrayspec = '[' constant_expression ']'*
arraylit = '[' arraylit (',' arraylit) ']' | '[' constant_expression (',' constant_expression)* ']'
constant = 'true' | 'false' | number
number = -?[0-9]+\.[0-9]*
identifier = [A-Za-z][A-Za-z0-9_]*
-}
