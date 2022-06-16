module Lexer
( lexString
, lexStringSingle
, ConstantType(..)
, Token(..)
, LexerResult
, isIdentifier
, isTypeName
, isConstant
, isOperator
, isControl
, isPunctuation
, isEof
, isInvalid
, punctuationMatches
, controlMatches
, operatorMatches
) where

import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Char as C
import System.IO

data ConstantType
  = IntConstant Integer
  | FloatConstant Float
  | BoolConstant Bool
  | StringConstant String
  deriving (Show, Eq)

data Token
  = Identifier String
  | TypeName String
  | Constant ConstantType
  | Operator String
  | Control String
  | Punctuation String
  | Eof
  | Invalid
  deriving (Show, Eq)

type LexerResult = (Token, String)

isIdentifier :: Token -> Bool
isIdentifier (Identifier _) = True
isIdentifier _              = False

isTypeName :: Token -> Bool
isTypeName (TypeName _) = True
isTypeName _            = False

isConstant :: Token -> Bool
isConstant (Constant _) = True
isConstant _            = False

isOperator :: Token -> Bool
isOperator (Operator _) = True
isOperator _            = False

isControl :: Token -> Bool
isControl (Control _) = True
isControl _           = False

isPunctuation :: Token -> Bool
isPunctuation (Punctuation _) = True
isPunctuation _               = False

isEof :: Token -> Bool
isEof Eof = True
isEof _   = False

isInvalid :: Token -> Bool
isInvalid Invalid = True
isInvalid _       = False

punctuationMatches :: String -> Token -> Bool
punctuationMatches v (Punctuation p) = p == v
punctuationMatches _ _               = False

controlMatches :: String -> Token -> Bool
controlMatches v (Control c) = c == v
controlMatches _ _           = False

operatorMatches :: String -> Token -> Bool
operatorMatches v (Operator o) = o == v
operatorMatches _ _             = False

operators :: S.Set String
operators = S.fromList ["=", "+=", "-=", "*=", "/=", "%=", "||", "&&", "==", "!=", "<", "<=", ">", ">=", "+", "-", "*", "/", "%", "!"]

allOperatorChars :: S.Set Char
allOperatorChars = S.foldr (S.union . S.fromList) S.empty operators

isOperatorChar :: Char -> Bool
isOperatorChar h = S.member h allOperatorChars

isLetterChar :: Char -> Bool
isLetterChar h = C.isAlpha h || h == '_'

isIdentifierChar :: Char -> Bool
isIdentifierChar h = C.isAlphaNum h || h == '_'

isNumber :: Char -> Bool
isNumber h = C.isDigit h || h == '.'

control :: S.Set String
control = S.fromList ["if", "else", "for", "while", "return"]

punctuation :: S.Set String
punctuation = S.fromList ["(", ")", "{", "}", ",", ";"]

isPunctuationChar :: Char -> Bool
isPunctuationChar h = S.member [h] punctuation

types :: S.Set String
types = S.fromList ["void", "char", "short", "int", "long", "float", "double", "bool", "string"]


lexStringSingle :: String -> LexerResult
lexStringSingle (h:t)
    | isOperatorChar h    = let (token, rest) = spanOperator (h:t)
                            in (Operator token, rest)
    | isPunctuationChar h = (Punctuation [h], t)
    | C.isDigit h         = let (token, rest) = span Lexer.isNumber t
                            in (classifyNumberToken (h:token), rest)
    | isLetterChar h      = let (token, rest) = span isIdentifierChar t
                              in (classifyLetterToken (h:token), rest)
    | C.isSpace h         = lexStringSingle $ eatWs t
    | h == '"'            = lexStringConstant t
    | otherwise           = (Invalid, t)
  where
    lexStringConstant :: String -> LexerResult
    lexStringConstant str
        = tryAppendStr $ until endingQuote buildString ("", str)
      where
        endingQuote (_, h1:t) = h1 == '"'
        endingQuote (_, []) = True
        buildString (lhs, h1:h2:t)
            | h1 == '\\' && h2 == 'n' = (lhs ++ ['\n'], t)
            | h1 == '\\' && h2 == 't' = (lhs ++ ['\t'], t)
            | h1 == '\\' && h2 == 'r' = (lhs ++ ['\r'], t)
            | h1 == '\\' && h2 == '"' = (lhs ++ ['"'], t)
            | otherwise               = (lhs ++ [h1], h2:t)
        buildString (lhs, [h]) = (lhs ++ [h], t)
        buildString (lhs, [])  = (lhs, "")
        tryAppendStr (buildStr, _:t) = (Constant $ StringConstant buildStr, t)
        tryAppendStr (_, rest) = (Invalid, rest)
    eatWs str = dropWhile C.isSpace str
    classifyNumberToken str
        | '.' `elem` str = Constant $ FloatConstant (read str :: Float)
        | otherwise      = Constant $ IntConstant (read str :: Integer)
    classifyLetterToken str
        | str == "true"            = Constant $ BoolConstant True
        | str == "false"           = Constant $ BoolConstant False
        | S.member str control     = Lexer.Control str
        | S.member str punctuation = Punctuation str
        | S.member str types       = TypeName str
        | otherwise                = Identifier str
    spanOperator :: String -> (String, String)
    spanOperator str = (extracted, last next:rest)
      where
        checkStop (cur, next, [])    = True
        checkStop (cur, next, rest)  = not $ S.member next operators
        (extracted, next, rest)      = until checkStop
                                       (\(cur, next, rest) -> (next, next ++ [head rest], tail rest))
                                       ("", [head str], tail str)
lexStringSingle [] = (Eof, "")

lexString :: String -> [Token]
lexString str = fst (until (\(_, rest) -> rest == "")
                           (\(tokList, curStr) -> let (newTok, remaining) = lexStringSingle curStr
                                                  in (tokList ++ [newTok], remaining)) 
                           ([], str)) ++ [Eof]
