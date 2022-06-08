module Lexer
( lexString
, lexStringSingle
, ConstantType(..)
, Token(..)
, LexerResult
) where

import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Char as C

data ConstantType
  = IntConstant Integer
  | FloatConstant Float
  | BoolConstant Bool
  deriving Show

data Token
  = Identifier String
  | TypeName String
  | Constant ConstantType
  | Operator String
  | Control String
  | Punctuation String
  | Eof
  | Invalid
  deriving Show

type LexerResult = (Token, String)

operators :: S.Set String
operators = S.fromList ["=", "+=", "-=", "*=", "/=", "%=", "||", "&&", "==", "!=", "<", "<=", ">", ">=", "+", "-", "*", "/", "%"]

allOperatorChars :: S.Set Char
allOperatorChars = S.foldr (S.union . S.fromList) S.empty operators

isOperator :: Char -> Bool
isOperator h = S.member h allOperatorChars

isLetter :: Char -> Bool
isLetter h = C.isAlpha h || h == '_'

isIdentifier :: Char -> Bool
isIdentifier h = C.isAlphaNum h || h == '_'

isNumber :: Char -> Bool
isNumber h = C.isDigit h || h == '.'

control :: S.Set String
control = S.fromList ["if", "else", "for", "while", "return"]

punctuation :: S.Set String
punctuation = S.fromList ["(", ")", "{", "}", ",", ";"]

isPunctuation :: Char -> Bool
isPunctuation h = S.member [h] punctuation

types :: S.Set String
types = S.fromList ["void", "char", "short", "int", "long", "float", "double", "bool"]

lexStringSingle :: String -> LexerResult
lexStringSingle (h:t)
    | isOperator h      = let (token, rest) = spanOperator (h:t)
                          in (Operator token, rest)
    | isPunctuation h   = (Punctuation [h], t)
    | C.isDigit h       = let (token, rest) = span Lexer.isNumber t
                          in (classifyNumberToken (h:token), rest)
    | Lexer.isLetter h  = let (token, rest) = span isIdentifier t
                          in (classifyLetterToken (h:token), rest)
    | C.isSpace h       = lexStringSingle $ eatWs t
    | otherwise         = (Invalid, t)
  where
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
    spanOperator :: [Char] -> (String, String)
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