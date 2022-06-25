module Lexer ( lexStringSingle ) where

import CompilerShared
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Char as C
import System.IO
import Debug.Trace

type LexerResult = (Token, String)

operators :: S.Set String
operators = S.fromList ["=", "+=", "-=", "*=", "/=", "%=", "||", "&&", "==", "!=", "<", "<=", ">", ">=", "+", "-", "*", "/", "%", "!", "&", "->", "."]
control :: S.Set String
control = S.fromList ["if", "else", "for", "while", "return", "break", "continue"]
punctuation :: S.Set String
punctuation = S.fromList ["(", ")", "{", "}", ",", ";", "[", "]"]
keyword :: S.Set String
keyword = S.fromList ["struct"]

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
isPunctuationChar :: Char -> Bool
isPunctuationChar h = S.member [h] punctuation

lexStringNoComment :: TypeEnv -> String -> LexerResult
lexStringNoComment env str2@(h:t) 
    | isOperatorChar h      = lexOperator str2
    | isPunctuationChar h   = (Punctuation [h], t)
    | C.isDigit h           = let (token, rest) = span Lexer.isNumber t
                               in (classifyNumberToken (h:token), rest)
    | isLetterChar h        = let (token, rest) = span isIdentifierChar t
                               in (classifyLetterToken (h:token) env, rest)
    | C.isSpace h           = lexStringSingle env (eatWs t)
    | h == '"'              = lexStringConstant t
    | otherwise             = (Invalid, t)
  where
    lexStringConstant :: String -> LexerResult
    lexStringConstant str
        = tryAppendStr $ until endingQuote buildString ("", str)
      where
        endingQuote (_, h:t) = h == '"'
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
    eatWs = dropWhile C.isSpace
    classifyNumberToken str 
        | '.' `elem` str = Constant $ FloatConstant (read str :: Float)
        | otherwise      = Constant $ IntConstant (read str :: Int)
    classifyLetterToken str env
        | str == "true"            = Constant $ BoolConstant True
        | str == "false"           = Constant $ BoolConstant False
        | S.member str control     = Control str
        | S.member str punctuation = Punctuation str
        | S.member str keyword     = Keyword str
        | otherwise                = Identifier str
    lexOperator :: String -> LexerResult
    lexOperator str
        | null longestMatch = (Invalid, rest)
        | otherwise         = (Operator longestMatch, drop (length longestMatch) str)
      where
        checkStop (_, _, [])            = True
        checkStop (cur, _, rest)        = not (any (L.isPrefixOf cur) (S.toList operators))
        stepLex (cur, longest, rest) 
            | S.member newCur operators = (newCur, newCur, tail rest)
            | otherwise                 = (newCur, longest, tail rest)
          where
            newCur = cur ++ [head rest]
        (end, longestMatch, rest) = until checkStop stepLex ("", "", str)

lexStringSingle :: TypeEnv -> String -> LexerResult
lexStringSingle env str@(h1:h2:t)
    | h1 == '/' && h2 == '/' = lexStringSingle env (tail $ dropWhile (/='\n') t) 
    | h1 == '/' && h2 == '*' = lexStringSingle env (findCommentEnd t)
    | otherwise              = lexStringNoComment env str
  where
    findCommentEnd :: String -> String
    findCommentEnd (h1:h2:t)
      | h1 == '*' && h2 == '/' = t
      | otherwise              = findCommentEnd (h2:t)
lexStringSingle env str@[h1] = lexStringNoComment env str
lexStringSingle _ []         = (Eof, [])