module Lexer ( lexStringSingle ) where

import CompilerShared
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Char as C
import System.IO
import Debug.Trace
import Control.Arrow
import Data.Tuple (swap)

type LexerResult = (Token, Int, String)

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

dropAndCount :: (a -> Bool) -> [a] -> ([a], Int)
dropAndCount fn = span fn >>> first (arr length) >>> swap

lexStringSingle :: TypeEnv -> String -> LexerResult
lexStringSingle env str = lexStringSingleHelper env str 0
  where
    lexStringSingleHelper :: TypeEnv -> String -> Int -> LexerResult
    lexStringSingleHelper env str@[h1] numParsed = lexStringNoComment env str numParsed
    lexStringSingleHelper _ [] numParsed         = (Eof, numParsed, [])
    lexStringSingleHelper env str@(h1:h2:t) numParsed
        | h1 == '/' && h2 == '/' = uncurry (lexStringSingleHelper env) $ second (+(numParsed + 2)) (dropAndCount (/='\n') t) 
        | h1 == '/' && h2 == '*' = uncurry (lexStringSingleHelper env) (findCommentEnd t (numParsed + 2))
        | otherwise              = lexStringNoComment env str numParsed
      where
        findCommentEnd :: String -> Int -> (String, Int)
        findCommentEnd (h1:h2:t) numParsed
            | h1 == '*' && h2 == '/' = (t, numParsed + 2)
            | otherwise              = findCommentEnd (h2:t) $ numParsed + 1
    lexStringNoComment :: TypeEnv -> String -> Int -> LexerResult
    lexStringNoComment env str2@(h:t) numParsed
        | isOperatorChar h      = lexOperator str2 numParsed
        | isPunctuationChar h   = (Punctuation [h], numParsed + 1, t)
        | C.isDigit h           = let (token, rest) = span Lexer.isNumber t
                                      totalParsed = numParsed + length token + 1
                                  in  (classifyNumberToken (h:token), totalParsed, rest)
        | isLetterChar h        = let (token, rest) = span isIdentifierChar t
                                      totalParsed = numParsed + length token + 1
                                  in  (classifyLetterToken (h:token) env, totalParsed, rest)
        | C.isSpace h           = uncurry (lexStringSingleHelper env) $ second (+numParsed) (dropAndCount C.isSpace (h:t))
        | h == '"'              = lexStringConstant t numParsed
        | otherwise             = (Invalid, numParsed, t)
      where
        lexStringConstant :: String -> Int -> LexerResult
        lexStringConstant str numParsed = tryAppendStr $ until endingQuote buildString ("", numParsed, str)
          where
            endingQuote (_, _, h:t) = h == '"'
            endingQuote (_, _, []) = True
            buildString (lhs, numParsed, h1:h2:t)
                | h1 == '\\' && h2 == 'n' = (lhs ++ ['\n'], numParsed + 2, t)
                | h1 == '\\' && h2 == 't' = (lhs ++ ['\t'], numParsed + 2, t)
                | h1 == '\\' && h2 == 'r' = (lhs ++ ['\r'], numParsed + 2, t)
                | h1 == '\\' && h2 == '"' = (lhs ++ ['"'], numParsed + 2, t)
                | otherwise               = (lhs ++ [h1], numParsed + 1, h2:t)
            buildString (lhs, numParsed, [h]) = (lhs ++ [h], numParsed + 1, t)
            buildString (lhs, numParsed, [])  = (lhs, numParsed + 1, "")
            tryAppendStr (buildStr, numParsed, _:t) = (Constant $ StringConstant buildStr, numParsed, t)
            tryAppendStr (_, numParsed, rest) = (Invalid, numParsed, rest)
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
        lexOperator :: String -> Int -> LexerResult
        lexOperator str numParsed
            | null longestMatch = (Invalid, numParsed, rest)
            | otherwise         = (Operator longestMatch, numParsed + length longestMatch, drop (length longestMatch) str)
          where
            checkStop (_, _, [])            = True
            checkStop (cur, _, rest)        = not (any (L.isPrefixOf cur) (S.toList operators))
            stepLex (cur, longest, rest) 
                | S.member newCur operators = (newCur, newCur, tail rest)
                | otherwise                 = (newCur, longest, tail rest)
              where
                newCur = cur ++ [head rest]
            (end, longestMatch, rest) = until checkStop stepLex ("", "", str)