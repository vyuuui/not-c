{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module Main where

import CompilerShared
import CompilerShow
import qualified Data.Char as C
import Lexer
import Parser
import System.IO
import Validator
import Control.Arrow
import Generator
import Debug.Trace

dropAndCountComment :: String -> Int -> (String, Int)
dropAndCountComment (h1:h2:t) count
    | h1 == '*' && h2 == '/' = (t, count + 2)
    | otherwise              = dropAndCountComment (h2:t) (count + 1)
dropAndCountComment ls count = ("", count + length ls)

printError :: String -> FailureInfo -> IO ()
printError progStr FailureInfo {failReason = failMsg, failRegion = (start, end), failLocation = fLoc} = do
    let realEnd = end + length (takeWhile (/='\n') (drop end (take fLoc progStr)))
        (lineNum0, colNum0, str0) = findMessage progStr start realEnd (1, 1, "")
        nextStart = removeWhitespace str0 0
        (lineNum1, colNum1, str1) = findMessage str0 nextStart (length str0) (lineNum0, colNum0, "")
    putStrLn ("Error on line " ++ show lineNum1 ++ " column " ++ show colNum1 ++ " in statement:\n>\t" ++ str1 ++ "\n\n" ++ failMsg)
  where
    removeWhitespace :: String -> Int -> Int
    removeWhitespace (h1:h2:t) start
        | h1 == '/' && h2 == '/' = uncurry removeWhitespace (second (+start) (dropAndCount (/='\n') t))
        | h1 == '/' && h2 == '*' = uncurry removeWhitespace (dropAndCountComment (h1:h2:t) start)
        | C.isSpace h1           = uncurry removeWhitespace (second (+start) (dropAndCount C.isSpace (h1:h2:t)))
        | otherwise              = start
    removeWhitespace [h]   start = if C.isSpace h then start + 1 else start
    removeWhitespace []    start = start

    findMessage :: String -> Int -> Int -> (Int, Int, String) -> (Int, Int, String) 
    findMessage (h:t) start end (curLine, curCol, curStr) = do
        if end <= 0
        then (curLine, curCol, curStr)
        else
            if start <= 0
            then findMessage t 0 (end - 1) (curLine, curCol, curStr ++ [h])
            else do
                let newLine = if h == '\n' then curLine + 1 else curLine
                    newCol = if h == '\n' then 1 else curCol + 1
                findMessage t (start - 1) (end - 1) (newLine, newCol, "")
    findMessage [] start end (curLine, curCol, curStr) =
        (curLine, curCol, curStr)


validateAndPrint :: String -> IO ()
validateAndPrint file = do
    contents <- readFile file
    prog <- case parseProg contents of
        Right p -> return p
        Left msg -> do
           printError contents msg
           return ([], [])
    let res = validateProgram prog
    case res of
        Left msg      -> printError contents msg
        Right (t, s)  -> mapM_ print t

generateAndPrint :: String -> IO ()
generateAndPrint file = do
    contents <- readFile file
    prog <- case parseProg contents of
         Right p -> return p
         Left msg -> do
             printError contents msg
             return ([], [])
    let res = validateProgram prog
    case res of
        Left msg   -> printError contents msg
        Right prog -> 
            let (asm, globs) = generateProgram prog 
            in putStrLn (concatMap showFunction asm) >> putStr (showGlobals globs)

generateAndWrite :: String -> String -> IO ()
generateAndWrite srcFile destFile = do
    contents <- readFile srcFile
    prog <- case parseProg contents of
         Right p -> return p
         Left msg -> do
             printError contents msg
             return ([], [])
    let res = validateProgram prog
    case res of
        Left msg      -> printError contents msg
        Right prog  -> do
            let (asm, globs) = generateProgram prog 
                asmStr = concatMap showFunction asm
                globStr = showGlobals globs
            writeFile destFile (asmStr ++ globStr)

main :: IO ()
main = return ()
