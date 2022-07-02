module Main where

import CompilerShared
import CompilerShow
import Lexer
import Parser
import System.IO
import Validator

loadAndParse :: String -> IO Program
loadAndParse file = do
    handle <- openFile file ReadMode
    contents <- hGetContents handle
    case parseProg contents of
        Right prog -> return prog
        Left msg -> error ("Bad program nat! msg=" ++ msg)

validateAndPrint :: Program -> IO ()
validateAndPrint prog = do
    let res = validateProgram prog
    case res of
        Left msg ->      putStrLn msg
        Right (t, s)  -> do
            mapM_ print t


main :: IO ()
main = return ()
