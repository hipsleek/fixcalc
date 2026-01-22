-- | LoopInv: Build constraint abstractions and compute loop invariants via LFP
-- 
-- This tool:
-- 1. Converts C code to Imp syntax (constraint abstraction)
-- 2. Runs the imp tool which uses fixCalc to compute LFP
-- 3. Shows the result
--
module Main where

import System.Environment (getArgs)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import System.FilePath (takeBaseName, takeDirectory, (</>))

import Lexer (tokenize)
import Parser (parse)
import ImpEmit (emitImp)

main :: IO ()
main = do
    args <- getArgs
    case args of
        [inputFile] -> processFile inputFile
        _ -> showHelp

showHelp :: IO ()
showHelp = do
    putStrLn "LoopInv - Loop Invariant Generator using fixCalc"
    putStrLn ""
    putStrLn "Usage: loopinv <input.c>"
    putStrLn ""
    putStrLn "This tool:"
    putStrLn "  1. Converts C code to Imp (constraint abstraction)"
    putStrLn "  2. Runs imp tool to compute loop invariants via LFP (fixCalc)"
    putStrLn "  3. Displays the computed result"

processFile :: FilePath -> IO ()
processFile inputFile = do
    putStrLn "================================================================"
    putStrLn "  LoopInv - Constraint Abstraction & LFP Computation"
    putStrLn "================================================================"
    putStrLn ""
    
    -- Step 1: Read and parse C code
    putStrLn $ "Input: " ++ inputFile
    putStrLn ""
    cCode <- readFile inputFile
    
    putStrLn "=== Original C Code ==="
    putStrLn cCode
    
    -- Step 2: Convert to Imp (constraint abstraction)
    putStrLn "=== Converting to Imp (Constraint Abstraction) ==="
    let tokens = tokenize cCode
    let ast = parse tokens
    let impCode = emitImp ast
    
    let impFile = takeDirectory inputFile </> takeBaseName inputFile ++ ".imp"
    writeFile impFile impCode
    putStrLn $ "Generated: " ++ impFile
    putStrLn ""
    putStrLn impCode
    
    -- Step 3: Run imp tool (which calls fixCalc for LFP)
    putStrLn "=== Running imp tool (LFP computation via fixCalc) ==="
    putStrLn ""
    
    let impBin = "./imp"
    (exitCode, stdout, stderr) <- readProcessWithExitCode impBin [impFile, "+infer"] ""
    
    case exitCode of
        ExitSuccess -> do
            putStrLn stdout
            
            -- Show the LFP result
            putStrLn "=== LFP Result (a.impt) ==="
            putStrLn ""
            imptContent <- readFile "a.impt"
            putStrLn imptContent
            
        ExitFailure code -> do
            putStrLn $ "Error: imp tool failed with code " ++ show code
            putStrLn "stderr:"
            putStrLn stderr
            putStrLn "stdout:"
            putStrLn stdout
