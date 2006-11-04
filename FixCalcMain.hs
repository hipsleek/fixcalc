module Main(main) where
import FixCalcParser(parse)
import MyPrelude
------------------------------------------
import Numeric(fromRat,showFFloat)
import System(getArgs)
import System.IO(hFlush,stdout)
import System.CPUTime(getCPUTime)
import System.Time(getClockTime,diffClockTimes)


main :: IO ()
main = 
  getArgs >>= \cmdLine ->
  processCmdLine cmdLine >>= \processedCmdLine ->
  case processedCmdLine of
    Nothing -> return ()
    Just file ->
      readFile file >>= \fileContents ->
      getCPUTime >>= \tStartCPU ->
      parse fileContents >>
      getCPUTime >>= \tEndCPU ->
      putStrLn ("Total CPU time: " ++ showDiffTimes tEndCPU tStartCPU)

processCmdLine:: [String] -> IO (Maybe String)
processCmdLine cmdLine = 
  case cmdLine of
    [] -> showHelpMessage
    ["--help"] -> showHelpMessage
    (source:args) -> 
      return (Just source)

showHelpMessage = 
  putStrLn "Usage: fixcalc file" >>
  return Nothing

