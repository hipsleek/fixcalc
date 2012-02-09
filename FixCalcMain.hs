module Main(main) where
import FixCalcParser(parse)
import ImpConfig(defaultFlags,Flags(..),Hull(..))
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
    Just (file,flags) ->
      readFile file >>= \fileContents ->
      getCPUTime >>= \tStartCPU ->
      parse fileContents flags >>
      getCPUTime >>= \tEndCPU ->
      --putStrLn ("Total CPU time: " ++ showDiffTimes tEndCPU tStartCPU)
      putStrLn ("")

processCmdLine:: [String] -> IO (Maybe (String,Flags))
processCmdLine cmdLine = 
  case cmdLine of
    [] -> showHelpMessage
    ["--help"] -> showHelpMessage
    (source:args) -> 
--      putStrLn ("Default flags: "++show defaultFlags) >>
      allArgs defaultFlags args >>= \allA ->
      case allA of
        Nothing -> return Nothing
        Just flags ->
--          putStrLn ("CmdLine flags: "++show flags) >>
          return (Just (source,flags))

showHelpMessage = 
  putStrLn "Usage: fixcalc file [options]" >>
  putStrLn "Options:" >>
  putStrLn "  -club:<lub>:\t Use the conjunctive lub operator <lub>, where <lub> can be Hull or ConvexHull." >>
  putStrLn "Default arguments: -club:Hull" >>
  return Nothing

allArgs:: Flags -> [String] -> IO (Maybe Flags)
allArgs flags [] = return (Just flags)
allArgs flags (a:args) = 
  oneArg flags a >>= \one ->
  case one of
    Nothing -> return Nothing
    Just newFlags -> (allArgs newFlags args)

oneArg:: Flags -> String -> IO (Maybe Flags)
oneArg prevFs arg = case arg of
  "-club:Hull" ->       return $ Just prevFs{whatHull=Hull}
  "-club:ConvexHull" -> return $ Just prevFs{whatHull=ConvexHull}
  '-':'v':':':level ->  return $ Just prevFs{showDebugMSG=read level}
  _ -> 
    putStrLn ("imp: unrecognised flag: " ++ arg) >>
    showHelpMessage

