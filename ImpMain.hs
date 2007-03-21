module Main(main) where
import Fresh(initialState,runFS,putStrFS,getFlags,FS(..),addOmegaStr,getCPUTimeFS)
import ImpAST(Prog(..),printProgImpi,printProgC,printProgImpt)
import ImpConfig(defaultFlags,Flags(..),Postcondition(..),Prederivation(..),Heur(..))
import ImpParser(parse)
import ImpSugar(specialize,desugarInfer,desugarChecker)
import ImpSTypeChecker(sTypeCheck)
import ImpTypeChecker(typeCheckProg)
import ImpTypeInfer(typeInferProg)
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
      readFile file >>= \meth ->
      let methIncl = if isIndirectionIntArray flags then "#include \"PrimitivesIndir.imp\"\n\n"++meth else meth in
      getCPUTime >>= \tStartCPU ->
      parse methIncl >>= \prog -> 
      putStrLn ("Parsing...done!") >>
      compile flags prog >>= \_ ->
      getCPUTime >>= \tEndCPU -> 
      putStrLn ("Total CPU time: " ++ showDiffTimes tEndCPU tStartCPU)

compile:: Flags -> Prog -> IO Prog
compile flags prog = 
  if noInference flags then 
        runFS (initialState flags) (
            	desugarChecker prog >>= \dsgProg ->
              typeCheckProg dsgProg
        )
  else 
        runFS (initialState flags) (
              getFlags >>= \flags ->  
              sTypeCheck prog >>= \noWhileProg ->
              putStrFS "Simple type-checking...done!" >>
              desugarInfer noWhileProg >>= \dsgProg@(Prog _ dsgPrims dsgMeths) -> 
              -- Print C code without any bound-checks.
              --  printProgCAll dsgProg >>
              typeInferProg dsgProg >>= \infProg ->
              printProgImpi infProg >>
              getCPUTimeFS >>= \time1 -> specialize infProg >>= \specializedProg -> getCPUTimeFS >>= \time2 ->
              -- putStrFS ("Specialization...done in " ++ showDiffTimes time2 time1) >> 
              printProgC specializedProg >>
              printProgImpt specializedProg >>
              if (checkingAfterInference flags) then 
                  	desugarChecker specializedProg >>= \dsgProg ->
                    typeCheckProg dsgProg
              else 
                    return specializedProg
        )



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
  putStrLn "Usage: imp file [options]" >>
  putStrLn "Options:" >>
  putStrLn "  +indir:\t Enable array indirection." >>
  putStrLn "  +check:\t Infer the input file and type-check the result." >>
  putStrLn "  -m:<bound>:\t Use <bound>-disjunctive fixpoint, where <bound> is the maximum number of disjuncts." >>
  putStrLn "  <pre><post>:\t Use the <pre><post> combination of prederivation and postcondition. <pre> can be Post/Strong/Sel/Weak. <post> can be Strong/Weak." >>
  putStrLn "  -infer +check:\t Type-check the input file (written in impt)." >>
  putStrLn "  Similarity:\t Uses the Similarity-based heuristic" >>
  putStrLn "  Hausdorff:\t Uses the Hausdorff-based heuristic" >>
  putStrLn "Default arguments: -indir -check -m:5 PostStrong Similarity" >>
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
  "-indir" -> return $ Just prevFs{isIndirectionIntArray=False}
  "+indir" -> return $ Just prevFs{isIndirectionIntArray=True}
  "-check" -> return $ Just prevFs{checkingAfterInference=False} 
  "+check" -> return $ Just prevFs{checkingAfterInference=True}
  "-sep" -> return $ Just prevFs{separateFstFromRec=False}
  "+sep" -> return $ Just prevFs{separateFstFromRec=True}
  "-anno" -> return $ Just prevFs{useAnnotatedFixpoint=False}
  "+anno" -> return $ Just prevFs{useAnnotatedFixpoint=True}
  "-selHull" -> return $ Just prevFs{useSelectiveHull=False}
  "+selHull" -> return $ Just prevFs{useSelectiveHull=True}
  "-widenEarly" -> return $ Just prevFs{widenEarly=False}
  "+widenEarly" -> return $ Just prevFs{widenEarly=True}
  '-':'m':':':m -> return $ Just prevFs{fixFlags=(read m,snd (fixFlags prevFs))}
  "PostStrong" -> return $ Just prevFs{prederivation=PostPD,postcondition=StrongPost}
  "PostWeak" -> return $ Just prevFs{prederivation=PostPD,postcondition=WeakPost}
  "StrongStrong" -> return $ Just prevFs{prederivation=StrongPD,postcondition=StrongPost}
  "StrongWeak" -> return $ Just prevFs{prederivation=StrongPD,postcondition=WeakPost}
  "SelStrong" -> return $ Just prevFs{prederivation=SelectivePD,postcondition=StrongPost}
  "SelWeak" -> return $ Just prevFs{prederivation=SelectivePD,postcondition=WeakPost}
  "WeakStrong" -> return $ Just prevFs{prederivation=WeakPD,postcondition=StrongPost}
  "WeakWeak" -> return $ Just prevFs{prederivation=WeakPD,postcondition=WeakPost}
  "Similarity" -> return $ Just prevFs{fixFlags=(fst (fixFlags prevFs),SimilarityHeur)}
  "Hausdorff" -> return $ Just prevFs{fixFlags=(fst (fixFlags prevFs),HausdorffHeur)} 
  "-infer" -> return $ Just prevFs{noInference=True}
  '-':'o':':':file -> return $ Just prevFs{outputFile=file}
  _ -> 
    putStrLn ("imp: unrecognised flag: " ++ arg) >>
    showHelpMessage