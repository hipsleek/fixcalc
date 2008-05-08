-- #ignore-exports
module Main(main) where
import Fresh(initialState,runFS,putStrFS,getFlags,FS(..),getCPUTimeFS)
import ImpAST(Prog(..),printProgImpi,printProgC,printProgImpt)
import ImpConfig(defaultFlags,Flags(..),Postcondition(..),Prederivation(..),Heur(..),Hull(..))
import ImpParser(parse)
import ImpSugar(specialize,desugarInfer,desugarChecker)
import ImpSTypeChecker(sTypeCheck)
import ImpTypeChecker(typeCheckProg)
import ImpTypeInfer(typeInferProg)
import MyPrelude
------------------------------------------
import System(getArgs)
import System.CPUTime(getCPUTime)


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
  putStrLn "  -m:<bound>\t\t Use <bound>-disjunctive fixpoint, where <bound> is the maximum number of disjuncts." >>
  putStrLn "  -club:<lub>\t\t Use the conjunctive lub operator <lub>, where <lub> can be Hull or ConvexHull." >>
  putStrLn "  -dlub:<lub>\t\t Use the disjunctive lub operator <lub>, where <lub> can be Similarity, Hausdorff or Interactive." >>
  putStrLn "   Similarity\t\t Use the Planar affinity-based heuristic [ASIAN'06]." >>
  putStrLn "   Hausdorff\t\t Use the Hausdorff-based heuristic [Sriram et al-SAS'06]." >>
  putStrLn "   Interactive\t\t Allow user to specify interactively which disjuncts to combine, and revert to Similarity-based heuristic when unspecified." >>
--  putStrLn "  <pre><post>\t Use the <pre><post> combination of prederivation and postcondition. <pre> can be Post/Strong/Sel/Weak. <post> can be Strong/Weak." >>
--  putStrLn "  +indir\t Enable array indirection." >>
--  putStrLn "  +check\t Infer the input file and type-check the result." >>
  putStrLn "  -infer +check\t\t Type-check the input file (written in impt format)." >>
  putStrLn "  +individual\t\t Enable tracing of individual bug conditions." >>
  putStrLn "  -v:<level>\t\t Be verbose, where <level> is the verbosity level (0, 1 or 2)." >>
  putStrLn "   0\t\t\t Do not show any fixpoint messages." >>
  putStrLn "   1\t\t\t Show only loss-of-precision messages." >>
  putStrLn "   2\t\t\t Show loss-of-precision and hull/widening messages." >>
  putStrLn "Default arguments: -m:5 -club:Hull -dlub:Similarity -individual -v:0" >>
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
  "-indir" ->       return $ Just prevFs{isIndirectionIntArray=False}
  "+indir" ->       return $ Just prevFs{isIndirectionIntArray=True}
  "-check" ->       return $ Just prevFs{checkingAfterInference=False} 
  "+check" ->       return $ Just prevFs{checkingAfterInference=True}
  "-sep" ->         return $ Just prevFs{separateFstFromRec=False}
  "+sep" ->         return $ Just prevFs{separateFstFromRec=True}
  "-anno" ->        return $ Just prevFs{useAnnotatedFixpoint=False}
  "+anno" ->        return $ Just prevFs{useAnnotatedFixpoint=True}
  "-selHull" ->     return $ Just prevFs{useSelectiveHull=False}
  "+selHull" ->     return $ Just prevFs{useSelectiveHull=True}
  "-widenEarly" ->  return $ Just prevFs{widenEarly=False}
  "+widenEarly" ->  return $ Just prevFs{widenEarly=True}
  '-':'m':':':m ->  return $ Just prevFs{fixFlags=(read m,snd (fixFlags prevFs))}
  "PostStrong" ->   return $ Just prevFs{prederivation=PostPD,postcondition=StrongPost}
  "PostWeak" ->     return $ Just prevFs{prederivation=PostPD,postcondition=WeakPost}
  "StrongStrong" -> return $ Just prevFs{prederivation=StrongPD,postcondition=StrongPost}
  "StrongWeak" ->   return $ Just prevFs{prederivation=StrongPD,postcondition=WeakPost}
  "SelStrong" ->    return $ Just prevFs{prederivation=SelectivePD,postcondition=StrongPost}
  "SelWeak" ->      return $ Just prevFs{prederivation=SelectivePD,postcondition=WeakPost}
  "WeakStrong" ->   return $ Just prevFs{prederivation=WeakPD,postcondition=StrongPost}
  "WeakWeak" ->     return $ Just prevFs{prederivation=WeakPD,postcondition=WeakPost}
  "+individual" ->  return $ Just prevFs{traceIndividualErrors=True}
  "-individual" ->  return $ Just prevFs{traceIndividualErrors=False}
  "-infer" ->       return $ Just prevFs{noInference=True}
  "-club:Hull" ->   return $ Just prevFs{whatHull=Hull}
  "-club:ConvexHull" -> return $ Just prevFs{whatHull=ConvexHull}
  "-dlub:Similarity" -> return $ Just prevFs{fixFlags=(fst (fixFlags prevFs),SimilarityHeur)}
  "-dlub:Hausdorff" -> return $ Just prevFs{fixFlags=(fst (fixFlags prevFs),HausdorffHeur)} 
  "-dlub:Interactive" -> return $ Just prevFs{fixFlags=(fst (fixFlags prevFs),SimInteractiveHeur),showDebugMSG=2} 
  '-':'v':':':level -> 
                    case snd (fixFlags prevFs) of
                      SimInteractiveHeur -> return $ Just prevFs{showDebugMSG=2}
                      _ -> return $ Just prevFs{showDebugMSG=read level}
  '-':'o':':':file -> return $ Just prevFs{outputFile=file}
  _ -> 
    putStrLn ("imp: unrecognised flag: " ++ arg) >>
    showHelpMessage