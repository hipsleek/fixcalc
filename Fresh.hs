{- | 
  Provides a Monad to maintain the state of the analyzer.
  Mainly used for unique name generation.
-}
module Fresh where
import ImpConfig(Flags,outputFile)
import MyPrelude
------------------------------------------
import System.CPUTime(getCPUTime)
import System.IO.Unsafe(unsafePerformIO)
-------FS Fresh---------------------------
data St = MkState { 
  cnt :: Integer, -- ^Used for unique name generation.
  omegaStrs:: [String], -- ^Strings to be printed in the log file. Kept in reverse order, so that adding a string is fast (to the front of the list).
  flags:: Flags, -- ^ Set of flags read from the command-line.
  safePrimChecks:: Int,
  unsafePrimChecks:: Int,
  safeUserChecks:: Int,
  unsafeUserChecks:: Int
}

newtype FS a = FS (St -> IO (St,a))

instance Monad FS where
  -- return :: a -> FS a
  return a = FS (\st -> return (st, a))
  (FS a) >>= f = 
    FS (\st -> 
      (a st) >>= \(st', a') -> 
      let (FS b) = (f a') in 
      (b st') >>= \(st'',b') ->
      return (st'',b'))

instance Functor FS where
  -- fmap:: (a->b) -> FS a -> FS b
  fmap f (FS stFunction) = FS (\n -> stFunction n >>= \(n1,a) -> return (n1,f a))
	                    
runFS:: St -> FS a -> IO a
runFS state (FS a) = 
  a state >>= \(finalState,result) ->
  let strs = reverse (omegaStrs finalState) in
  let outFile = outputFile (flags finalState) ++ ".omega" in
  let str = concatSepBy "\n" strs in
  writeFile outFile str >>
  return result

initialState:: Flags -> St
initialState fs = MkState{cnt=0,omegaStrs=[],flags=fs, safePrimChecks=0, unsafePrimChecks=0, safeUserChecks=0, unsafeUserChecks=0}

fresh:: FS String
fresh = FS (\st -> return (st{cnt = (cnt st) + 1},"f_" ++ show (cnt st)))

freshVar:: FS String
freshVar = FS (\st -> return (st{cnt = (cnt st) + 1},"v_" ++ show (cnt st)))

freshLabel:: FS String
freshLabel = FS (\st -> return (st{cnt = (cnt st) + 1},"l_" ++ show (cnt st)))

takeFresh:: Int -> FS [String]
takeFresh 0 = return []
takeFresh n = fresh >>= \fsh -> 
  takeFresh (n-1) >>= \fshs -> return $ fsh:fshs

addOmegaStr:: String -> FS ()
addOmegaStr newStr = 
  FS (\st -> return (st{omegaStrs=(newStr:omegaStrs st)},()))

writeOmegaStrs:: FS ()
writeOmegaStrs = 
  getFlags >>= \flags ->
  let outFile = outputFile flags ++ ".omega" in
  getOmegaStrs >>= \strs ->
  let str = concatSepBy "\n" strs in
    FS (\st -> writeFile outFile str >> return (st,()))
  where
  getOmegaStrs:: FS [String]
  getOmegaStrs = FS (\st -> return (st,reverse (omegaStrs st)))

getFlags:: FS Flags
getFlags = FS (\st -> return (st,flags st))

incSafePrimChecks:: FS ()
incSafePrimChecks = FS (\st -> return (st{safePrimChecks = (safePrimChecks st) + 1},()))

getSafePrimChecks:: FS Int
getSafePrimChecks = FS (\st -> return (st,safePrimChecks st))

incUnsafePrimChecks:: FS ()
incUnsafePrimChecks = FS (\st -> return (st{unsafePrimChecks = (unsafePrimChecks st) + 1},()))

getUnsafePrimChecks:: FS Int
getUnsafePrimChecks = FS (\st -> return (st,unsafePrimChecks st))

incSafeUserChecks:: FS ()
incSafeUserChecks = FS (\st -> return (st{safeUserChecks = (safeUserChecks st) + 1},()))

getSafeUserChecks:: FS Int
getSafeUserChecks = FS (\st -> return (st,safeUserChecks st))

incUnsafeUserChecks:: FS ()
incUnsafeUserChecks = FS (\st -> return (st{unsafeUserChecks = (unsafeUserChecks st) + 1},()))

getUnsafeUserChecks:: FS Int
getUnsafeUserChecks = FS (\st -> return (st,unsafeUserChecks st))

putStrFS:: String -> FS ()
putStrFS str = FS (\st -> putStrLn str >> return (st,()))

putStrNoLnFS:: String -> FS ()
putStrNoLnFS str = FS (\st -> putStr str >> return (st,()))

getCPUTimeFS:: FS Integer
getCPUTimeFS = FS (\st -> getCPUTime >>= \t -> return (st,t))

---------For Debugging-------------------
---- empty state of the monad contains counter 0 and empty program
--emptyST:: St
--emptyST = MkState{cnt=0,prog=Prog [] []}
--
---- uses the empty state to run the Monad function
--runFSEmpty:: Show a => FS a -> a
--runFSEmpty (FS a) = snd (a emptyST)

-------Example: starting FS Monad------
--type Prog = String
--typeCheck:: Prog -> String
--typeCheck p = runFS MkState{cnt=0,prog=p} _typeCheck
--  where
--  _typeCheck :: FS String
--  _typeCheck = getProg >>= \p -> 
--    fresh >>= \f -> 
--    return $ f

{- freshTy with do mapM and fmap
freshTy:: AnnTy -> FS AnnTy
freshTy ty = case ty of
  AnnPrimTy (ty,_) -> fresh >>= \fsh -> return $ AnnPrimTy (ty,Just fsh)
  AnnArrTy (ty,_) annPrims -> do
    fsh <- fresh
    fshTys <-
      mapM (\ty -> 
        fmap (\(AnnPrimTy t) -> t) (freshTy (AnnPrimTy ty))
      ) annPrims
    return $ AnnArrTy (ty,Just (AnnElem fsh)) fshTys
  _ -> error $ "what other type to freshen up besides AnnPrimTy and AnnArrTy?"
-}

{- freshTy without do notation
freshTy:: AnnTy -> FS AnnTy
freshTy ty = case ty of
  AnnPrimTy (ty,_) -> fresh >>= \fsh -> return $ AnnPrimTy (ty,Just fsh)
  AnnArrTy (ty,_) annPrims ->
    fresh >>= \fsh -> 
      mapM (\(ty,_) -> fresh >>= \fsh -> return (ty,Just fsh)) annPrims >>= \fshTys ->
        return $ AnnArrTy (ty,Just (AnnElem fsh)) fshTys
-}
