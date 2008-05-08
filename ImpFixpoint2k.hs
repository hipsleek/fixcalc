{- |Fixed point analysis that is used in (1) bug discovery from "ImpOutInfer", (2) array bound check elimination from "ImpTypeInfer" and 
  (3) FixedPoint Calculator from "FixCalc".
-}
module ImpFixpoint2k(
  fixpoint2k, 
  bottomUp2k,   
  topDown2k,
  fixTestBU,
  fixTestTD,
  getOneStep,
  subrec,
  combSelHull,  -- |Function re-exported from "ImpHullWiden".
  getDisjuncts, -- |Function re-exported from "ImpHullWiden".
  widen         -- |Function re-exported from "ImpHullWiden".
) where
import Fresh(FS,fresh,takeFresh,addOmegaStr,getFlags,putStrFS,getCPUTimeFS)
import ImpAST
import ImpConfig(useSelectiveHull,widenEarly,showDebugMSG,Heur(..),fixFlags,FixFlags)
import ImpFormula(debugApply,noChange,simplify,subset,recTheseQSizeVars,pairwiseCheck,equivalent)
import ImpHullWiden(widen,widenOne,combHull,combSelHull,countDisjuncts,getDisjuncts,DisjFormula)
import MyPrelude
---------------
import List((\\),nub)
import Maybe(catMaybes)
import Monad(when,mapAndUnzipM)

maxIter::Int
maxIter = 10

{- |Given CAbst, returns two results of fixpoint computation: a postcondition and a transitive invariants.
    This function uses the old fixpoint procedure if simulateOldFixpoint returns True. Only in this case the first argument is used. -}
fixpoint2k:: MethDecl -> RecPost -> FS (Formula,Formula)
-- requires: CAbst has ex-quantified variables that are all different
-- otherwise simplifyRecPost is incorrect: (ex x: x=1 & (ex x: x=2)) is transformed to (ex x: (ex x: (x=1 & x=2)))
fixpoint2k m recPost@(RecPost mn f (i,o,byval)) =
  if simulateOldFixpoint then fixpoint m recPost
  else
  if not (fst (testRecPost recPost)) then error ("assertion failed in fixpoint2k") 
  else
      getFlags >>= \flags -> let fixFlags1 = fixFlags flags in
--            addOmegaStr("CAbst:="++showSet f) >>
--            bottomUp2k recPost fixFlags1 fFalse >>= \(postNoSimpl,_) ->
--            putStrFS("OK:="++showSet postNoSimpl) >>
--      newSimplifyEntireRecPost recPost >>= \sRecPost@(RecPost _ sf _) ->
      let sRecPost@(RecPost _ sf _) = recPost in
--            addOmegaStr("SimplCAbst:="++showSet sf) >>
---- Bottom-Up fixpoint
      addOmegaStr ("\n# " ++ show sRecPost) >> addOmegaStr ("#\tstart bottomUp2k") >>
      getCPUTimeFS >>= \time1 -> 
      bottomUp2k sRecPost fixFlags1 fFalse >>= \(post,cntPost) ->
      addOmegaStr ("# Post" ++ show (fst fixFlags1) ++ ":=" ++ showSet post) >> 
      addOmegaStr ("#\tend bottomUp2k" ++ "\n") >>
      getCPUTimeFS >>= \time2 -> 
--      putStrFS("OK:=" ++ showSet post) >>
--      putStrFS ("    BU " ++ show cntPost ++ "iter: " ++ showDiffTimes time2 time1)>>
---- Top-Down fixpoint
      topDown2k sRecPost (1,SimilarityHeur) fTrue >>= \(inv,cntInv) ->
      getCPUTimeFS >>= \time3 -> 
      addOmegaStr ("# Inv:=" ++ showRelation (i,recTheseQSizeVars i,inv) ++ "\n") >>
--      putStrFS("TransInv:=" ++ showRelation(i,recTheseQSizeVars i,inv)) >>
--      putStrFS("    TD " ++ show cntInv ++ "iter: " ++ showDiffTimes time3 time2) >>
      return (post,inv)
     
----Bottom-Up fixpoint
-- 3rd widening strategy + general selHull
bottomUp2k:: RecPost -> FixFlags -> Formula -> FS (Formula,Int)
-- ^Given CAbst, fixpoint flags and an initial formula F (usually False), returns an approximation 
-- for the least-fixed point of CAbst and the number of iterations in which the result is obtained.
-- This computation is also named bottom-up fixpoint.
bottomUp2k recpost (m,heur) initFormula = 
  getFlags >>= \flags -> 
  subrec recpost initFormula >>= \f1 -> simplify f1 >>= \f1r ->
  addOmegaStr ("# F1:="++showSet f1r) >>
    subrec recpost f1r >>= \f2 -> simplify f2 >>= \f2r -> 
    addOmegaStr ("# Fx:="++showSet f2) >>
    addOmegaStr ("# F2:="++showSet f2r) >>
  subrec recpost f2r >>= \f3 ->  simplify f3 >>= \f3r -> 
  addOmegaStr ("# F3:="++showSet f3r) >>
  pairwiseCheck f3r >>=  \pwF3 -> let mdisj = min m (countDisjuncts pwF3) in
  when (showDebugMSG flags >=1) (putStrFS("Deciding a value for m: limit from command line (m="++show m++"), from heuristic (m=" ++ show (countDisjuncts pwF3) ++ ") => m="++ show mdisj)) >>
  combSelHull (mdisj,heur) (getDisjuncts f3r) f1r >>= \s3 ->
  iterBU2k recpost (mdisj,heur) f3r s3 f1r 4 >>= \res ->
  return res
    
iterBU2k:: RecPost -> FixFlags -> Formula -> DisjFormula -> Formula -> Int -> FS (Formula,Int)
-- requires: scrt, sbase are in conjunctive form
iterBU2k recpost (m,heur) fcrt scrt fbase cnt =
  if (cnt>maxIter) then return (fTrue,-1)
  else
-- 3nd widening strategy: iterate using scrt (fcrt is not used anymore)
    subrec recpost (Or scrt) >>= \fn -> simplify fn >>= \fnext ->
    addOmegaStr ("# F"++ show cnt ++ ":="++showSet fnext) >>
    combSelHull (m,heur) (getDisjuncts fnext) fbase >>= \fnextHMany ->
    widen heur (scrt,fnextHMany) >>= \snext ->
    fixTestBU recpost (Or snext) >>= \fixok ->
    if fixok then pairwiseCheck (Or snext) >>= \pw -> return (pw,cnt)
    else iterBU2k recpost (m,heur) fnext snext fbase (cnt+1)  
    
-- iterates starting with scrt (downwards if scrt is Reductive point; upwards if scrt is Extensive point)
-- iterates until maxIter (no termination criterion)
iterate2k:: RecPost -> FixFlags -> DisjFormula -> Int -> FS (Formula,Int)
-- requires: scrt is in conjunctive form
iterate2k recpost (m,heur) scrt cnt =
    subrec recpost (Or scrt) >>= \fn -> simplify fn >>= \fnext ->
    addOmegaStr ("# F"++ show cnt ++ ":="++showSet fnext) >>
    combSelHull (m,heur) (getDisjuncts fnext) undefined >>= \snext ->
    fixTestBU recpost (Or snext) >>= \fixok -> 
--    when (not fixok) (putStrFS ("not a Reductive point at "++show cnt)) >>
--    putStrFS("    Post" ++ show cnt ++ ":=" ++ showSet (Or snext)) >>
    if (cnt>maxIter) then pairwiseCheck (Or snext) >>= \pw -> return (pw,cnt)
    else iterate2k recpost (m,heur) snext (cnt+1)  
    
{- |Given CAbst and F, returns True if F is a reductive point of CAbst: CAbst(F) => F. -}
fixTestBU:: RecPost -> Formula -> FS Bool
fixTestBU recpost candidate = 
    addOmegaStr ("#\tObtained postcondition?") >>
    subrec recpost candidate >>= \fnext -> 
    subset fnext candidate

subrec :: RecPost -> Formula -> FS Formula
-- ^Given CAbst and F, returns CAbst(F). 
-- More precisely: subrec (RecPost foo (...foo(f0,f1)...) ([i,s],_,[i])) (i<s) = (...(f0<f1 && PRMf0=f0)...)
-- Function subrec is related to ImpOutInfer.replaceLblWithFormula.
subrec (RecPost formalMN f1 (formalI,formalO,qsvByVal)) f2 =
  subrec1 f1 f2
 where 
 subrec1:: Formula -> Formula -> FS Formula
 subrec1 f g = case f of 
    And fs ->  mapM (\x -> subrec1 x g) fs >>= \res -> return (And res)
    Or fs -> mapM (\x -> subrec1 x g) fs >>= \res -> return (Or res)
    Exists vars ff -> subrec1 ff g >>= \res -> return (Exists vars res)
    GEq us -> return f
    EqK us -> return f
    AppRecPost actualMN actualIO ->
      if not (formalMN==actualMN) then
        error "subrec: mutual recursion detected" 
      else if not (length (formalI++formalO) == length actualIO) then
        error $ "subrec: found different no of QSVs for CAbst:\n " ++ show f
      else
        let rho = zip (formalI++formalO) actualIO in
        debugApply rho g >>= \rhoG ->
        return $ fAnd [rhoG,noChange qsvByVal]
    _ -> error ("unexpected argument: "++show f)

-----Top Down fixpoint
-- 2nd widening strategy + general selHull
topDown2k:: RecPost -> FixFlags -> Formula -> FS (Formula,Int)
-- ^Given CAbst, fixpoint flags and the postcondition formula F (usually True), returns a transitive
-- invariant and the number of iterations in which the result is obtained.
-- This computation is also named top-down fixpoint and is a generalization of the U+ transitive closure 
-- operator computed by Omega Calculator (see PEPM'00 paper for more details).
topDown2k recpost (m,heur) postFromBU = 
  getFlags >>= \flags -> 
  getOneStep recpost postFromBU >>= \oneStep@(ins,recs,g1) ->
  addOmegaStr ("#\tG1:="++showRelation oneStep) >>
  compose g1 oneStep >>= \gcomp ->
  pairwiseCheck (fOr [g1,gcomp]) >>= \g2 -> 
  addOmegaStr ("#\tG2:="++showRelation (ins,recs,g2)) >>
  let mdisj = min m (countDisjuncts g2) in
--  when (showDebugMSG flags >=1) (putStrFS("Deciding a value for m: limit from command line (m="++show m++"), from heuristic (m=" ++ show (countDisjuncts g2) ++ ") => m="++ show mdisj)) >>
  combSelHull (mdisj,heur) (getDisjuncts g2) undefined >>= \disjG2 ->
  iterTD2k recpost (mdisj,heur) disjG2 oneStep 3

iterTD2k:: RecPost -> FixFlags -> DisjFormula -> Relation -> Int -> FS (Formula,Int)
iterTD2k recpost (m,heur) gcrt oneStep cnt = 
  if (cnt>maxIter) then return (fTrue,-1)
  else
    compose (Or gcrt) oneStep >>= \gcomp ->
    simplify (Or (getDisjuncts(thd3 oneStep)++getDisjuncts gcomp)) >>=  \gcompPlusOne ->
    addOmegaStr ("#\tG" ++ show (cnt) ++ " hulled to G" ++ show (cnt) ++ "r") >>
    combSelHull (m,heur) (getDisjuncts gcompPlusOne) undefined >>= \gnext ->
    widen heur (gcrt,gnext) >>= \gcrtW ->
    fixTestTD oneStep (Or gcrtW) >>= \fixok ->
    if fixok then return (Or gcrtW,cnt)
    else iterTD2k recpost (m,heur) gcrtW oneStep (cnt+1)

fixTestTD:: Relation -> Formula -> FS Bool
fixTestTD oneStep candidate = 
  compose candidate oneStep >>= \gcomp ->
  addOmegaStr ("#\tObtained invariant?") >> 
  subset (Or [gcomp,thd3 oneStep]) candidate 

compose:: Formula -> Relation -> FS (Formula)
compose gcrt (ins,recs,gbase) =
  takeFresh (length ins) >>= \freshies ->
  let freshQsvs = map (\fsh -> (SizeVar fsh,Unprimed)) freshies in
  let rhoRecsFsh = zip recs freshQsvs in
  let rhoInsFsh = zip ins freshQsvs in
  debugApply rhoRecsFsh gcrt >>= \conj1 -> 
  debugApply rhoInsFsh gbase >>= \conj2 ->
  let disj2 = fExists freshQsvs (And [conj1,conj2]) in
  return disj2
  
getOneStep:: RecPost -> Formula -> FS Relation
-- ^does not work correctly when postFromBU is different than the True formula. This problem is encountered for non-linear recursive function like quick_sort and msort.
-- Adding a strong postFromBU (which includes the checks) makes the resulting TransInv too strong (all rec-checks will be satisfied.
-- Possible solution: mark AppRecPost with a number in the order in which they appear in the source code.
-- ensures: (length ins) = (length recs)
getOneStep recPost@(RecPost mn f (i,o,_)) postFromBU =
  let recs = (recTheseQSizeVars i) in
  getRecCtxs recs (i++o) postFromBU f >>= \(_,recCtxs) ->
  let disjCtxRec = fExists o (fOr recCtxs) in
  simplify disjCtxRec >>= \oneStep ->
  return (i,recs,oneStep)

getRecCtxs:: [QSizeVar] -> [QSizeVar] -> Formula -> Formula -> FS (Formula,[Formula])
-- qsvs -> formula from cAbst -> postFromBU -> (general Ctx,recursive Ctxs)
getRecCtxs recs io postFromBU formula = case formula of
  And fs -> 
    mapAndUnzipM (\conjunct -> getRecCtxs recs io postFromBU conjunct) fs >>= \(genCtxs,recCtxss) ->
    let genCtx = fAnd genCtxs in
    let recCtxs = map (\recCtx -> fAnd [genCtx,recCtx])(concat recCtxss) in
    return (genCtx,recCtxs)
  Or fs -> 
    mapAndUnzipM (\conjunct -> getRecCtxs recs io postFromBU conjunct) fs >>= \(genCtxs,recCtxss) ->
    let genCtx = fOr genCtxs in
    let recCtxs = (concat recCtxss) in
    return (genCtx,recCtxs)
  Exists exQsv f -> 
    getRecCtxs recs io postFromBU f >>= \(genCtx,recCtxs) ->
    return (Exists exQsv genCtx,map (Exists exQsv) recCtxs)
  EqK ups -> return (formula,[])
  GEq ups -> return (formula,[])
  AppRecPost _ insouts ->
    let actualArgs = take (length recs) insouts in    
    let argsPairs = zip recs actualArgs in
-- Include postFromBU instead of fTrue
          let rhoFormalToActual = zipOrFail io insouts in
          debugApply rhoFormalToActual postFromBU >>= \post ->
    let eqs = map (\(f,a) -> EqK [Coef f 1,Coef a (-1)]) argsPairs in
    return (post,[fAnd eqs])

----------------------------------
--------Old fixpoint procedure----
----------------------------------
-- Below procedures use RecPost (instead of CAbst) as well as the rewritten fixpoint methods.
-- They should give same result as the old fixpoint
-- flags that can be used: widenEarly, selHull
simulateOldFixpoint = False

-- old version of the fixpoint procedure
fixpoint:: MethDecl -> RecPost -> FS (Formula,Formula)
fixpoint m recPost@(RecPost mn f (i,o,_)) =
---- BU fixpoint for non-simplified RecPost
      getCPUTimeFS >>= \time1 ->
      addOmegaStr ("\n# " ++ show recPost) >> addOmegaStr ("#\tstart bottomUp") >>
      bottomUp recPost >>= \(post,cntPost) ->
      addOmegaStr ("# Post:=" ++ showSet post) >> addOmegaStr ("#\tend bottomUp2k" ++ "\n") >> 
      putStrFS("    Post:=" ++ showSet post) >>
---- Statistics BU
      getCPUTimeFS >>= \time2 -> 
      putStrFS ("    BU " ++ show cntPost ++ "iter: " ++ showDiffTimes time2 time1) >>
---- TD fixpoint for simplified RecPost
      topDown recPost post >>= \(inv,cntInv) ->
      addOmegaStr ("# Inv:=" ++ showRelation (i,recTheseQSizeVars i,inv) ++ "\n") >>
      getCPUTimeFS >>= \time3 -> 
      putStrFS("    TD " ++ show cntInv ++ "iter: " ++ showDiffTimes time3 time2) >>
      return (post,inv)
   
-- old widening strategy + selHullBase
bottomUp:: RecPost -> FS (Formula,Int)
bottomUp recpost =
  subrec recpost fFalse >>= \f1 -> simplify f1 >>= \f1r ->
  addOmegaStr ("# F1:="++showSet f1r) >>
    subrec recpost f1r >>= \f2 -> simplify f2 >>= \f2r -> 
    addOmegaStr ("# F2:="++showSet f2r) >>
  subrec recpost f2r >>= \f3 -> simplify f3 >>= \f3r -> 
  addOmegaStr ("# F3:="++showSet f3r) >>
  getFlags >>= \flags -> 
  if useSelectiveHull flags then
    combSelHullBase (getDisjuncts f3r) f1r >>= \s4 ->
    iterBU recpost f3r s4 f1r 4
  else 
    combHull (getDisjuncts f3r) >>= \f3H ->
    iterBUConj recpost f3r f3H 4
  
iterBU:: RecPost -> Formula -> DisjFormula -> Formula -> Int -> FS (Formula,Int)
-- requires: elements of scrt are in conjunctive form
iterBU recpost fcrt scrt fbase cnt =
  if (cnt>maxIter) then return (fTrue,-1)
  else
    subrec recpost fcrt >>= \fn -> simplify fn >>= \fnext ->
    addOmegaStr ("# F"++ show cnt ++ ":="++showSet fnext) >>
    combSelHullBase (getDisjuncts fnext) fbase >>= \snext -> 
    widenOne (head scrt,head snext) >>= \fcrtWBase ->
    widenOne (head (tail scrt),head (tail snext)) >>= \fcrtWRec ->
    let fcrtW = Or [fcrtWRec,fcrtWBase] in
      fixTestBU recpost fcrtW >>= \fixok ->
      if fixok then return (fcrtW,cnt)
      else iterBU recpost fnext snext fbase (cnt+1)  

iterBUConj:: RecPost -> Formula -> Formula -> Int -> FS (Formula,Int)
-- requires: scrt is in conjunctive form
iterBUConj recpost fcrt scrt cnt =
  if (cnt>maxIter) then return (fTrue,-1)
  else
    subrec recpost fcrt >>= \fn -> simplify fn >>= \fnext ->
    addOmegaStr ("# F"++ show cnt ++ ":="++showSet fnext) >>
    combHull (getDisjuncts fnext) >>= \snext ->
    widenOne (scrt,snext) >>= \fcrtW ->
      fixTestBU recpost fcrtW >>= \fixok ->
      if fixok then return (fcrtW,cnt)
      else iterBUConj recpost fnext snext (cnt+1)  

combSelHullBase:: DisjFormula -> Formula -> FS DisjFormula
-- requires: disj represents the DNF-form of a formula f (Or fs)
-- ensures: (length res)=2
combSelHullBase disj base = 
  classify disj base >>= \(nonRec,rec) ->
  -- it should not happen that length nonRec==0 or length rec==0
  -- but it happens! for bsearch,mergesort,FFT
  (case length nonRec of {0 -> return fTrue; 1 -> return (head nonRec); _ -> combHull nonRec}) >>= \nonRecH ->
  (case length rec of {0 -> return fTrue; 1 -> return (head rec); _ -> combHull rec}) >>= \recH ->
  return [recH,nonRecH]
  where
  classify:: DisjFormula -> Formula -> FS (DisjFormula,DisjFormula)
  classify [] base = return ([],[])
  classify (f:fs) base = 
    subset base f >>= \subok -> 
    classify fs base >>= \(restNonRec,restRec) -> 
    if subok then return (f:restNonRec,restRec)
    else return (restNonRec,f:restRec)

-----Top Down fixpoint
topDown:: RecPost -> Formula -> FS (Formula,Int)
topDown recpost postFromBU = 
  getOneStep recpost postFromBU >>= \oneStep@(ins,recs,g1) ->
  addOmegaStr ("#\tG1:="++showRelation oneStep) >>
      compose g1 (ins,recs,g1) >>= \gcomp ->
      addOmegaStr ("#\tG2 hulled to G2r") >>
      combHull [g1,gcomp] >>= \g2 ->
      iterTD recpost g2 oneStep 3

iterTD:: RecPost -> Formula -> Relation -> Int -> FS (Formula,Int)
iterTD recpost gcrt oneStep cnt = 
  if (cnt>maxIter) then return (fTrue,-1)
  else
    compose gcrt oneStep >>= \gcomp ->
    addOmegaStr ("#\tG" ++ show (cnt) ++ " hulled to G" ++ show (cnt) ++ "r") >>
    combHull [gcrt,gcomp] >>= \gnext ->
    widenOne (gcrt,gnext) >>= \gcrtW ->
    fixTestTD oneStep gcrtW >>= \fixok ->
    if fixok then return (gcrtW,cnt)
    else iterTD recpost gnext oneStep (cnt+1)

{---------------------------------
--------NewSimplify RecPost----
----------------------------------
Step1: Replace AppRecPost with markers (m=0) and collect actual arguments
Step2: Simplify formula
Step3: Replace markers with AppRecPost
...
-}
--Occurrences of AppRecPost will be replaced by a (b=0) and a marker is returned: (b,AppRecPost insouts)
type Marker = (QSizeVar,Formula)

newSimplifyEntireRecPost:: RecPost -> FS RecPost
newSimplifyEntireRecPost recpost@(RecPost mn prmf oth@(_,_,qsvByVal)) = 
  let (prms,f) = (case prmf of {Exists prms f -> (prms,f);_ -> error("assertion failed in simplifyRecPost")}) in
  -- prms should be (primeTheseQSizeVars qsvByVal)
  newSimplifyWithAppRecPost f >>= \sF ->
  let entireRecPost = Exists prms sF in 
  return (RecPost mn entireRecPost oth)

newSimplifyWithAppRecPost:: Formula -> FS Formula
-- ^simplification of a formula that may contain an AppRecPost constructor.
-- This function is not used currently: it is unsafe, because Omega.simplify, when given a complex argument, may drop information about a marker.
newSimplifyWithAppRecPost f =
  putStrFS ("#####simplifyRecPost") >>
      addOmegaStr("1BefSimpl:="++showSet f) >>
  replaceAppRecPost f >>= \(markF,markAppRecPost,markArgs) ->
      addOmegaStr("2WithMark:="++showSet markF) >>
  simplify markF >>= \sMarkF ->
      addOmegaStr("3AftSimplWithMark:="++showSet sMarkF) >>
  let sF = fExists markArgs (replaceBackAppRecPost markAppRecPost sMarkF) in
      addOmegaStr("4AftSimpl:="++showSet sF) >>
  return sF
  where
  replaceAppRecPost:: Formula -> FS (Formula,[Marker],[QSizeVar])
  -- requires: formula is not mutually recursive
  replaceAppRecPost formula = case formula of
    And fs -> 
      mapM replaceAppRecPost fs >>= \results -> let (replFs,replPair,args) = unzip3 results in
      return (And replFs,concat replPair,concat args)
    Or fs -> 
      mapM replaceAppRecPost fs >>= \results -> let (replFs,replPair,args) = unzip3 results in
      return (Or replFs,concat replPair,concat args)
    Exists exQsvs f ->
      replaceAppRecPost f >>= \(replF,replPair,args) ->
      return (Exists exQsvs replF,replPair,args)
    GEq ups -> return (formula,[],[])
    EqK ups -> return (formula,[],[])
    -- goo(i1,j1) will be replaced by f_0=0 && f_1=i1 && f_2=i2
    -- the marker will be (f_0,goo(f_1,f_2))
    AppRecPost _ insouts ->
      fresh >>= \mark -> 
      let markQsv = (SizeVar mark, Unprimed) in
      let markEq = EqK [Coef markQsv 1,Const 0] in --add a marker
      takeFresh (length insouts) >>= \args ->
      let argsQsv = map (\arg -> (SizeVar arg,Unprimed)) args in
      let argsEq = map (\(i,fsh) -> EqK [Coef i 1,Coef fsh (-1)]) (zip insouts argsQsv) in 
      debugApply (zip insouts argsQsv) formula >>= \markFormula ->
      return (fAnd (markEq:argsEq),[(markQsv,markFormula)],argsQsv)

replaceBackAppRecPost:: [Marker] -> Formula -> Formula
replaceBackAppRecPost replPair formula = case formula of
  And fs ->
    And $ map (replaceBackAppRecPost replPair) fs
  Or fs ->
    Or $ map (replaceBackAppRecPost replPair) fs
  Exists exQsvs f -> Exists exQsvs (replaceBackAppRecPost replPair f)
  GEq ups -> formula
  EqK ups -> -- any ups contain a marker? replace it back with AppCAbst
    let apps = catMaybes $ map (\(qsv,f) -> if qsv `elem` fqsv (EqK ups) then Just f else Nothing) replPair in
    case length apps of
      0 -> formula
      1 -> head apps
      2 -> error $ "replaceBackAppRecPost: two fresh variables in the same equality"++show formula
  AppRecPost mn insouts -> error $ "replaceBackAppRecPost: argument should not contain AppRecPost:\n " ++ show formula 


{---------------------------------
--------OldSimplify RecPost----
----------------------------------
Incorrect solution:
MN<x> := (x>=0 || x<0 && exists(x1: x1=x-1 && MN<x1>))
Introduce markers for applications:
MN<x,x1,m> := (x>=0 || x<0 && exists(x1: x1=x-1 && m=0))
Problem: x1 will be simplified due to the existential quantifier

Steps for correct solution:
Step1: Replace AppRecPost with markers (m=0) and collect actual arguments
Step2: Float quantifiers for local-vars to the outermost scope
Step3: Simplify all the quantified-local-vars, which are innermost than any actual-argument (local-vars)
Step4: Replace markers with AppRecPost
...
-}
oldSimplifyRecPost:: RecPost -> FS RecPost
oldSimplifyRecPost recpost@(RecPost mn f oth) = 
  let (quants,noF) = floatQfiers f in
  replaceAppRecPost noF >>= \(markNoF,markAppRecPost) ->
      let actualInsouts = concatMap (\(qsvs,f) -> case f of AppRecPost mn args -> args) markAppRecPost in
      let (quantsArgs,exMarkNoF) = includeQfiers markNoF quants actualInsouts in
      simplify exMarkNoF >>= \sMarkNoF ->
      let sNoF = replaceBackAppRecPost markAppRecPost sMarkNoF in
      let sF = pasteQfiers (quantsArgs,sNoF) in
  return (RecPost mn sF oth)
  where
  replaceAppRecPost:: Formula -> FS (Formula,[Marker])
  -- requires: formula is not mutually recursive
  replaceAppRecPost formula = case formula of
    And fs -> 
      mapM replaceAppRecPost fs >>= \results -> let (replFs,replPair) = unzip results in
      return (And replFs,concat replPair)
    Or fs -> 
      mapM replaceAppRecPost fs >>= \results -> let (replFs,replPair) = unzip results in
      return (Or replFs,concat replPair)
--    Not f -> 
--      replaceAppRecPost f >>= \(replF,replPair) ->
--      return (Not replF,replPair)
    Exists exQsvs f ->
      replaceAppRecPost f >>= \(replF,replPair) ->
      return (Exists exQsvs replF,replPair)
--    Forall forQsvs f ->
--      replaceAppRecPost f >>= \(replF,replPair) ->
--      return (Forall forQsvs replF,replPair)
    GEq ups -> return (formula,[])
    EqK ups -> return (formula,[])
    AppRecPost _ _ ->
      fresh >>= \fsh -> 
      let fshQsv = (SizeVar fsh, Unprimed) in
      let fshEq = EqK [Coef fshQsv 1,Const 0] in --add a marker
      return (fshEq,[(fshQsv,formula)])

includeQfiers:: Formula -> [Formula] -> [QSizeVar] -> ([Formula],Formula)
-- ensures: exists (quants: f) = exists ((fst res): (snd res))
includeQfiers f quants insouts = 
  let (nonArgsQ,withArgsQ) = 
        span (\f -> case f of {
                          Exists qsvs _ -> noElemFromFstIsInSnd qsvs insouts; 
                          Forall qsvs _ -> noElemFromFstIsInSnd qsvs insouts}
             ) (reverse quants) in
    (reverse withArgsQ,pasteQfiers (reverse nonArgsQ,f))

pasteQfiers:: ([Formula],Formula) -> Formula
pasteQfiers (qs,nof) = 
  let rqs = reverse qs in
    foldl (\f1 -> \f2 -> case f2 of {Exists qsvs _ -> Exists qsvs f1}) nof rqs

floatQfiers:: Formula -> ([Formula],Formula)
floatQfiers formula = case formula of
  And fs -> 
    let (qss,nofs) = unzip $ map (\f -> floatQfiers f) fs in
      (concat qss,And nofs)
  Or fs ->
    let (qss,nofs) = unzip $ map (\f -> floatQfiers f) fs in
      (concat qss,Or nofs)
  GEq us -> ([],formula)
  EqK us -> ([],formula)
  AppRecPost mn insouts -> ([],formula)
  Exists qsvs f ->
    let (qs,nof) = floatQfiers f in
      ((Exists qsvs undefined):qs,nof)
  _ -> error "floatQfiers: unexpected argument"


--testRecPost:: RecPost -> Bool
testRecPost recpost@(RecPost mn f oth) = 
  let (b,qsvs) = testF f in
  (b,qsvs) --  && (length qsvs == length (nub qsvs))
  where 
  testF:: Formula -> (Bool,[QSizeVar])
  testF formula = case formula of
    And fs -> 
      let (bs,qsvs) = unzip (map (\f -> testF f) fs) in
      (and bs,concat qsvs)
    Or fs -> 
      let (bs,qsvs) = unzip (map (\f -> testF f) fs) in
      (and bs,concat qsvs)
    Exists qsvs f -> let (b,exs) = testF f in (b,qsvs++exs)
    GEq us -> (True,[])
    EqK us -> (True,[])
    AppRecPost mn insouts -> (True,[])
    Not f -> error ("unexpected argument: "++show formula)
    Forall qsvs f -> error ("unexpected argument: "++show formula)
    AppCAbst mn _ _ -> error ("unexpected argument: "++show formula)
    Union fs -> error ("unexpected argument: "++show formula)
    FormulaBogus -> error ("unexpected argument: "++show formula)

{-
template formula = case formula of
  And fs ->
  Or fs ->
  Not f ->
  Exists qsvs f ->
  GEq us ->
  EqK us ->
  AppRecPost mn insouts ->
  _ -> error ("unexpected argument: "++show formula)
-}
