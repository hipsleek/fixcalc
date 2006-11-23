module ImpFixpoint2k(fixpoint2k,bottomUp2k,Heur(..),subrec,combSelHull,getDisjuncts,undefinedF,widen,fixTestBU) where
import Fresh(FS,fresh,takeFresh,addOmegaStr,getFlags,putStrFS,getCPUTimeFS)
import ImpAST
import ImpConfig(useSelectiveHull,widenEarly,Heur(..),FixFlags,fixFlags)
import ImpFormula(debugApply,noChange,simplify,subset,recTheseQSizeVars,pairwiseCheck,equivalent)
import ImpHullWiden(widen,widenOne,combHull,combSelHull,countDisjuncts,getDisjuncts,DisjFormula)
import MyPrelude(showDiffTimes,noElemFromFstIsInSnd,zipOrFail,thd3)
---------------
import List((\\),nub)
import Maybe(catMaybes)
import Monad(when)

maxIter::Int
maxIter = 10

undefinedF = error "this dummy argument (formula) should not be used"

-- fixpoint2k:: Method_declaration -> CAbst -> (Postcondition,Invariant)
fixpoint2k:: MethDecl -> RecPost -> FS (Formula,Formula)
-- requires: CAbst has ex-quantified variables that are all different
-- otherwise simplifyRecPost is incorrect: (ex x: x=1 & (ex x: x=2)) is transformed to (ex x: (ex x: (x=1 & x=2)))
fixpoint2k m recPost@(RecPost mn io f (i,o,_)) =
  if simulateOldFixpoint then fixpoint m recPost
  else
  if not (fst (testRecPost recPost)) then error ("assertion failed in fixpoint2k") 
  else
      getFlags >>= \flags -> let fixFlags1 = fixFlags flags in
--            putStrFS("CAbst:="++showSet f) >>
--            bottomUp2k recPost fixFlags1 fFalse >>= \(postNoSimpl,_) ->
--            putStrFS("OK:="++showSet postNoSimpl) >>
      newSimplifyRecPost recPost >>= \sRecPost@(RecPost _ _ sf _) ->
--      putStrFS("SimplCAbst:="++showSet sf) >>
---- BU2k fixpoint for simplified RecPost
      addOmegaStr ("\n# " ++ show sRecPost) >> addOmegaStr ("#\tstart bottomUp2k") >>
      getCPUTimeFS >>= \time1 -> 
      bottomUp2k sRecPost fixFlags1 fFalse >>= \(post,cntPost) ->
      addOmegaStr ("# Post" ++ show (fst fixFlags1) ++ ":=" ++ showSet post) >> 
      addOmegaStr ("#\tend bottomUp2k" ++ "\n") >>
      putStrFS("OK:=" ++ showSet post) >>
--            equivalent postNoSimpl post >>= \b ->
--            (if (not b) then putStrFS ("###notEquivalent") else putStrFS ("###Equivalent")) >>
      getCPUTimeFS >>= \time2 -> 
      putStrFS ("    BU " ++ show cntPost ++ "iter: " ++ showDiffTimes time2 time1)>>
---- TD fixpoint for simplified RecPost
      topDown2k sRecPost (1,SimilarityHeur) fTrue >>= \(inv,cntInv) ->
      getCPUTimeFS >>= \time3 -> 
      addOmegaStr ("# Inv:=" ++ showRelation (i,recTheseQSizeVars i,inv) ++ "\n") >>
      putStrFS("TransInv:=" ++ showRelation(i,recTheseQSizeVars i,inv)) >>
      putStrFS("    TD " ++ show cntInv ++ "iter: " ++ showDiffTimes time3 time2) >>
--      let (inv,cntInv) = (fTrue,-1) in
      return (post,inv)
     
----Bottom-Up fixpoint
-- 3rd widening strategy + general selHull
bottomUp2k:: RecPost -> FixFlags -> Formula -> FS (Formula,Int)
bottomUp2k recpost (m,heur) initFormula = 
  subrec recpost initFormula >>= \f1 -> simplify f1 >>= \f1r ->
  addOmegaStr ("# F1:="++showSet f1r) >>
    subrec recpost f1r >>= \f2 -> simplify f2 >>= \f2r -> 
    addOmegaStr ("# F2:="++showSet f2r) >>
  subrec recpost f2r >>= \f3 ->  simplify f3 >>= \f3r -> 
  addOmegaStr ("# F3:="++showSet f3r) >>
--  putStrFS ("    Disj during BUfix: "++show (countDisjuncts f1r) ++ ", " ++ show (countDisjuncts f2r) ++ ", " ++ show (countDisjuncts f3r)) >>
  pairwiseCheck f3r >>=  \pwF3 -> let mdisj = min m (countDisjuncts pwF3) in
  putStrFS("Upper-bound m:="++show m++", Heuristic m:=" ++ show (countDisjuncts pwF3)) >>
  combSelHull (mdisj,heur) (getDisjuncts f3r) f1r >>= \s3 ->
  iterBU2k recpost (mdisj,heur) f3r s3 f1r 4
    
iterBU2k:: RecPost -> FixFlags -> Formula -> DisjFormula -> Formula -> Int -> FS (Formula,Int)
-- requires: scrt, sbase are in conjunctive form
iterBU2k recpost (m,heur) fcrt scrt fbase cnt =
  if (cnt>maxIter) then return (fTrue,-1)
  else
-- 2nd widening strategy: iterate using fcrt
--    subrec recpost fcrt >>= \fn -> simplify fn >>= \fnext ->
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
    combSelHull (m,heur) (getDisjuncts fnext) undefinedF >>= \snext ->
    fixTestBU recpost (Or snext) >>= \fixok -> 
    when (not fixok) (putStrFS ("not a Reductive point at "++show cnt)) >>
    putStrFS("    Post" ++ show cnt ++ ":=" ++ showSet (Or snext)) >>
    if (cnt>maxIter) then pairwiseCheck (Or snext) >>= \pw -> return (pw,cnt)
    else iterate2k recpost (m,heur) snext (cnt+1)  
    
fixTestBU:: RecPost -> Formula -> FS Bool
fixTestBU recpost candidate = 
    addOmegaStr ("#\tObtained postcondition?") >>
    subrec recpost candidate >>= \fnext -> 
    subset fnext candidate

subrec :: RecPost -> Formula -> FS Formula
subrec (RecPost formalMN formalIO f1 (_,_,qsvByVal)) f2 =
  subrec1 f1 f2
 where 
 subrec1:: Formula -> Formula -> FS Formula
 subrec1 f g = case f of 
    (And fs) -> 
      mapM (\x -> subrec1 x g) fs >>= \res -> return (And res)
    (Or fs) -> 
      mapM (\x -> subrec1 x g) fs >>= \res -> return (Or res)
    (Not ff) -> 
      subrec1 ff g >>= \res -> return (Not res)
    (Exists vars ff) -> 
      subrec1 ff g >>= \res -> return (Exists vars res)
    (Forall vars ff) -> 
      subrec1 ff g >>= \res -> return (Forall vars res)
    (AppRecPost actualMN actualIO) ->
      if not (formalMN==actualMN) then
        error "subrec: mutual recursion detected" 
      else if not (length formalIO == length actualIO) then
        error $ "subrec: found different no of QSVs for CAbst:\n " ++ show f
      else
        let rho = zip formalIO actualIO in
        debugApply rho g >>= \rhoG ->
-- NOT TRUE: If assignments to pass-by-value parameters are disallowed in the method body: adding explicit noChange is not needed
--        return rhoG
        return $ fAnd [rhoG,noChange qsvByVal]
    (AppCAbst actualName actualArgs actualRes) -> 
        error "subrec: encountered AppCAbst" 
    _ -> return f

-----Top Down fixpoint
-- 2nd widening strategy + general selHull
topDown2k:: RecPost -> FixFlags -> Formula -> FS (Formula,Int)
topDown2k recpost (m,heur) postFromBU = 
  getOneStep recpost postFromBU >>= \oneStep@(ins,recs,g1) ->
  addOmegaStr ("#\tG1:="++showRelation oneStep) >>
--  putStrFS ("    Disj during TDfix: "++show (countDisjuncts g1)) >>
  compose g1 (ins,recs,g1) >>= \gcomp ->
  getFlags >>= \flags -> 
      pairwiseCheck g1 >>=  \pwG1 -> let mdisj = min m (countDisjuncts pwG1) in
--      putStrFS("    suggestedM:="++show m++", heurM:=" ++ show (countDisjuncts pwG1)) >>
      addOmegaStr ("#\tG2 hulled to G2r") >>
      combSelHull (mdisj,heur) (getDisjuncts g1 ++ getDisjuncts gcomp) undefinedF >>= \g2 ->

--      combSelHull (mdisj,heur) (getDisjuncts g1 ++ getDisjuncts gcomp) undefinedF >>= \g1' ->
--      compose (Or g1') oneStep >>= \gcomp' ->
--      addOmegaStr ("#\tG3 hulled to G3r") >>
--      combSelHull (mdisj,heur) (getDisjuncts(thd3 oneStep)++getDisjuncts gcomp') undefinedF >>= \g2 ->

      iterTD2k recpost (mdisj,heur) g2 oneStep 3

iterTD2k:: RecPost -> FixFlags -> DisjFormula -> Relation -> Int -> FS (Formula,Int)
iterTD2k recpost (m,heur) gcrt oneStep cnt = 
  if (cnt>maxIter) then return (fTrue,-1)
  else
    compose (Or gcrt) oneStep >>= \gcomp ->
    addOmegaStr ("#\tG" ++ show (cnt) ++ " hulled to G" ++ show (cnt) ++ "r") >>
    combSelHull (m,heur) (gcrt++getDisjuncts gcomp) undefinedF >>= \gnext ->
-- using g1=thd3 oneStep insted of gcrt gives simpler formulae!
--    combSelHull (m,heur) (getDisjuncts(thd3 oneStep)++getDisjuncts gcomp) undefinedF >>= \gnext ->
    widen heur (gcrt,gnext) >>= \gcrtW ->
    fixTestTD oneStep (Or gcrtW) >>= \fixok ->
    if fixok then return (Or gcrtW,cnt)
    else iterTD2k recpost (m,heur) gcrtW oneStep (cnt+1)

fixTestTD:: Relation -> Formula -> FS Bool
fixTestTD oneStep candidate = 
  compose candidate oneStep >>= \gcomp ->
  combHull [candidate,gcomp] >>= \gnext ->
  addOmegaStr ("#\tObtained invariant?") >> subset gnext candidate

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
-- ensures: (length ins) = (length recs)
getOneStep recPost@(RecPost mn io f (i,o,_)) postFromBU =
  if not (null ((io \\ i) \\ o)) then 
    error ("getOneStep: incoherent arguments io, i, o\n io: " ++ show io ++ "\n i:" ++ show i ++ "\n o:" ++ show o)
  else 
    let ins = i in
    let recs = (recTheseQSizeVars i) in
    ctxRec recs io postFromBU f >>= \ctx ->
    addOmegaStr("# RecCtx:=" ++ showSet(fExists o ctx)) >>
    simplify (fExists o ctx) >>= \oneStep ->
    return (ins,recs,oneStep)

ctxRec:: [QSizeVar] -> [QSizeVar] -> Formula -> Formula -> FS Formula
ctxRec recs io postFromBU formula = case formula of
  And fs -> 
    mapM (\f -> if isRec f then ctxRec recs io postFromBU f else return f) fs >>= \mapfs -> return (And mapfs)
  Or fs -> 
    mapM (\f -> if isRec f then ctxRec recs io postFromBU f else return fFalse) fs >>= \mapfs -> return (Or mapfs)
  Not f -> 
    ctxRec recs io postFromBU f >>= \ctx -> return (Not ctx)
  GEq us -> error ("ctxRec: " ++ (showSet formula)) --It should not happen (?)
  EqK us -> error ("ctxRec: " ++ (showSet formula)) --It should not happen (?)
  AppRecPost mn insouts -> 
    let ins = take (length recs) insouts in
    let rhoFormalToActual = zipOrFail io insouts in
    debugApply rhoFormalToActual postFromBU >>= \post ->
    let eqs = And $ map (\(vrec,v) -> EqK [Coef vrec 1,Coef v (-1)]) (zip recs ins) in
    return (And [post,eqs])
  Forall qsvs f -> 
    ctxRec recs io postFromBU f >>= \ctx -> return (Forall qsvs ctx)
  Exists qsvs f -> 
    ctxRec recs io postFromBU f >>= \ctx -> return (Exists qsvs ctx)
  _ -> error ("ctxRec: unexpected argument: "++show formula)

isRec:: Formula -> Bool
isRec formula = case formula of
  And fs -> any isRec fs
  Or fs -> any isRec fs
  Not f -> isRec f
  GEq us -> False
  EqK us -> False
  AppRecPost mn insouts -> True
  Forall qsvs f -> isRec f
  Exists qsvs f -> isRec f
  _ -> error ("isRec: unexpected argument: "++show formula)

----------------------------------
--------Old fixpoint procedure----
----------------------------------
-- Below procedures use RecPost (instead of CAbst) as well as the rewritten fixpoint methods.
-- They should give same result as the old fixpoint
-- flags that can be used: widenEarly, selHull
simulateOldFixpoint = False

-- old version of the fixpoint procedure
fixpoint:: MethDecl -> RecPost -> FS (Formula,Formula)
fixpoint m recPost@(RecPost mn io f (i,o,_)) =
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
--------Simplify RecPost----
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
--Occurrences of AppRecPost will be replaced by a (b=0) and a marker is returned: (b,AppRecPost insouts)
type Marker = (QSizeVar,Formula)

newSimplifyRecPost:: RecPost -> FS RecPost
newSimplifyRecPost recpost@(RecPost mn insouts prmf oth) = 
  let (prms,f) = (case prmf of {Exists prms f -> (prms,f);_ -> error("assertion failed in simplifyRecPost")}) in
  replaceAppRecPost f >>= \(markF,markAppRecPost,markArgs) ->
  simplify markF >>= \sMarkF ->
  let sF = replaceBackAppRecPost markAppRecPost sMarkF in
  let sFWithArgs = Exists prms (fExists markArgs sF) in 
  return (RecPost mn insouts sFWithArgs oth)
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


oldSimplifyRecPost:: RecPost -> FS RecPost
oldSimplifyRecPost recpost@(RecPost mn insouts f oth) = 
  let (quants,noF) = floatQfiers f in
  replaceAppRecPost noF >>= \(markNoF,markAppRecPost) ->
      let actualInsouts = concatMap (\(qsvs,f) -> case f of AppRecPost mn args -> args) markAppRecPost in
      let (quantsArgs,exMarkNoF) = includeQfiers markNoF quants actualInsouts in
      simplify exMarkNoF >>= \sMarkNoF ->
      let sNoF = replaceBackAppRecPost markAppRecPost sMarkNoF in
      let sF = pasteQfiers (quantsArgs,sNoF) in
  return (RecPost mn insouts sF oth)
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
    Not f -> 
      replaceAppRecPost f >>= \(replF,replPair) ->
      return (Not replF,replPair)
    Exists exQsvs f ->
      replaceAppRecPost f >>= \(replF,replPair) ->
      return (Exists exQsvs replF,replPair)
    Forall forQsvs f ->
      replaceAppRecPost f >>= \(replF,replPair) ->
      return (Forall forQsvs replF,replPair)
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
testRecPost recpost@(RecPost mn insouts f oth) = 
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
    QLabelSubst subst lbl -> error ("unexpected argument: "++show formula)

{-
template formula = case formula of
  And fs ->
  Or fs ->
  Not f ->
  Exists qsvs f ->
  GEq us ->
  EqK us ->
  AppRecPost mn insouts ->
  QLabelSubst subst lbl ->
  _ -> error ("unexpected argument: "++show formula)
-}
