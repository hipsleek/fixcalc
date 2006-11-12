module ImpFixpoint2k(fixpoint2k,bottomUp2k,Heur(..),subrec,combSelHull,getDisjuncts,undefinedF,widen,widenPPL,fixTestBU) where
import Fresh(FS,fresh,takeFresh,addOmegaStr,getFlags,putStrFS,getCPUTimeFS)
import ImpAST
import ImpConfig(useSelectiveHull,widenEarly,noExistentialsInDisjuncts,Heur(..),FixFlags,fixFlags)
import ImpFormula(debugApply,noChange,simplify,hull,subset,equivalent,recTheseQSizeVars,pairwiseCheck,projectQSV,hausdorffDistance,addHDistances)
import MyPrelude(tr,showDiffTimes,noElemFromFstIsInSnd,singleton,zipOrFail,numsFrom,updateList)
---------------
import Data.Array
import List(nub,union,(\\))
import Maybe(catMaybes,fromJust)
import Monad(filterM,foldM,when)

--fixFlags2 = (3,SimilarityHeur)
maxIter:: RecPost -> Int
maxIter _ = 10
showDebugMSG = False

-- uses RecPost and the rewritten fixpoint methods, but should give same result as the old fixpoint
-- flags: widenEarly, selHull
simulateOldFixpoint = False


type DisjFormula = [Formula] -- represents (Or [Formula]).
type ConjFormula = [Formula] -- represents (And [Formula]).
type DisjMFormula = [Maybe Formula]
undefinedF = error "this dummy argument (formula) should not be used"

-- fixpoint2k:: Method_declaration -> CAbst -> (Postcondition,Invariant)
fixpoint2k:: MethDecl -> RecPost -> FS (Formula,Formula)
-- requires: CAbst has ex-quantified variables that are all different
-- otherwise simplifyRecPost is incorrect: (ex x: x=1 & (ex x: x=2)) is transformed to (ex x: (ex x: (x=1 & x=2)))
fixpoint2k m recPost@(RecPost mn io f (i,o,_)) =
  if simulateOldFixpoint then fixpoint m recPost
  else
      getFlags >>= \flags -> let fixFlags1 = fixFlags flags in
---- Simplify RecPost
      simplifyRecPost recPost >>= \sRecPost@(RecPost _ _ sf _) ->
---- BU2k fixpoint for simplified RecPost (fixFlags)
      getCPUTimeFS >>= \time1 -> 
      addOmegaStr ("\n# " ++ show sRecPost) >> addOmegaStr ("#\tstart bottomUp2k") >>
      bottomUp2k sRecPost fixFlags1 fFalse >>= \(post1,cntPost1) ->
      addOmegaStr ("# Post" ++ show (fst fixFlags1) ++ ":=" ++ showSet (fqsv post1,post1)) >> addOmegaStr ("#\tend bottomUp2k" ++ "\n") >>
      when (showDebugMSG) (putStrFS("    Post" ++ show (fst fixFlags1) ++ ":=" ++ showSet(fqsv post1,post1))) >>
---- BU2k fixpoint for simplified RecPost (fixFlags2,ascending-seq,covered-widening)
      getCPUTimeFS >>= \time2 -> 
--      addOmegaStr ("#\tstart bottomUp2kPPL") >>
--      bottomUp2kPPL sRecPost fixFlags1 fFalse >>= \(post2,cntPost2) ->
--      addOmegaStr ("# Post" ++ show (fst fixFlags1) ++ ":=" ++ showSet (fqsv post2,post2)) >> addOmegaStr ("#\tend bottomUp2kPPL" ++ "\n") >>
--      putStrFS("    Post" ++ show (fst fixFlags1) ++ ":=" ++ showSet(fqsv post2,post2)) >>
      let (post2,cntPost2) = (fTrue,-1) in
---- Statistics BU
      getCPUTimeFS >>= \time3 -> 
--      putStrFS ("    BU " ++ show cntPost1 ++ "iter: " ++ showDiffTimes time2 time1 ++ ", " 
--                          ++ show cntPost2 ++ "iter: " ++ showDiffTimes time3 time2) >>
---- TD fixpoint for simplified RecPost
--      topDown2k sRecPost (1,SimilarityHeur) fTrue >>= \(inv,cntInv) ->
--      addOmegaStr ("# Inv:=" ++ showRelation (i,recTheseQSizeVars i,inv) ++ "\n") >>
      let (inv,cntInv) = (fTrue,-1) in
--      putStrFS("    Inv:=" ++ showRelation(i,recTheseQSizeVars i,inv)) >>
--      getCPUTimeFS >>= \time4 -> 
--      putStrFS("    TD " ++ show cntInv ++ "iter: " ++ showDiffTimes time4 time3) >>
--      equivalent nsPost sPost >>= \b ->
--      (if not b then putStrFS ("    CAbst simplification...NOTOK     ##########") 
--      else putStrFS("    CAbst simplification...OK: fixBU(CAbst)=fixBU(simplCAbst)")) >>
--        let respost=post1 in
--        subset post1 post2 >>= \b1 ->
--        subset post2 post1 >>= \b2 ->
--        case (b1,b2) of
--          (True,True) -> putStrFS("##########equivalent") >> return (respost,inv)
--          (True,False) -> putStrFS("##########postMY is stronger than postWI") >> return (respost,inv)
--          (False,True) -> putStrFS("##########postWI is stronger than postMY") >> return (respost,inv)
--          (False,False) -> putStrFS("##########unrelated") >> return (respost,inv)
      return (post1,inv)
     
----Bottom-Up fixpoint
bottomUp2kPPL:: RecPost -> FixFlags -> Formula -> FS (Formula,Int)
bottomUp2kPPL recpost (m,heur) initFormula = 
  subrec recpost initFormula >>= \f1 -> simplify f1 >>= \f1r ->
  addOmegaStr ("# F1:="++showSet(fqsv f1r,f1r)) >>
    subrec recpost f1r >>= \f2 -> simplify f2 >>= \f2r -> 
    addOmegaStr ("# F2:="++showSet(fqsv f2r,f2r)) >>
  subrec recpost f2r >>= \f3 -> simplify f3 >>= \f3r -> 
  addOmegaStr ("# F3:="++showSet(fqsv f3r,f3r)) >>
  pairwiseCheck f3r >>=  \pwF3 -> let mdisj = min m (countDisjuncts pwF3) in
  combSelHull (mdisj,heur) (getDisjuncts f3r) f1r >>= \s3 ->
  iterBU2kPPL recpost (mdisj,heur) f3r s3 f1r 4

iterBU2kPPL:: RecPost -> FixFlags -> Formula -> DisjFormula -> Formula -> Int -> FS (Formula,Int)
-- requires: fcrt, scrt, sbase are in conjunctive form
iterBU2kPPL recpost (m,heur) fcrt scrt fbase cnt =
  if (cnt>maxIter recpost) then return (fTrue,-1)
  else
    subrec recpost (Or scrt) >>= \fn -> simplify fn >>= \fnext ->
    addOmegaStr ("# F"++ show cnt ++ ":="++showSet(fqsv fnext,fnext)) >>
    combSelHull (m,heur) (getDisjuncts fnext) fbase >>= \fnextHMany ->
--    putStrFS("widenPPL:\n" ++ concatSepByLn (map (\f -> showSet (fqsv f,f)) (fnextHMany++scrt))) >> 
    widenPPL (scrt++fnextHMany) (scrt++fnextHMany) >>= \snext ->
    fixTestBU recpost (Or snext) >>= \fixok ->
    if fixok then pairwiseCheck (Or snext) >>= \pw -> return (pw,cnt)
    else iterBU2kPPL recpost (m,heur) fnext snext fbase (cnt+1)  

-- 3rd widening strategy + general selHull
bottomUp2k:: RecPost -> FixFlags -> Formula -> FS (Formula,Int)
bottomUp2k recpost (m,heur) initFormula = 
  subrec recpost initFormula >>= \f1 -> simplify f1 >>= \f1r ->
  addOmegaStr ("# F1:="++showSet(fqsv f1r,f1r)) >>
    subrec recpost f1r >>= \f2 -> 
    simplify f2 >>= \f2r -> 
    addOmegaStr ("# F2:="++showSet(fqsv f2r,f2r)) >>
  subrec recpost f2r >>= \f3 -> simplify f3 >>= \f3r -> 
  addOmegaStr ("# F3:="++showSet(fqsv f3r,f3r)) >>
--  putStrFS ("    Disj during BUfix: "++show (countDisjuncts f1r) ++ ", " ++ show (countDisjuncts f2r) ++ ", " ++ show (countDisjuncts f3r)) >>
  pairwiseCheck f3r >>=  \pwF3 -> let mdisj = min m (countDisjuncts pwF3) in
  putStrFS("Upper-bound m:="++show m++", Heuristic m:=" ++ show (countDisjuncts pwF3)) >>
  combSelHull (mdisj,heur) (getDisjuncts f3r) f1r >>= \s3 ->
  iterBU2k recpost (mdisj,heur) f3r s3 f1r 4
    
iterBU2k:: RecPost -> FixFlags -> Formula -> DisjFormula -> Formula -> Int -> FS (Formula,Int)
-- requires: scrt, sbase are in conjunctive form
iterBU2k recpost (m,heur) fcrt scrt fbase cnt =
  if (cnt>maxIter recpost) then return (fTrue,-1)
  else
-- 2nd widening strategy: iterate using fcrt
--    subrec recpost fcrt >>= \fn -> simplify fn >>= \fnext ->
-- 3nd widening strategy: iterate using scrt (fcrt is not used anymore)
    subrec recpost (Or scrt) >>= \fn -> simplify fn >>= \fnext ->
    addOmegaStr ("# F"++ show cnt ++ ":="++showSet(fqsv fnext,fnext)) >>
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
    addOmegaStr ("# F"++ show cnt ++ ":="++showSet(fqsv fnext,fnext)) >>
    combSelHull (m,heur) (getDisjuncts fnext) undefinedF >>= \snext ->
    fixTestBU recpost (Or snext) >>= \fixok -> 
    when (not fixok) (putStrFS ("not a Reductive point at "++show cnt)) >>
    putStrFS("    Post" ++ show cnt ++ ":=" ++ showSet(fqsv (Or snext),Or snext)) >>
    if (cnt>maxIter recpost) then pairwiseCheck (Or snext) >>= \pw -> return (pw,cnt)
    else iterate2k recpost (m,heur) snext (cnt+1)  
    
fixTestBU:: RecPost -> Formula -> FS Bool
fixTestBU recpost candidate = 
    addOmegaStr ("#\tObtained postcondition?") >>
    subrec recpost candidate >>= \fnext -> 
    subset fnext candidate

-- old version of the fixpoint procedure
fixpoint:: MethDecl -> RecPost -> FS (Formula,Formula)
fixpoint m recPost@(RecPost mn io f (i,o,_)) =
---- BU fixpoint for non-simplified RecPost
      getCPUTimeFS >>= \time1 ->
      addOmegaStr ("\n# " ++ show recPost) >> addOmegaStr ("#\tstart bottomUp") >>
      bottomUp recPost >>= \(post,cntPost) ->
      addOmegaStr ("# Post:=" ++ showSet (fqsv post,post)) >> addOmegaStr ("#\tend bottomUp2k" ++ "\n") >> 
      putStrFS("    Post:=" ++ showSet(fqsv post,post)) >>
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
  addOmegaStr ("# F1:="++showSet(fqsv f1r,f1r)) >>
    subrec recpost f1r >>= \f2 -> simplify f2 >>= \f2r -> 
    addOmegaStr ("# F2:="++showSet(fqsv f2r,f2r)) >>
  subrec recpost f2r >>= \f3 -> simplify f3 >>= \f3r -> 
  addOmegaStr ("# F3:="++showSet(fqsv f3r,f3r)) >>
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
  if (cnt>maxIter recpost) then return (fTrue,-1)
  else
    subrec recpost fcrt >>= \fn -> simplify fn >>= \fnext ->
    addOmegaStr ("# F"++ show cnt ++ ":="++showSet(fqsv fnext,fnext)) >>
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
  if (cnt>maxIter recpost) then return (fTrue,-1)
  else
    subrec recpost fcrt >>= \fn -> simplify fn >>= \fnext ->
    addOmegaStr ("# F"++ show cnt ++ ":="++showSet(fqsv fnext,fnext)) >>
    combHull (getDisjuncts fnext) >>= \snext ->
    widenOne (scrt,snext) >>= \fcrtW ->
      fixTestBU recpost fcrtW >>= \fixok ->
      if fixok then return (fcrtW,cnt)
      else iterBUConj recpost fnext snext (cnt+1)  

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
      iterTD2k recpost (mdisj,heur) g2 oneStep 3

iterTD2k:: RecPost -> FixFlags -> DisjFormula -> Relation -> Int -> FS (Formula,Int)
iterTD2k recpost (m,heur) gcrt oneStep cnt = 
  if (cnt>maxIter recpost) then return (fTrue,-1)
  else
    compose (Or gcrt) oneStep >>= \gcomp ->
    addOmegaStr ("#\tG" ++ show (cnt) ++ " hulled to G" ++ show (cnt) ++ "r") >>
    combSelHull (m,heur) (gcrt++getDisjuncts gcomp) undefinedF >>= \gnext ->
    widen heur (gcrt,gnext) >>= \gcrtW ->
    fixTestTD oneStep (Or gcrtW) >>= \fixok ->
    if fixok then return (Or gcrtW,cnt)
    else iterTD2k recpost (m,heur) gcrtW oneStep (cnt+1)

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
  if (cnt>maxIter recpost) then return (fTrue,-1)
  else
    compose gcrt oneStep >>= \gcomp ->
    addOmegaStr ("#\tG" ++ show (cnt) ++ " hulled to G" ++ show (cnt) ++ "r") >>
    combHull [gcrt,gcomp] >>= \gnext ->
    widenOne (gcrt,gnext) >>= \gcrtW ->
    fixTestTD oneStep gcrtW >>= \fixok ->
    if fixok then return (gcrtW,cnt)
    else iterTD recpost gnext oneStep (cnt+1)

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
  if not (null ((io \\ i) \\ o)) then error ("getOneStep: incoherent arguments io, i, o\n io: " ++ show io ++ "\n i:" ++ show i ++ "\n o:" ++ show o)
  else 
    let ins = i in
    let recs = (recTheseQSizeVars i) in
    ctxRec recs io postFromBU f >>= \ctx ->
    addOmegaStr("# RecCtx:=" ++ showSet(fqsv (fExists o ctx),(fExists o ctx))) >>
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
  GEq us -> error ("ctxRec: " ++ (showSet (fqsv formula,formula))) --It should not happen (?)
  EqK us -> error ("ctxRec: " ++ (showSet (fqsv formula,formula))) --It should not happen (?)
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


-----Operators common to BU and TD
-- widening powersets based on subset
widenPPL:: DisjFormula -> DisjFormula -> FS DisjFormula
widenPPL initialXs xs = 
  choosePair xs xs >>= \maybePair ->
  case maybePair of 
    Just (x1,x2) -> widenOne (x1,x2) >>= \w -> 
--      putStrFS("widenPPL-pair:\n" ++ concatSepByLn (map (\f -> showSet (fqsv f,f)) [x1,x2,w])) >> 
      widenPPL initialXs (w:(xs \\ [x1,x2]))
    Nothing -> 
--      putStrFS("widenPPL-end:\n" ++ concatSepByLn (map (\f -> showSet (fqsv f,f)) xs)) >> 
      return xs

choosePair:: DisjFormula -> DisjFormula -> FS (Maybe (Formula,Formula))
choosePair [] xs = return Nothing
choosePair (x:testedXs) xs = 
  chooseSecond x (xs\\[x]) >>= \maybePair -> 
  case maybePair of
    Just (x1,x2) -> return maybePair
    Nothing -> choosePair testedXs xs

chooseSecond:: Formula -> DisjFormula -> FS (Maybe (Formula,Formula))
chooseSecond x [] = return Nothing
chooseSecond x (y:ys) = 
  subset x y >>= \subok ->
  if subok then return (Just (x,y)) else chooseSecond x ys

-- widening powersets based on affinity
widen:: Heur -> (DisjFormula,DisjFormula) -> FS DisjFormula
-- requires (length xs)=(length ys)
-- ensures (length res)=(length xs)
widen heur (xs,ys) = 
  when (not (length xs == length ys)) (error("ERROR: widen requires two formuale with same number of disjuncts\n"++showSet (fqsv (Or xs),Or xs) ++ "\n" ++ showSet(fqsv (Or ys),Or ys))) >>
  addOmegaStr ("# Widen1IN:=" ++ showSet(fqsv (Or xs),Or xs)) >> addOmegaStr ("# Widen2IN:=" ++ showSet(fqsv (Or ys),Or ys)) >> 
  let (mxs,mys) = (map (\x -> Just x) xs,map (\y -> Just y) ys) in
  computeMx heur (mxs,mys) >>= \affinMx ->
  iterateMx heur (mxs,mys) affinMx [] >>= \ijs ->
  when (showDebugMSG) (putStrFS("    Pairs of disjuncts to widen: "++show ijs)) >>
  mapM (\(i,j) -> widenOne (xs!!i,ys!!j)) ijs >>= \res ->
  addOmegaStr ("# WidenOUT:=" ++ showSet(fqsv (Or res),Or res)) >> 
  return res
  

computeMx:: Heur -> (DisjMFormula,DisjMFormula) -> FS AffinMx
-- requires: length disjCrt = length disjNxt
computeMx heur (disjCrt,disjNxt) = 
  let n = length disjCrt-1 in 
  let mx = initAffinMx n in
  computeMx1 heur mx (n,n) 0 (disjCrt,disjNxt)
  where
      computeMx1:: Heur -> AffinMx -> (Int,Int) -> Int -> (DisjMFormula,DisjMFormula) -> FS AffinMx
      computeMx1 heur mat (m,n) i (disjCrt,disjNxt) | i>n = return mat
      computeMx1 heur mat (m,n) i (disjCrt,disjNxt) = 
        computeRow heur mat (m,n) i 0 (disjCrt,disjNxt) >>= \mat1 ->
        computeMx1 heur mat1 (m,n) (i+1) (disjCrt,disjNxt)

-- computes Affinities for row i
computeRow:: Heur -> AffinMx -> (Int,Int) -> Int -> Int -> (DisjMFormula,DisjMFormula) -> FS AffinMx
computeRow heur mat (m,n) i j (disjCrt,disjNxt) | j>n = return mat
computeRow heur mat (m,n) i j (disjCrt,disjNxt) = 
  affinity (disjCrt!!i) (disjNxt!!j) heur comb2Widen (nub $ concatMap fqsv (catMaybes (disjCrt++disjNxt))) >>= \affinIJ -> 
  let newmat = mat // [((i,j),affinIJ)] in
  computeRow heur newmat (m,n) i (j+1) (disjCrt,disjNxt)

-- computes Affinities for col j
computeCol:: Heur -> AffinMx -> (Int,Int) -> Int -> Int -> (DisjMFormula,DisjMFormula) -> FS AffinMx
computeCol heur mat (m,n) i j (disjCrt,disjNxt) | i>n = return mat
computeCol heur mat (m,n) i j (disjCrt,disjNxt) = 
  affinity (disjCrt!!i) (disjNxt!!j) heur comb2Widen (nub $ concatMap fqsv (catMaybes (disjCrt++disjNxt))) >>= \affinIJ -> 
  let newmat = mat // [((i,j),affinIJ)] in
  computeCol heur newmat (m,n) (i+1) j (disjCrt,disjNxt)

iterateMx:: Heur -> (DisjMFormula,DisjMFormula) -> AffinMx -> [(Int,Int)] -> FS [(Int,Int)]
iterateMx heur (disjCrt,disjNxt) affinMx partIJs = 
  let (i,j) = chooseMaxElem affinMx in
  when True (putStrFS ("WidenMatrix "++showAffinMx affinMx) >> putStrFS ("MAX elem is: " ++ show (i,j))) >>
  replaceRelatedWithNoth (disjCrt,disjNxt) (i,j) >>= \(replDisjCrt,replDisjNxt) ->
  if (length (catMaybes replDisjCrt))==0 then return ((i,j):partIJs)
  else 
    computeRow heur affinMx (length replDisjCrt-1,length replDisjCrt-1) i 0 (replDisjCrt,replDisjNxt) >>= \affinMx1->
    computeCol heur affinMx1 (length replDisjCrt-1,length replDisjCrt-1) 0 j (replDisjCrt,replDisjNxt) >>= \affinMx2->
    iterateMx heur (replDisjCrt,replDisjNxt) affinMx2 ((i,j):partIJs)

-- replaces two related disjuncts with Nothing
replaceRelatedWithNoth:: (DisjMFormula,DisjMFormula) -> (Int,Int) -> FS (DisjMFormula,DisjMFormula)
replaceRelatedWithNoth (disjCrt,disjNxt) (i,j) =
  let disjI = updateList disjCrt i Nothing in
  let disjJ = updateList disjNxt j Nothing in
  return (disjI,disjJ)


widenOne:: (Formula,Formula) -> FS Formula
-- requires: fcrt, fnext are conjunctive formulae
widenOne (fcrt,fnext) = 
--    addOmegaStr ("# WidenCrt:=" ++ showSet (fqsv fcrt,fcrt)) >> addOmegaStr("# WidenNxt:=" ++ showSet (fqsv fnext,fnext)) >>
  closure fcrt >>= \fcrts ->
  mapM (subset fnext) fcrts >>= \suboks ->
  let fcrts' = zip fcrts suboks in
  let fcrt' = filter (\(f,ok) -> ok) fcrts' in
  let fwid = fAnd (map fst fcrt') in
--    addOmegaStr ("# WidenRes:=" ++ showSet (fqsv fwid,fwid)) >>
  return fwid

closure:: Formula -> FS ConjFormula
-- requires: f is conjunctive formula
closure f =
--  let updSubst = collectUpdSubst f in
  let updSubst = [] in
  let conjs = buildClauses updSubst f in
--    addOmegaStr ("Subst:"++show updSubst) >> 
--    addOmegaStr ("FPlusClosure:=" ++ showSet (fqsv (And conjs),And conjs)) >>
  let noconst = discoverIneqWithoutNegConstant conjs in
  discover2Ineq conjs >>= \discov ->
--  putStrFS ("###"++showSet(fqsv (fAnd conjs),fAnd conjs)++"\n>>>"++showSet(fqsv (fAnd discov),fAnd discov)++"\n|||"++showSet(fqsv (fAnd noconst),fAnd noconst)) >>
  return (conjs++discov++noconst)
  where
    -- input: (i+13<=j)
    -- output: (i<=j)
    discoverIneqWithoutNegConstant:: ConjFormula -> ConjFormula
    -- requires: formula is in conjunctive form
    discoverIneqWithoutNegConstant fs = 
      let newfs = map discoverIneqWithoutNegConstant1 fs in
      (nub newfs) \\ fs
    discoverIneqWithoutNegConstant1:: Formula -> Formula
    discoverIneqWithoutNegConstant1 formula = case formula of
      And fs -> fAnd (map discoverIneqWithoutNegConstant1 fs)
      GEq us -> let newus = filter (\u -> case u of {Const x -> if x<0 then False else True; Coef _ _ -> True}) us in
                GEq newus
      EqK us -> formula
      _ -> error ("unexpected argument: "++show formula)
    
    -- input: (i<=j && 4a<=2+i+3j)
    -- output: (a<=j)
    discover2Ineq:: ConjFormula -> FS ConjFormula
    discover2Ineq fs =
      let vars = fqsv (fAnd fs) in
      let singletons = map (\x -> [x]) vars in
      let pairs = genPairs vars in
      mapM (discover2Relation fs vars) (pairs) >>= \newfs ->
      let filtfs = filter (\f -> formulaIsNotEqK f) (nub $ concat newfs) in
      return (filtfs \\ fs)
    discover2Relation:: ConjFormula -> [QSizeVar] -> [QSizeVar] -> FS ConjFormula
    discover2Relation fs allvars varsToKeep = hull (fExists (allvars \\ varsToKeep) (fAnd fs)) >>= \fsimpl ->
      return (formulaToConjList fsimpl)
    genPairs:: [a] -> [[a]]
    genPairs xs | length xs <=1 = []
    genPairs (x:xs) = 
      let p1 = map (\y -> [x,y]) xs in
      let p2 = genPairs xs in p1++p2
    formulaToConjList:: Formula -> ConjFormula
    -- requires: formula is in conjunctive form
    formulaToConjList formula = case formula of
      And fs -> concatMap formulaToConjList fs
      GEq us -> [formula]
      EqK us -> [formula]
      _ -> error ("unexpected argument: "++show formula)
    formulaIsNotEqK formula = case formula of
      EqK us -> False
      _ -> True

    -- input: (f1-f3>=0 && f1+f2=0)
    -- output: [(f1,[-f2]),(f2,[-f1])]
    collectUpdSubst:: Formula -> [(QSizeVar,[Update])]
    collectUpdSubst f =
     case f of
       And fs -> concatMap collectUpdSubst fs
       GEq ups -> []
       EqK ups -> 
         let obtainSubst = (\ups -> \u -> case u of {
                                                Const i -> [];
                                                Coef qsv 1 -> [(qsv,map (mulUpdate (-1)) (ups\\[u]))]; --  [(Coef qsv (-i),ups\\[u])]
                                                Coef qsv (-1) -> [(qsv,(ups\\[u]))];
                                                _ -> []}
                            ) in
         concatMap (obtainSubst ups) ups
       _ -> error $ "widenOne: argument must be in conjunctive form\n " ++ show f
    buildClauses:: [(QSizeVar,[Update])] -> Formula -> [Formula]
    buildClauses updSubst f = 
     case f of
       And fs -> concatMap (buildClauses updSubst) fs
       GEq ups -> f:(applyUpdSubst updSubst f)
       EqK ups -> -- [f]
         -- more precise widening if (f2-f1=1) is transformed to (1<=f2-f1 && f2-f1<=1)
         [GEq ups,GEq (map (mulUpdate (-1)) ups)] 
       _ -> error $ "widenOne: argument must be in conjunctive form\n " ++ show f
    -- input: [(f1,[-f2]),(f2,[-f1])]
    -- input: (f1-f3>=0 && f1+f2=0)
    -- output: (f1-f3>=0 && -f2-f3>=0 && f1+f2=0)
    applyUpdSubst:: [(QSizeVar,[Update])] -> Formula -> [Formula]
    applyUpdSubst subs geq@(GEq _) = catMaybes $ map (\s -> applyOneUpdSubst s geq) subs
    applyOneUpdSubst:: (QSizeVar,[Update]) -> Formula -> Maybe Formula
    applyOneUpdSubst (qsv,ups) (GEq geqs) =
     let qsvIsIn = any (\u -> case u of {Coef qsv1 i -> qsv==qsv1; _ -> False}) geqs in 
     if qsvIsIn then
       let upsAfterSubs = concatMap (\u -> case u of {Coef qsv1 i -> if (qsv1==qsv) then map (mulUpdate i) ups else [u];_ -> [u]}) geqs in
       Just (GEq upsAfterSubs)
     else Nothing
    
    mulUpdate:: Int -> Update -> Update
    mulUpdate x (Const i) = Const (i*x)
    mulUpdate x (Coef qsv i) = Coef qsv (i*x)

combHull:: DisjFormula -> FS Formula
-- requires: disj represents the DNF-form of a formula f (Or fs)
combHull disj = hull (Or disj)

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

-----Selective Hull
combSelHull::FixFlags -> DisjFormula -> Formula -> FS DisjFormula
-- requires: disj represents the DNF-form of a formula f (Or fs)
-- requires: m>=1
-- ensures: length(res)=m
combSelHull (m,heur) disj fbase = 
  addOmegaStr ("# SelhullIN:=" ++ showSet(fqsv (Or disj),Or disj)) >> 
  (if length disj <= m then return disj
  else case m of
    1 -> combHull disj >>= \h -> return [h]
    _ -> -- assert (1<m<(length disj))
      mapM hullExistentials disj >>= \disjNoEx ->
      let disjM = map (\d -> Just d) disjNoEx in
      when showDebugMSG (putStrFS ("####SelHull: start iterating with "++show (length (catMaybes disjM))++ " disjuncts:\n" ++ concatSepByLn (map (\mf -> case mf of {Nothing -> "Nothing";Just f -> showSet(fqsv f,f)}) disjM))) >>
      computeHalfMx heur disjM >>= \affinMx ->
      iterateHalfMx (m,heur) disjM affinMx >>= \relatedDisjM ->
      return (catMaybes relatedDisjM)
    ) >>= \res -> addOmegaStr("# SelhullOUT:=" ++ showSet(fqsv (Or res),Or res)) >> return res

computeHalfMx:: Heur -> DisjMFormula -> FS AffinMx
-- ensures: (n,n)=length res, where n=length disj
computeHalfMx heur disj = 
  let n = length disj-1 in 
  let mx = initAffinMx n in
  computeHalfMx1 heur mx (n,n) 0 disj
  where
      computeHalfMx1:: Heur -> AffinMx -> (Int,Int) -> Int -> DisjMFormula -> FS AffinMx
      computeHalfMx1 heur mat (m,n) i disj | i>n = return mat
      computeHalfMx1 heur mat (m,n) i disj = 
        computeHalfRow heur mat (m,n) i (i+1) disj >>= \mat1 ->
-- The upper-half of the matrix is traversed with "computeHalfRow". I suspect "computeHalfCol" is redundant/useless
--        computeHalfCol heur mat1 (m,n) (i-1) i disj >>= \mat2 ->
        computeHalfMx1 heur mat1 (m,n) (i+1) disj

-- computes Affinities for second-half of row i, between columns j(first call uses i+1) and n
computeHalfRow:: Heur -> AffinMx -> (Int,Int) -> Int -> Int -> DisjMFormula -> FS AffinMx
computeHalfRow heur mat (m,n) i j disj | j>n = return mat
computeHalfRow heur mat (m,n) i j disj = 
  affinity (disj!!i) (disj!!j) heur comb2Hull (nub $ concatMap fqsv (catMaybes disj))>>= \affinIJ -> 
  let newmat = mat // [((i,j),affinIJ)] in
  computeHalfRow heur newmat (m,n) i (j+1) disj
-- computes Affinities for upper-half of column j, between rows i(first call uses j-1) and 0
computeHalfCol:: Heur -> AffinMx -> (Int,Int) -> Int -> Int -> DisjMFormula -> FS AffinMx
computeHalfCol heur mat (m,n) i j disj | i<0 = return mat
computeHalfCol heur mat (m,n) i j disj = 
  affinity (disj!!i) (disj!!j) heur comb2Hull (nub $ concatMap fqsv (catMaybes disj)) >>= \affinIJ -> 
  let newmat = mat // [((i,j),affinIJ)] in
  computeHalfCol heur newmat (m,n) (i-1) j disj

iterateHalfMx:: FixFlags -> DisjMFormula -> AffinMx -> FS DisjMFormula
iterateHalfMx (m,heur) disjM affinMx = 
  let (i,j) = chooseMaxElem affinMx in
  when ((affinMx!(i,j))<100) (putStrFS ("SelHull chooses disjuncts with less than 100%: "++ show (affinMx!(i,j)))) >>
  when showDebugMSG (putStrFS ("SelHullMatrix " ++ showAffinMx affinMx) >> putStrFS ("MAX elem is: " ++ show (i,j))) >>
  replaceRelated disjM (i,j) >>= \replDisjM ->
  when showDebugMSG (putStrFS ("####"++show (length (catMaybes replDisjM))++ "\n" ++ concatSepByLn (map (\mf -> case mf of {Nothing -> "Nothing";Just f -> showSet(fqsv f,f)}) replDisjM))) >>
  if (length (catMaybes replDisjM))<=m then return replDisjM
  else 
    computeHalfRow heur affinMx (length replDisjM-1,length replDisjM-1) i (i+1) replDisjM >>= \affinMx1->
    computeHalfCol heur affinMx1 (length replDisjM-1,length replDisjM-1) (i-1) i replDisjM >>= \affinMx2->
    computeHalfRow heur affinMx2 (length replDisjM-1,length replDisjM-1) j (j+1) replDisjM >>= \affinMx3->
    computeHalfCol heur affinMx3 (length replDisjM-1,length replDisjM-1) (j-1) j replDisjM >>= \affinMx4->
    iterateHalfMx (m,heur) replDisjM affinMx4

-- replaces two related disjuncts with their hull
replaceRelated:: DisjMFormula -> (Int,Int) -> FS DisjMFormula
-- requires: (0<=i,j<length disj)
-- ensures: length res=length disj
replaceRelated disj (i,j) =
  let relI = map (\i -> fromJust (disj!!i)) [i,j] in
  hull (Or relI) >>= \hulled ->
  let disjI = updateList disj i (Just hulled) in
  let disjIJ = updateList disjI j Nothing in
  return disjIJ
  
comb2Hull:: Formula -> Formula -> FS Formula
comb2Hull = (\f1 -> \f2 -> hull (Or [f1,f2]))

comb2Widen:: Formula -> Formula -> FS Formula
comb2Widen = (\f1 -> \f2 -> widenOne (f1,f2))

affinity:: Maybe Formula -> Maybe Formula -> Heur -> (Formula -> Formula -> FS Formula) -> [QSizeVar] -> FS Int
-- requires: f1,f2 represent conjunctive formulae
affinity Nothing _ heur _ _ = return identityA
affinity _ Nothing heur _ _ = return identityA
affinity (Just f1) (Just f2) HausdorffHeur _ fsv =
  putStrFS (concatMap show fsv) >>
  mapM (\x -> projectQSV f1 x) fsv >>= \ranges1 ->
  mapM (\x -> projectQSV f2 x) fsv >>= \ranges2 ->
  let distances = map hausdorffDistance (zip ranges1 ranges2) in
  let (inc,dist) = addHDistances distances in
  let maxdist = 1000 in
  let haus = ceiling (fromIntegral (100*inc) / fromIntegral (length fsv+1)) + ceiling (fromIntegral (100*dist) / fromIntegral ((length fsv+1)*maxdist))in
  putStrFS ("haus: " ++ show (length fsv) ++ ":" ++ show inc ++ ":" ++ show dist ++ ":" ++ show haus ++ ":" ++ show (100-haus)) >>
  return (100-haus)
affinity (Just f1) (Just f2) heur operation _ = 
    operation f1 f2 >>= \foperation -> 
    simplify (And [foperation,fNot(Or [f1,f2])]) >>= \fDif ->
    subset fDif fFalse >>= \difIsFalse ->
    if difIsFalse then return 100
    else
      subset fTrue foperation >>= \operationIsTrue ->
      if operationIsTrue then return 0 else 
      case heur of
        SimilarityHeur -> 
--          putStrFS("F1:="++showSet(fqsv f1,f1)) >> putStrFS("F2:="++showSet(fqsv f2,f2)) >>
          let (cf1,cf2) = (countConjuncts f1,countConjuncts f2) in
          mset f1 f2 foperation >>= \mSet ->
          let cmset = length mSet in
          let frac = (((fromIntegral cmset / (fromIntegral (cf1+cf2)))*98)+1) in
--          putStrFS("Foper:="++showSet(fqsv foperation,foperation)) >>
--          putStrFS("mSet::="++concatMap (\f -> showSet(fqsv f,f)) mSet) >>
--          putStrFS("affin:="++show cmset ++ "/" ++ show (cf1+cf2) ++ "  " ++ show (ceiling frac)) >>
          return (ceiling frac)
        DifferenceHeur -> 
          let n = countDisjuncts fDif in
          let nsteps = if n>4 then 4 else n in
          let disj = getDisjuncts fDif in
          let getAverageConjuncts = (\c -> fromIntegral (countConjuncts c) / (fromIntegral n)) in
          let s = ceiling $ sum (map getAverageConjuncts disj) in
          let diffSteps = 100 - (20*nsteps-s) in
          return diffSteps
        SyntacticHeur -> error "not implemented"
    where
      mset:: Formula -> Formula -> Formula -> FS [Formula]
      -- requires: f1,f2 are conjunctive formulae
      mset f1 f2 foperation =
        let (conjf1,conjf2) = (getConjuncts f1,getConjuncts f2) in
        filterM (\f -> subset foperation f) (conjf1 `union` conjf2)

getDisjuncts:: Formula -> [Formula]
-- requires formula is in DNF-form (result of simplify)
getDisjuncts formula = 
  case formula of
    And _ -> if countDisjuncts formula == 1 then [formula] else error ("getDisjuncts: "++show formula)
    Or fs -> if countDisjuncts formula == length fs then fs else error ("getDisjuncts: "++show formula)
    GEq us -> [formula] 
    EqK us -> [formula]
    AppRecPost mn insouts -> [formula]
    Exists qsvs f -> if countDisjuncts formula == 1 then [formula] else [formula]
    _ -> error ("getDisjuncts: unexpected argument"++show formula)

countDisjuncts:: Formula -> Int
countDisjuncts formula = case formula of
  And fs -> maximum $ map (\f -> countDisjuncts f) fs
  Or fs -> sum (map (\f -> countDisjuncts f) fs)
  GEq us -> 1
  EqK us -> 1
  AppRecPost mn insouts -> 1
  Exists qsvs f -> countDisjuncts f
  _ -> error ("countDisjuncts: unexpected argument: "++show formula)

getConjuncts:: Formula -> [Formula]
-- requires: formula is conjunctive
getConjuncts formula = case formula of
  And fs -> concatMap (\f -> getConjuncts f) fs
  GEq us -> [formula]
  EqK us -> [formula]
  Exists qsvs f -> if countDisjuncts f == 1 then [formula] else error ("getConjuncts: unexpected argument: "++show formula)
  _ -> error ("getConjuncts: unexpected argument: "++show formula)

countConjuncts:: Formula -> Int
-- requires: formula is conjunctive
countConjuncts formula = case formula of
  And fs -> sum (map (\f -> countConjuncts f) fs)
  GEq us -> 1
  EqK us -> 1
  Exists qsvs f -> if countDisjuncts f == 1 then countConjuncts f else error ("countConjuncts: unexpected argument: "++show formula)
  _ -> error ("countConjuncts: unexpected argument: "++show formula)

hullExistentials:: Formula -> FS Formula
hullExistentials disj = 
  if (noExistentialsInDisjuncts==True) && (countExis disj > 0) then 
    hull disj
  else return disj

countExis:: Formula -> Int
countExis formula = case formula of
  And fs -> sum (map (\f -> countExis f) fs)
  Or fs -> sum (map (\f -> countExis f) fs)
  GEq us -> 0
  EqK us -> 0
  Exists qsvs f -> 1 + countExis f
  _ -> error ("countConjuncts: unexpected argument: "++show formula)

{- Simplify RecPost
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

simplifyRecPost:: RecPost -> FS RecPost
simplifyRecPost recpost@(RecPost mn insouts f oth) = 
  let (quants,noF) = floatQfiers f in
  replaceAppRecPost noF >>= \(markNoF,markAppRecPost) ->
      let actualInsouts = concatMap (\(qsvs,f) -> case f of AppRecPost mn args -> args) markAppRecPost in
      let (quantsArgs,exMarkNoF) = includeQfiers markNoF quants actualInsouts in
      simplify exMarkNoF >>= \sMarkNoF ->
      let sNoF = replaceBackAppRecPost markAppRecPost sMarkNoF in
      let sF = pasteQfiers (quantsArgs,sNoF) in
  return (RecPost mn insouts sF oth)
  
showQ (Forall qsvs f) = show qsvs
showQ (Exists qsvs f) = show qsvs

includeQfiers:: Formula -> [Formula] -> [QSizeVar] -> ([Formula],Formula)
-- ensures: exists (quants: f) = exists ((fst res): (snd res))
includeQfiers f quants insouts = 
  let (nonArgsQ,withArgsQ) = span (\f -> case f of {Exists qsvs _ -> noElemFromFstIsInSnd qsvs insouts; Forall qsvs _ -> noElemFromFstIsInSnd qsvs insouts}) (reverse quants) in
    (reverse withArgsQ,pasteQfiers (reverse nonArgsQ,f))

-- floatQuantifiers is not used
floatQuantifiers:: Formula -> Formula
-- ensures: equivalent(formula,res)
floatQuantifiers formula = 
  pasteQfiers (floatQfiers formula)

pasteQfiers:: ([Formula],Formula) -> Formula
pasteQfiers (qs,nof) = 
  let rqs = reverse qs in
    foldl (\f1 -> \f2 -> case f2 of {Forall qsvs _ -> Forall qsvs f1;Exists qsvs _ -> Exists qsvs f1}) nof rqs

floatQfiers:: Formula -> ([Formula],Formula)
floatQfiers formula = case formula of
  And fs -> 
    let (qss,nofs) = unzip $ map (\f -> floatQfiers f) fs in
      (concat qss,And nofs)
  Or fs ->
    let (qss,nofs) = unzip $ map (\f -> floatQfiers f) fs in
      (concat qss,Or nofs)
  Not f ->
    let (qs,nof) = floatQfiers f in
    let notQs = map (\q -> case q of {Forall q f -> Exists q f;Exists q f -> Forall q f}) qs in
      (notQs,Not nof)
  GEq us -> ([],formula)
  EqK us -> ([],formula)
  AppRecPost mn insouts -> ([],formula)
  Forall qsvs f -> 
    let (qs,nof) = floatQfiers f in
      ((Forall qsvs undefined):qs,nof)
  Exists qsvs f ->
    let (qs,nof) = floatQfiers f in
      ((Exists qsvs undefined):qs,nof)
  _ -> error "floatQfiers: unexpected argument"

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

replaceBackAppRecPost:: [Marker] -> Formula -> Formula
replaceBackAppRecPost replPair formula = case formula of
  And fs ->
    And $ map (replaceBackAppRecPost replPair) fs
  Or fs ->
    Or $ map (replaceBackAppRecPost replPair) fs
  Not f -> Not $ (replaceBackAppRecPost replPair) f
  Exists exQsvs f -> Exists exQsvs (replaceBackAppRecPost replPair f)
  Forall forQsvs f -> Forall forQsvs (replaceBackAppRecPost replPair f)
  GEq ups -> formula
  EqK ups -> -- any ups contain a marker? replace it back with AppCAbst
    let apps = catMaybes $ map (\(qsv,f) -> if qsv `elem` fqsv (EqK ups) then Just f else Nothing) replPair in
    case length apps of
      0 -> formula
      1 -> head apps
      2 -> error $ "replaceBackAppRecPost: two fresh variables in the same equality"++show formula
  AppRecPost mn insouts -> error $ "replaceBackAppRecPost: argument should not contain AppRecPost:\n " ++ show formula 

----Affinity Matrix--------------------
type AffinMx = Array (Int,Int) Int
identityA = 0 
-- identityA should not confuse "chooseMaxElem" which computes maximum element from AffinMx matrix

initAffinMx:: Int -> AffinMx
initAffinMx n =
  let gen = take ((n+1)*(n+1)) (numsFrom 0) in
  let l = map (\x -> ((x `quot` (n+1),x `rem` (n+1)),identityA)) gen in
    array ((0,0),(n,n)) l

-- returns the indices corresponding to the maximum element in the matrix
chooseMaxElem:: AffinMx -> (Int,Int)
chooseMaxElem mat = 
  let firstMax = ((0,0),mat!(0,0)) in
  let maxe = foldl (\((mi,mj),amax) -> \((i,j),val) -> if val>=amax then ((i,j),val) else ((mi,mj),amax)) firstMax (assocs mat) in
  fst maxe

showAffinMx:: AffinMx -> String
showAffinMx mat = let ((_,_),(m,n)) = bounds mat in ("- noRows: "++show (m+1) ++ ", noCols: "++show (n+1)++"\n") ++  showMatrix mat (m,n) 0
  where
    showMatrix:: AffinMx -> (Int,Int) -> Int -> String
    showMatrix mat (m,n) i | i==m = showRow mat (m,n) i 0
    showMatrix mat (m,n) i = showRow mat (m,n) i 0 ++ "\n" ++ showMatrix mat (m,n) (i+1)
    showRow:: AffinMx -> (Int,Int) -> Int -> Int -> String
    showRow mat (m,n) i j | j>n = ""
    showRow mat (m,n) i j = show (mat!(i,j)) ++ " " ++ showRow mat (m,n) i (j+1)



{-
template formula = case formula of
  And fs ->
  Or fs ->
  Not f ->
  GEq us ->
  EqK us ->
  AppRecPost mn insouts ->
  Forall qsvs f ->
  Exists qsvs f ->
  _ -> error ("unexpected argument: "++show formula)
-}

