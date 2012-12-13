{- |Fixed point analysis that is used in (1) bug discovery from "ImpOutInfer", (2) array bound check elimination from "ImpTypeInfer" and 
  (3) FixedPoint Calculator from "FixCalc".
-}
module ImpFixpoint2k(
  fixpoint2k, 
  bottomUp2k,   
  bottomUp_mr,
  bottomUp2k_gen,
  topDown2k,
  fixTestBU,
  fixTestTD,
  getOneStep,
  subrec,
  combSelHull,  -- |Function re-exported from "ImpHullWiden".
  getDisjuncts, -- |Function re-exported from "ImpHullWiden".
  widen         -- |Function re-exported from "ImpHullWiden".
) where
import Fresh(FS,fresh,takeFresh,addOmegaStr,writeOmegaStrs,getFlags,putStrFS,getCPUTimeFS)
import ImpAST
import ImpConfig(showDebugMSG,Heur(..),fixFlags,FixFlags,simplifyCAbst,simulateOldFixpoint,useSelectiveHull,widenEarly)
import ImpFormula(debugApply,noChange,simplify,subset,recTheseQSizeVars,pairwiseCheck,equivalent)
import ImpHullWiden(widen,widenOne,combHull,combSelHull,countDisjuncts,getDisjuncts,DisjFormula)
import MyPrelude
---------------
import List((\\),nub,find,zip4,zip5,zip)
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
      (if simplifyCAbst flags then
        newSimplifyEntireRecPost recPost
      else return recPost) >>= \sRecPost@(RecPost _ sf _) ->
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
    
bottomUp2k_gen :: [RecPost] -> [FixFlags] -> [Formula] -> FS [(Formula,Int)] 
bottomUp2k_gen recpost flagsl initFormula = 
  addOmegaStr("+++++++++++++++++++++++++++") >> 
  addOmegaStr("New fix point iteration") >> 
  addOmegaStr("+++++++++++++++++++++++++++") >> 
  getFlags >>= \flags -> 
  subrec_gen recpost initFormula >>= \f1 -> 
  mapM (\f2 -> simplify f2) f1 >>= \initf1 -> 
  mapM (\f1r -> addOmegaStr ("# F1:="++showSet f1r)) initf1 >>
  subrec_gen recpost initf1 >>= \f1 -> 
  mapM (\f2 -> simplify f2) f1 >>= \initf2 -> 
  mapM (\f1r -> addOmegaStr ("# F2:="++showSet f1r)) initf2 >>
  subrec_gen recpost initf2 >>= \f1 -> 
  mapM (\f2 -> simplify f2) f1 >>= \initf3 -> 
  mapM (\f1r -> addOmegaStr ("# F3:="++showSet f1r)) initf3 >>
  mapM (\f3r -> (pairwiseCheck f3r)) initf3 >>= \pwF3l -> 
  let mdisj = map (\(pwF3,(m,heur)) -> (min m (countDisjuncts pwF3))) (zip pwF3l flagsl) in
  let zipf1 = zip4 initf1 initf3 mdisj (snd (unzip flagsl)) in 
  -- hull
  -- substitution
  mapM (\(f1r,f3r,mdisj,heur) -> combSelHull (mdisj,heur) (getDisjuncts f3r) f1r) zipf1 >>= \hf1 -> 
  subrec_gen recpost (map (\x -> (Or x)) hf1) >>= \f1 -> 
  mapM (\f2 -> simplify f2) f1 >>= \initf4 -> 
  mapM (\f1r -> addOmegaStr ("# F4:="++showSet f1r)) initf4 >>
          -- mapM (\f3r -> (pairwiseCheck f3r)) initf4 >>=
          -- \hf2 ->
          --      substitution
          --     subrec_gen recpost initf4
          --     >>= \f1 -> mapM (\f2 -> simplify f2) f1
          --     >>= \initf5 -> mapM (\f1r -> addOmegaStr ("# F5:="++showSet f1r)) initf5 >>
          --     mapM (\f3r -> (pairwiseCheck f3r)) initf4 >>=
          --     \hullf2 ->
          --     subrec_gen recpost initf5
          --     >>= \f1 -> mapM (\f2 -> simplify f2) f1
          --     >>= \initf6 -> mapM (\f1r -> addOmegaStr ("# F5:="++showSet f1r)) initf4 >>
  -- hull again  
  let mdisj = map (\(pwF3,(m,heur)) -> (min m (countDisjuncts pwF3))) (zip initf4 flagsl) in              
  let zipf1 = zip4 initf1 initf4 mdisj (snd (unzip flagsl)) in 
  mapM (\(f1r,f6r,mdisj,heur) -> combSelHull (mdisj,heur) (getDisjuncts f6r) f1r) zipf1 >>= \s3 ->   
  -- call to iter 
  iterBU2k_gen recpost (zip mdisj (snd (unzip flagsl))) s3 initf1 (map (\x->4) initf1) 

iterBU2k_gen:: [RecPost] -> [FixFlags] -> [DisjFormula] -> [Formula] -> [Int] -> FS [(Formula,Int)]
iterBU2k_gen recpost flags scrtl fbasel cntl =
  let scrt_or = map (\x -> (Or x)) scrtl in
  subrec_gen recpost scrt_or >>= \fn -> 
  mapM (\f -> simplify f) fn >>= \fnextl ->
  let zipf = zip5 cntl scrtl fnextl fbasel flags in
  mapM (\(cnt,scrt,fnext,fbase,(m,heur)) ->
             if (cnt>maxIter) then return ([fTrue],-1)
             else addOmegaStr ("# F"++ show cnt ++ ":="++showSet fnext) >>
                  combSelHull (m,heur) (getDisjuncts fnext) fTrue 
                  >>= \fnextHMany -> widen heur (scrt,fnextHMany) 
                                     >>= \wl -> return (wl, cnt)) zipf >>= \snext_cnt ->
  let (snextl, cntll) = unzip snext_cnt in
  let snextl_or = map (\x -> (Or x)) snextl in
  addOmegaStr("++++++++++++++++++++++++++++++++++")>>
  addOmegaStr("After widenning: " ++ (foldl (\x -> \y -> x ++" "++(show y)) "" snextl_or)) >>
  addOmegaStr("++++++++++++++++++++++++++++++++++")>>
  fixTestBU_gen recpost snextl_or >>= \fixokl -> 
  let fixok = foldl (\x -> \y -> x&&y) True fixokl in 
  if fixok 
  then 
    mapM (\(snext, cnt) -> pairwiseCheck (Or snext) >>= \pw -> return (pw,cnt)) snext_cnt >>= \r -> return r
  else 
    addOmegaStr("++++++++++++++++++++++++++++++++++") >>
    addOmegaStr("Didn't reach fixpoint yet -> iterate again") >>
    addOmegaStr("++++++++++++++++++++++++++++++++++") >>
    iterBU2k_gen recpost flags snextl fbasel (map (\x -> if (x /= -1) then x+1 else x) cntll)

         
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

--cris
fixTestBU_mr:: RecPost -> RecPost-> Formula -> Formula -> FS Bool
fixTestBU_mr recpost1 respost2 candidate1 candidate2 = 
    addOmegaStr ("#\tObtained postcondition?") >>
    subrec_mr recpost1 respost2 candidate1 candidate2 >>= \fnext -> 
    subset fnext candidate1

fixTestBU_gen:: [RecPost] -> [Formula] -> FS [Bool]
fixTestBU_gen recpost candidate = 
  subrec_gen recpost candidate >>=
  \f -> let zipf = zip f candidate in mapM (\(f,c) -> (subset f c)) zipf

--cris
subrec_mr :: RecPost -> RecPost -> Formula -> Formula -> FS Formula
subrec_mr (RecPost formalMN1 f1 (formalI1,formalO1,qsvByVal1)) 
          (RecPost formalMN2 _ (formalI2,formalO2,qsvByVal2))
          f2 f3 =
  subrec_mr1 f1 f2 f3
  where 
    subrec_mr1:: Formula -> Formula -> Formula -> FS Formula
    subrec_mr1 f g h = case f of 
      And fs ->  mapM (\x -> subrec_mr1 x g h) fs >>= \res -> return (And res)
      Or fs -> mapM (\x -> subrec_mr1 x g h) fs >>= \res -> return (Or res)
      Exists vars ff -> subrec_mr1 ff g h >>= \res -> return (Exists vars res)
      GEq us -> return f
      EqK us -> return f
      AppRecPost actualMN actualIO ->
          if (formalMN1==actualMN) then
              if not (length (formalI1++formalO1) == length actualIO) then 
                  error $ "subrec: found different no of QSVs for CAbst:\n " ++ show f
              else
                 let rho = zip (formalI1++formalO1) actualIO in
                 debugApply rho g >>= \rhoG -> return $ fAnd [rhoG,noChange qsvByVal1]
          else if (formalMN2==actualMN) then
                   if not (length (formalI2++formalO2) == length actualIO) then
                       error $ "subrec: found different no of QSVs for CAbst:\n " ++ show f
                   else
                       let rho = zip (formalI2++formalO2) actualIO in
                       debugApply rho h >>= \rhoH ->
                           return $ fAnd [rhoH,noChange qsvByVal2]
               else            
                   error "subrec_mr: input error detected" 
      _ -> error ("unexpected argument: "++show f)

subrec_gen1 :: RecPost -> [RecPost] -> [Formula] -> FS Formula
subrec_gen1 rp r g = 
  case rp of
   RecPost formalMN1 f (formalI,formalO,qsvByVal) ->
    addOmegaStr("+++++++++++++++++++++++++++++") >>
    addOmegaStr("Subst for " ++ show f ++ ":") >>
    addOmegaStr("+++++++++++++++++++++++++++++") >>
    subrec1 f r g
     where 
      subrec1:: Formula -> [RecPost] -> [Formula] -> FS Formula
      subrec1 f r g = 
         case f of 
            And fs -> mapM (\x -> subrec1 x r g) fs >>= \res -> return (And res)
            Or fs -> mapM (\x -> subrec1 x r g) fs >>= \res -> return (Or res)
            Exists vars ff -> subrec1 ff r g >>= \res -> return (Exists vars res)
            GEq us -> return f
            EqK us -> return f
            AppRecPost actualMN actualIO ->
              let func = zip r g in
              let func_app = find (\x -> case (fst x) of
                                       RecPost formalMN2 f2 (formalI2,formalO2,qsvByVal2) -> (actualMN == formalMN2)
                                       _ -> False) func in
              case func_app of
                Nothing -> error "subrec_gen: input error detected" 
                Just (RecPost formalMN2 f2 (formalI2,formalO2,qsvByVal2), f3) ->
                    if not (length (formalI2++formalO2) == length actualIO) then
                           error $ "subrec: found different no of QSVs for CAbst:\n " ++ show f
                       else
                           let rho = zip (formalI2++formalO2) actualIO in
                           addOmegaStr ("before subst: " ++ show f3) >> simplify f3 >>= \f3s ->
                           debugApply rho f3s  >>= \rhof3 -> simplify rhof3 >>= \rhof31 -> addOmegaStr ("after subst: " ++ show rhof31) >>= 
                           \_ -> return $ (fAnd [rhof31,noChange qsvByVal2])
            _ -> error ("unexpected argument: "++show f)
   _ -> error "subrec_gen: input error detected"


subrec_gen :: [RecPost] -> [Formula] -> FS [Formula]
subrec_gen rp f  = mapM (\x -> subrec_gen1 x rp f) rp

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
  addOmegaStr ("# G1:="++showRelation oneStep) >>
  compose g1 oneStep >>= \gcomp ->
  pairwiseCheck (fOr [g1,gcomp]) >>= \g2 -> 
  addOmegaStr ("# G2:="++showRelation (ins,recs,g2)) >>
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
    addOmegaStr ("# G" ++ show (cnt) ++ " hulled to G" ++ show (cnt) ++ "r") >>
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
  
--cris
bottomUp_mr:: RecPost -> RecPost -> FS (Formula,Int)
bottomUp_mr recpost1 recpost2 =
  subrec_mr recpost1 recpost2 fFalse fFalse >>= \f1 -> simplify f1 >>= \f1r ->
  subrec_mr recpost2 recpost1 fFalse fFalse >>= \f2 -> simplify f2 >>= \f2r ->
  addOmegaStr ("# F1a:="++showSet f1r) >>
  addOmegaStr ("# F1b:="++showSet f2r) >>
  
  subrec_mr recpost1 recpost2 f1r f2r >>= \f3 -> simplify f3 >>= \f3r -> 
  subrec_mr recpost2 recpost1 f2r f1r >>= \f4 -> simplify f4 >>= \f4r -> 
  addOmegaStr ("# F2a:="++showSet f3r) >>
  addOmegaStr ("# F2b:="++showSet f4r) >>
  
  subrec_mr recpost1 recpost2 f3r f4r >>= \f5 -> simplify f5 >>= \f5r -> 
  subrec_mr recpost2 recpost1 f4r f3r >>= \f6 -> simplify f6 >>= \f6r -> 
  addOmegaStr ("# F3a:="++showSet f5r) >>
  addOmegaStr ("# F3b:="++showSet f6r) >>

  getFlags >>= \flags -> 
--  if useSelectiveHull flags then
--    combSelHullBase (getDisjuncts f5r) f1r >>= \s4 ->
--    iterBU recpost1 f5r s4 f1r 4
--  else 
  combHull (getDisjuncts f5r) >>= \f5H -> 
  combHull (getDisjuncts f6r) >>= \f6H -> 
  iterBUConj_mr recpost1 recpost2 f5r f6r f5H f6H 4


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

-- cris
iterBUConj_mr:: RecPost -> RecPost -> Formula -> Formula -> Formula -> Formula -> Int -> FS (Formula,Int)
-- requires: scrt is in conjunctive form
iterBUConj_mr recpost1 recpost2 fcrt gcrt fcrtH gcrtH cnt =
  if (cnt>maxIter) then return (fTrue,-1)
  else
    subrec_mr recpost1 recpost2 fcrt gcrt >>= \fn -> simplify fn >>= \fnext ->
    subrec_mr recpost2 recpost1 gcrt fcrt >>= \gn -> simplify gn >>= \gnext ->
    addOmegaStr ("# F"++ show cnt ++ ":="++showSet fnext) >>
    combHull (getDisjuncts fnext) >>= \snext ->
    widenOne (fcrtH,snext) >>= \fcrtW ->
    combHull (getDisjuncts gnext) >>= \tnext ->
    widenOne (gcrtH,tnext) >>= \gcrtW ->
    fixTestBU_mr recpost1 recpost2 fcrtW gcrtW >>= \fixok ->
      if fixok then addOmegaStr ("# Result F "++ show cnt ++ ":="++showSet fcrtW) >> return (fcrtW,cnt)
      else iterBUConj_mr recpost1 recpost2 fnext gnext snext tnext (cnt+1)  

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
  classify disj base >>= \(nonRec,rec1) ->
  -- it should not happen that length nonRec==0 or length rec==0
  -- but it happens! for bsearch,mergesort,FFT
  (case length nonRec of {0 -> return fTrue; 1 -> return (head nonRec); _ -> combHull nonRec}) >>= \nonRecH ->
  (case length rec1 of {0 -> return fTrue; 1 -> return (head rec1); _ -> combHull rec1}) >>= \recH ->
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
  addOmegaStr ("#####simplifyRecPost") >>
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
  EqK ups -> -- any ups contain a marker? replace it back with AppRecPost
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

-------Bottom-up fixpoint----------------------------------    
--        CAbst -> initArr := {[s,i,j]: exists(s',i',j':
--           (i>j) or (0<=i<s & i<=j & initArr(s',i',j') & s=s' & i'=i+1 & j'=j))}; 
--        
--        f1 := subrec CAbst False
--        f2 := subrec CAbst f1
--        f3 := subrec CAbst f2
--        (fNonRec,f3Rec) := selHull f3 f1
--        
--        f4 := subrec CAbst f3
--        (fNonRec,f4Rec) := selHull f4 f1
--        f3WRec := widen f3Rec f4Rec
--        f3W := fNonRec OR f3WRec
--        f4' := subrec CAbst f3W
--        f3W;f4'; f4' subset f3W;
--
-- iter(CAbst,f1,fNonRec,f4,f4Rec)       
--        f5 := subrec CAbst f4
--        (fNonRec,f5Rec) := selHull f5 f1
--        f4WRec := widen f4Rec f5Rec
--        f4W := fNonRec OR f4WRec
--        f5' := subrec CAbst f4W
--        f4W;f5'; f5' subset f4W;
-----------------------------------------------------------    
-------Top-down fixpoint-----------------------------------    
--        G := REC(i,i') - collect from the CAbst, contexts corresponding to recursive calls (call replaced by TRUE)
--        G :={[s,i,j]->[s',i',j']:
--                 ( (0<=i<s & i<=j) & (0<=i'<s' & i'<=j')
--                  & i'=i+1 & s'=s & j'=j)}; 
--        G1 := hull G;
--        G2 := hull(G1 union (G1 compose G));
--        G3 := hull(G2 union (G2 compose G));
--        
--        G4  := hull(G3 union (G3 compose G));
--        G3w := {[s,i,j] -> [s,i',j] : 0 <= i < i' <= j, s-1};#widen G3 G4
--        G4' := hull(G3w union (G3w compose G));
--        G3w;G4'; G4' subset G3w; 
-- iter(G,G4)       
--        G5  := hull(G4 union (G4 compose G));
--        G4w := widen G4 G5;
--        G5' := hull(G4w union (G4w compose G));
--        G4w;G5'; G5' subset G4w;
--        
--        #####2 series - more precise because Gs are not hulled - larger formulae
--        
--        G := REC(i,i') - collect from the CAbst, contexts corresponding to recursive calls (call replaced by TRUE)
--        G1 := G;
--        H1 := hull G;
--        
--        G2 := G1 compose G;
--        H2 := hull(H1 union G2);
--        
--        G3 := G2 compose G;
--        H3 := hull(H2 union G3);
-- iter(G,G3,H3)       
--        G4 := G3 compose G;
--        H4 := hull(H3 union G4);
--        H3w:={[s,i,j] -> [s,i',j] : 0 <= i < i' <= s-1, j}; # H3w := widen H3 H4
--        H4' := hull(H3w union G4);
--        H3w;H4'; H4' subset H3w; 
-----------------------------------------------------------        
