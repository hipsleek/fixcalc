{- |Provides operators for Hulling and Widening on the powerset domain of polyhedra -}
-----Operators common to BU and TD
module ImpHullWiden(
  widen,          -- |Disjunctive widening. Given xs and ys, requires that length xs=length ys.
  widenOne,       -- |Conjunctive widening. 
  combHull,       -- |Given F in DNF-form, performs convex-hulling and returns a conjunctive formula.
  combSelHull,    -- |Given F in DNF-form and m, performs selective hulling. Ensures that length(res)=m. The third argument is not used.
  countDisjuncts, -- |Given F in DNF-form (e.g. result of simplify), returns the number of disjuncts from F.
  getDisjuncts,   -- |Given F in DNF-form (e.g. result of simplify), returns a list with the disjuncts from F.
  Disjunct,       -- |Conjunctive formula. The Or constructor is not used.
  DisjFormula,    -- |Formula in DNF form equivalent to (Or [Formula]). The Or constructor is not used in any Formula in the list.
  showDebugMSG
) where
import Fresh(FS,addOmegaStr,putStrFS,putStrNoLnFS,getLineFS,hFlushStdoutFS)
import ImpAST
import ImpConfig(noExistentialsInDisjuncts,Heur(..),FixFlags)
import ImpFormula(simplify,hull,subset)
import MyPrelude(numsFrom,updateList,singleton,concatSepBy)
---------------
import Data.Array(Array,(//),(!),array,assocs,bounds)
import Data.Char(digitToInt,isDigit)
import List(nub,union,(\\))
import Maybe(catMaybes,fromJust)
import Monad(filterM,when)

{- | 0 -> do not show any messages
     1 -> show only loss-of-precision messages
     2 -> show more messages -}
showDebugMSG:: Int
showDebugMSG = 2

type Disjunct = Formula 
type DisjFormula = [Formula] 

----------------------------------
--------Widening powersets--------
----------------------------------
widen:: Heur -> (DisjFormula,DisjFormula) -> FS DisjFormula
-- requires (length xs)=(length ys)
-- ensures (length res)=(length xs)
widen heur (xs,ys) = 
  when (not (length xs == length ys)) (error("ERROR: widen requires two formuale with same number of disjuncts\n"
                                            ++showSet (Or xs) ++ "\n" ++ showSet(Or ys))) >>
  mapM hullExistentials xs >>= \xsNoEx ->
  mapM hullExistentials ys >>= \ysNoEx ->
  addOmegaStr ("# Widen1IN:=" ++ showSet(Or xsNoEx)) >> 
  addOmegaStr ("# Widen2IN:=" ++ showSet(Or ysNoEx)) >> 
  let (mxs,mys) = (map (\x -> Just x) xsNoEx,map (\y -> Just y) ysNoEx) in
  computeMx heur (mxs,mys) >>= \affinMx ->
  iterateMx heur (mxs,mys) affinMx [] >>= \ijs ->
  when (showDebugMSG >= 2) (putStrFS("    Pairs of disjuncts to widen: "++show ijs)) >>
  mapM (\(i,j) -> widenOne (xsNoEx!!i,ysNoEx!!j)) ijs >>= \res ->
  addOmegaStr ("# WidenOUT:=" ++ showSet(Or res)) >> 
  return res
  
computeMx:: Heur -> ([Maybe Disjunct],[Maybe Disjunct]) -> FS AffinMx
-- requires: length disjCrt = length disjNxt
computeMx heur (disjCrt,disjNxt) = 
  let n = length disjCrt-1 in 
  let mx = initAffinMx n in
  computeMx1 heur mx (n,n) 0 (disjCrt,disjNxt)
  where
      computeMx1:: Heur -> AffinMx -> (Int,Int) -> Int -> ([Maybe Disjunct],[Maybe Disjunct]) -> FS AffinMx
      computeMx1 heur mat (m,n) i (disjCrt,disjNxt) | i>n = return mat
      computeMx1 heur mat (m,n) i (disjCrt,disjNxt) = 
        computeRow heur mat (m,n) i 0 (disjCrt,disjNxt) >>= \mat1 ->
        computeMx1 heur mat1 (m,n) (i+1) (disjCrt,disjNxt)

-- computes Affinities for row i
computeRow:: Heur -> AffinMx -> (Int,Int) -> Int -> Int -> ([Maybe Disjunct],[Maybe Disjunct]) -> FS AffinMx
computeRow heur mat (m,n) i j (disjCrt,disjNxt) | j>n = return mat
computeRow heur mat (m,n) i j (disjCrt,disjNxt) = 
  affinity (disjCrt!!i) (disjNxt!!j) heur comb2Widen (nub $ concatMap fqsv (catMaybes (disjCrt++disjNxt))) >>= \affinIJ -> 
  let newmat = mat // [((i,j),affinIJ)] in
  computeRow heur newmat (m,n) i (j+1) (disjCrt,disjNxt)

-- computes Affinities for col j
computeCol:: Heur -> AffinMx -> (Int,Int) -> Int -> Int -> ([Maybe Disjunct],[Maybe Disjunct]) -> FS AffinMx
computeCol heur mat (m,n) i j (disjCrt,disjNxt) | i>n = return mat
computeCol heur mat (m,n) i j (disjCrt,disjNxt) = 
  affinity (disjCrt!!i) (disjNxt!!j) heur comb2Widen (nub $ concatMap fqsv (catMaybes (disjCrt++disjNxt))) >>= \affinIJ -> 
  let newmat = mat // [((i,j),affinIJ)] in
  computeCol heur newmat (m,n) (i+1) j (disjCrt,disjNxt)

iterateMx:: Heur -> ([Maybe Disjunct],[Maybe Disjunct]) -> AffinMx -> [(Int,Int)] -> FS [(Int,Int)]
iterateMx heur (disjCrt,disjNxt) affinMx partIJs = 
  chooseElem heur affinMx >>= \(i,j) ->
  when (showDebugMSG>=1) (putStrFS ("WidenMatrix "++showAffinMx affinMx) >> putStrFS ("Chosen elem is: " ++ show (i,j))) >>
  replaceRelatedWithNoth (disjCrt,disjNxt) (i,j) >>= \(replDisjCrt,replDisjNxt) ->
  if (length (catMaybes replDisjCrt))==0 then return ((i,j):partIJs)
  else 
    computeRow heur affinMx (length replDisjCrt-1,length replDisjCrt-1) i 0 (replDisjCrt,replDisjNxt) >>= \affinMx1->
    computeCol heur affinMx1 (length replDisjCrt-1,length replDisjCrt-1) 0 j (replDisjCrt,replDisjNxt) >>= \affinMx2->
    iterateMx heur (replDisjCrt,replDisjNxt) affinMx2 ((i,j):partIJs)

-- replaces two related disjuncts with Nothing
replaceRelatedWithNoth:: ([Maybe Disjunct],[Maybe Disjunct]) -> (Int,Int) -> FS ([Maybe Disjunct],[Maybe Disjunct])
replaceRelatedWithNoth (disjCrt,disjNxt) (i,j) =
  let disjI = updateList disjCrt i Nothing in
  let disjJ = updateList disjNxt j Nothing in
  return (disjI,disjJ)


----------------------------------
--------Widening on conj domain---
----------------------------------
widenOne:: (Disjunct,Disjunct) -> FS Disjunct
-- requires: fcrt, fnext are conjunctive formulae
widenOne (fcrt,fnext) = 
--    addOmegaStr ("# WidenCrt:=" ++ showSet fcrt) >> 
--    addOmegaStr("# WidenNxt:=" ++ showSet fnext) >>
  closure fcrt >>= \fcrts ->
  mapM (subset fnext) fcrts >>= \suboks ->
  let fcrts' = zip fcrts suboks in
  let fcrt' = filter (\(f,ok) -> ok) fcrts' in
  let fwid = fAnd (map fst fcrt') in
--    addOmegaStr ("# WidenRes:=" ++ showSet fwid) >>
  return fwid

closure:: Disjunct -> FS [Disjunct]
-- requires: f is conjunctive formula
closure f =
  let updSubst = [] in
  let conjs = buildClauses updSubst f in
  let noconst = discoverIneqWithoutNegConstant conjs in
  discover2Ineq conjs >>= \discov ->
  return (conjs++discov++noconst)
  where
    -- input: (i+13<=j)
    -- output: (i<=j)
    discoverIneqWithoutNegConstant:: [Disjunct] -> [Disjunct]
    -- requires: formula is in conjunctive form
    discoverIneqWithoutNegConstant fs = 
      let newfs = map discoverIneqWithoutNegConstant1 fs in
      (nub newfs) \\ fs
    discoverIneqWithoutNegConstant1:: Disjunct -> Disjunct
    discoverIneqWithoutNegConstant1 formula = case formula of
      And fs -> fAnd (map discoverIneqWithoutNegConstant1 fs)
      GEq us -> let newus = filter (\u -> case u of {Const x -> if x<0 then False else True; Coef _ _ -> True}) us in
                GEq newus
      EqK us -> formula
      _ -> error ("unexpected argument: "++show formula)
    
    -- input: (i<=j && 4a<=2+i+3j)
    -- output: (a<=j)
    discover2Ineq:: [Disjunct] -> FS [Disjunct]
    discover2Ineq fs =
      let vars = fqsv (fAnd fs) in
      let singletons = map (\x -> [x]) vars in
      let pairs = genPairs vars in
      mapM (discover2Relation fs vars) (pairs) >>= \newfs ->
      let filtfs = filter (\f -> formulaIsNotEqK f) (nub $ concat newfs) in
      return (filtfs \\ fs)
    discover2Relation:: [Disjunct] -> [QSizeVar] -> [QSizeVar] -> FS [Disjunct]
    discover2Relation fs allvars varsToKeep = hull (fExists (allvars \\ varsToKeep) (fAnd fs)) >>= \fsimpl ->
      return (formulaToConjList fsimpl)
    genPairs:: [a] -> [[a]]
    genPairs xs | length xs <=1 = []
    genPairs (x:xs) = 
      let p1 = map (\y -> [x,y]) xs in
      let p2 = genPairs xs in p1++p2
    formulaToConjList:: Disjunct -> [Disjunct]
    -- requires: formula is in conjunctive form
    formulaToConjList formula = case formula of
      And fs -> concatMap formulaToConjList fs
      GEq us -> [formula]
      EqK us -> [formula]
      _ -> error ("unexpected argument: "++show formula)
    formulaIsNotEqK formula = case formula of
      EqK us -> False
      _ -> True

    buildClauses:: [(QSizeVar,[Update])] -> Disjunct -> [Disjunct]
    buildClauses updSubst f = 
     case f of
       And fs -> concatMap (buildClauses updSubst) fs
       GEq ups -> f:(applyUpdSubst updSubst f)
       EqK ups -> -- [f]
         -- more precise widening if (f2-f1=1) is transformed to (1<=f2-f1 && f2-f1<=1)
         [GEq ups,GEq (map (mulUpdate (-1)) ups)] 
       _ -> error $ "widenOne: argument must be in conjunctive form\n " ++ show f
    -- input: (f1-f3>=0 && f1+f2=0)
    -- output: [(f1,[-f2]),(f2,[-f1])]
    collectUpdSubst:: Disjunct -> [(QSizeVar,[Update])]
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
    -- input: [(f1,[-f2]),(f2,[-f1])]
    -- input: (f1-f3>=0 && f1+f2=0)
    -- output: (f1-f3>=0 && -f2-f3>=0 && f1+f2=0)
    applyUpdSubst:: [(QSizeVar,[Update])] -> Disjunct -> [Disjunct]
    applyUpdSubst subs geq@(GEq _) = catMaybes $ map (\s -> applyOneUpdSubst s geq) subs
    applyOneUpdSubst:: (QSizeVar,[Update]) -> Disjunct -> Maybe Disjunct
    applyOneUpdSubst (qsv,ups) (GEq geqs) =
     let qsvIsIn = any (\u -> case u of {Coef qsv1 i -> qsv==qsv1; _ -> False}) geqs in 
     if qsvIsIn then
       let upsAfterSubs = concatMap (\u -> case u of {Coef qsv1 i -> if (qsv1==qsv) then map (mulUpdate i) ups else [u];_ -> [u]}) geqs in
       Just (GEq upsAfterSubs)
     else Nothing
    
    mulUpdate:: Int -> Update -> Update
    mulUpdate x (Const i) = Const (i*x)
    mulUpdate x (Coef qsv i) = Coef qsv (i*x)

----------------------------------
--------Selective Hull------------
----------------------------------
combSelHull::FixFlags -> DisjFormula -> Formula -> FS DisjFormula
-- requires: disj represents the DNF-form of a formula f (Or fs)
-- requires: m>=1
-- ensures: length(res)=m
combSelHull (m,heur) disj fbase = 
  addOmegaStr ("# SelhullIN:=" ++ showSet(Or disj)) >> 
  (if length disj <= m then return disj
  else case m of
    1 -> combHull disj >>= \h -> return [h]
    _ -> -- assert (1<m<(length disj))
      mapM hullExistentials disj >>= \disjNoEx ->
      let disjM = map (\d -> Just d) disjNoEx in
      when (showDebugMSG>=2) (putStrFS ("####SelHull: start iterating with "++show (length (catMaybes disjM))
                                   ++ " disjuncts:\n" ++ concatSepBy "\n" (map (\mf -> case mf of {Nothing -> "Nothing";Just f -> showSet f}) disjM))) >>
      computeHalfMx heur disjM >>= \affinMx ->
      iterateHalfMx (m,heur) disjM affinMx >>= \relatedDisjM ->
      return (catMaybes relatedDisjM)
    ) >>= \res -> addOmegaStr("# SelhullOUT:=" ++ showSet(Or res)) >> return res

combHull:: DisjFormula -> FS Formula
-- requires: disj represents the DNF-form of a formula f (Or fs)
combHull disj = hull (Or disj)

computeHalfMx:: Heur -> [Maybe Disjunct] -> FS AffinMx
-- ensures: (n,n)=length res, where n=length disj
computeHalfMx heur disj = 
  let n = length disj-1 in 
  let mx = initAffinMx n in
  computeHalfMx1 heur mx (n,n) 0 disj
  where
      computeHalfMx1:: Heur -> AffinMx -> (Int,Int) -> Int -> [Maybe Disjunct] -> FS AffinMx
      computeHalfMx1 heur mat (m,n) i disj | i>n = return mat
      computeHalfMx1 heur mat (m,n) i disj = 
        computeHalfRow heur mat (m,n) i (i+1) disj >>= \mat1 ->
        computeHalfMx1 heur mat1 (m,n) (i+1) disj

-- computes Affinities for second-half of row i, between columns j(first call uses i+1) and n
computeHalfRow:: Heur -> AffinMx -> (Int,Int) -> Int -> Int -> [Maybe Disjunct] -> FS AffinMx
computeHalfRow heur mat (m,n) i j disj | j>n = return mat
computeHalfRow heur mat (m,n) i j disj = 
  affinity (disj!!i) (disj!!j) heur comb2Hull (nub $ concatMap fqsv (catMaybes disj))>>= \affinIJ -> 
  let newmat = mat // [((i,j),affinIJ)] in
  computeHalfRow heur newmat (m,n) i (j+1) disj
-- computes Affinities for upper-half of column j, between rows i(first call uses j-1) and 0
computeHalfCol:: Heur -> AffinMx -> (Int,Int) -> Int -> Int -> [Maybe Disjunct] -> FS AffinMx
computeHalfCol heur mat (m,n) i j disj | i<0 = return mat
computeHalfCol heur mat (m,n) i j disj = 
  affinity (disj!!i) (disj!!j) heur comb2Hull (nub $ concatMap fqsv (catMaybes disj)) >>= \affinIJ -> 
  let newmat = mat // [((i,j),affinIJ)] in
  computeHalfCol heur newmat (m,n) (i-1) j disj

iterateHalfMx:: FixFlags -> [Maybe Disjunct] -> AffinMx -> FS [Maybe Disjunct]
iterateHalfMx (m,heur) disjM affinMx = 
  chooseElem heur affinMx >>= \(i,j) ->
  when (showDebugMSG>=2) (putStrFS ("SelHullMatrix " ++ showAffinMx affinMx) >> putStrFS ("Chosen elem is: " ++ show (i,j))) >>
  when (showDebugMSG>=1 && (affinMx!(i,j))<100) (putStrFS ("SelHull chose disjuncts with less than 100% affinity: "++ show (affinMx!(i,j)))) >>
  replaceRelated disjM (i,j) >>= \replDisjM ->
  when (showDebugMSG>=2) (putStrFS ("####"++show (length (catMaybes replDisjM))++ "\n" 
                               ++ concatSepBy "\n" (map (\mf -> case mf of {Nothing -> "Nothing";Just f -> showSet f}) replDisjM))) >>
  if (length (catMaybes replDisjM))<=m then return replDisjM
  else 
    computeHalfRow heur affinMx (length replDisjM-1,length replDisjM-1) i (i+1) replDisjM >>= \affinMx1->
    computeHalfCol heur affinMx1 (length replDisjM-1,length replDisjM-1) (i-1) i replDisjM >>= \affinMx2->
    computeHalfRow heur affinMx2 (length replDisjM-1,length replDisjM-1) j (j+1) replDisjM >>= \affinMx3->
    computeHalfCol heur affinMx3 (length replDisjM-1,length replDisjM-1) (j-1) j replDisjM >>= \affinMx4->
    iterateHalfMx (m,heur) replDisjM affinMx4

-- replaces two related disjuncts with their hull
replaceRelated:: [Maybe Disjunct] -> (Int,Int) -> FS [Maybe Disjunct]
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

----------------------------------
--------Affinity Matrix-----------
----------------------------------
type AffinMx = Array (Int,Int) Int
identityA = -1 
-- identityA should be smaller than all elements from AffinMx (so that "chooseElem" computes maximum element from AffinMx matrix)

initAffinMx:: Int -> AffinMx
initAffinMx n =
  let gen = take ((n+1)*(n+1)) (numsFrom 0) in
  let l = map (\x -> ((x `quot` (n+1),x `rem` (n+1)),identityA)) gen in
    array ((0,0),(n,n)) l

-- |Returns the indices of either the maximum element in the matrix or chosen by the user with SimInteractiveHeur.
chooseElem:: Heur -> AffinMx -> FS (Int,Int)
chooseElem heur mat = 
  let firstMax = ((0,0),mat!(0,0)) in
  let maxe = foldl (\((mi,mj),amax) -> \((i,j),val) -> if val>=amax then ((i,j),val) else ((mi,mj),amax)) firstMax (assocs mat) in
  case heur of
    SimInteractiveHeur -> 
      putStrFS ("MAX elem is: " ++ show (fst maxe)) >>
      putStrNoLnFS ("Choose an elem: ") >> hFlushStdoutFS >> getLineFS >>= \str -> 
      return (getIndices str (fst maxe))
    _ -> return (fst maxe)

getIndices:: String -> (Int,Int) -> (Int,Int)
getIndices str givenmax = 
  if length str >= 5 && str!!0 == '(' && isDigit (str!!1) && str!!2 == ',' && isDigit (str!!3) && str!!4 == ')' then
    (digitToInt (str!!1), digitToInt (str!!3))
  else givenmax

showAffinMx:: AffinMx -> String
showAffinMx mat = 
  let ((_,_),(m,n)) = bounds mat in 
    ("- noRows: "++show (m+1) ++ ", noCols: "++show (n+1)++"\n") ++  showMatrix mat (m,n) 0
  where
    showMatrix:: AffinMx -> (Int,Int) -> Int -> String
    showMatrix mat (m,n) i | i==m = showRow mat (m,n) i 0
    showMatrix mat (m,n) i = showRow mat (m,n) i 0 ++ "\n" ++ showMatrix mat (m,n) (i+1)
    showRow:: AffinMx -> (Int,Int) -> Int -> Int -> String
    showRow mat (m,n) i j | j>n = ""
    showRow mat (m,n) i j = show (mat!(i,j)) ++ " " ++ showRow mat (m,n) i (j+1)

affinity:: Maybe Formula -> Maybe Formula -> Heur -> (Formula -> Formula -> FS Formula) -> [QSizeVar] -> FS Int
-- requires: f1,f2 represent conjunctive formulae
affinity Nothing _ heur _ _ = return identityA
affinity _ Nothing heur _ _ = return identityA
affinity (Just f1) (Just f2) HausdorffHeur _ fsv =
  mapM (\x -> projectQSV f1 x) fsv >>= \ranges1 ->
  mapM (\x -> projectQSV f2 x) fsv >>= \ranges2 ->
  let distances = map hausdorffDistance (zip ranges1 ranges2) in
  let (inc,dist) = addHDistances distances in
  let maxdist = 1000 in
  let haus = ceiling (fromIntegral (100*inc) / fromIntegral (length fsv+1)) + 
             ceiling (fromIntegral (100*dist) / fromIntegral ((length fsv+1)*maxdist))in
--  putStrFS (concatMap show fsv) >>
--  putStrFS ("haus: " ++ show (length fsv) ++ ":" ++ show inc ++ ":" ++ show dist ++ ":" ++ show haus ++ ":" ++ show (100-haus)) >>
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
        DifferenceHeur -> 
          let n = countDisjuncts fDif in
          let nsteps = if n>4 then 4 else n in
          let disj = getDisjuncts fDif in
          let getAverageConjuncts = (\c -> fromIntegral (countConjuncts c) / (fromIntegral n)) in
          let s = ceiling $ sum (map getAverageConjuncts disj) in
          let diffSteps = 100 - (20*nsteps-s) in
          return diffSteps
        _ -> {- SimilarityHeur, SimInteractiveHeur -}
--          putStrFS("F1:="++showSet f1) >> putStrFS("F2:="++showSet f2) >>
          let (cf1,cf2) = (countConjuncts f1,countConjuncts f2) in
          mset f1 f2 foperation >>= \mSet ->
          let cmset = length mSet in
          let frac = (((fromIntegral cmset / (fromIntegral (cf1+cf2)))*98)+1) in
--          putStrFS("Foper:="++showSet foperation) >>
--          putStrFS("mSet::="++concatMap (\f -> showSet f) mSet) >>
--          putStrFS("affin:="++show cmset ++ "/" ++ show (cf1+cf2) ++ "  " ++ show (ceiling frac)) >>
          return (ceiling frac)
    where
      mset:: Formula -> Formula -> Formula -> FS [Formula]
      -- requires: f1,f2 are conjunctive formulae
      mset f1 f2 foperation =
        let (conjf1,conjf2) = (getConjuncts f1,getConjuncts f2) in
        filterM (\f -> subset foperation f) (conjf1 `union` conjf2)

type Range = (Maybe Int,Maybe Int) 
-- ^A 'Range' value represents an interval: 'Nothing' means Infinity, 'Just' i means the integer i.
-- For example, (Nothing,Just 3) = (-inf,3]
projectQSV:: Formula -> QSizeVar -> FS Range
-- ^'projectQSV' computes from a formula, the range for some qsv.
-- For example, from (x+7>=0 && y>=0 && -x>=0) the range for x is [-7,0]. 
-- requires: f1 is in conjunctive form, without quantifiers.
-- requires: f1 contains at most 2 conjuncts (one upper bound and one lower bound).
projectQSV f1 qsv = 
  let f2 = fExists (fqsv f1 \\ [qsv]) f1 in
  hull f2 >>= \f3 -> 
--  putStrFS ("simpl:= " ++ show f3 ++ "\trange: " ++ show (extractRange f3)) >>
  return (extractRange f3)

extractRange:: Formula -> Range
extractRange formula = case formula of 
  And fs -> intersectRanges (map extractRange fs)
  GEq us -> 
    let coefVars = catMaybes $ map (\u -> case u of {Const _ -> Nothing;Coef _ i -> Just i}) us in
    let sumConsts = sum $ map (\u -> case u of {Const i -> i;Coef _ _ -> 0}) us in
    if (singleton coefVars) then
      let coef = head coefVars in
      case coef of 
        1 -> (Just (-sumConsts), Nothing)
        -1 -> (Nothing,Just sumConsts)
        _ -> error ("extractRange: unexepcted coefficient: "++show formula)
    else error ("extractRange: unexepcted coefficient: "++show formula)
  EqK us -> 
    let coefVars = catMaybes $ map (\u -> case u of {Const _ -> Nothing;Coef _ i -> Just i}) us in
    let sumConsts = sum $ map (\u -> case u of {Const i -> i;Coef _ _ -> 0}) us in
    case length coefVars of
      0 -> (Nothing,Nothing)
      1 -> case (head coefVars) of 
        1 -> (Just (-sumConsts),Just (-sumConsts))
        -1 -> (Just sumConsts,Just sumConsts)
        _ -> error ("extractRange: unexepcted coefficient: "++show formula)
      _ -> error ("extractRange: unexepcted coefficient: "++show formula)
  _ -> error ("extractRange: unexpected argument: "++show formula)
  where
  intersectRanges:: [Range] -> Range
  intersectRanges l | (length l == 2) = case (l!!0,l!!1) of
    ((Nothing,Just i),(Just j,Nothing)) -> if (i>=j) then (Just j,Just i) else error ("intersectRanges: unexpected argument: "++show l)
    ((Just i,Nothing),(Nothing,Just j)) -> if (j>=i) then (Just i,Just j) else error ("intersectRanges: unexpected argument: "++show l)
    ((Nothing,Nothing),r) -> r
    (r,(Nothing,Nothing)) -> r
    _ -> error ("intersectRanges: unexpected argument: "++show l)
  intersectRanges l | (length l /= 2) = error ("intersectRanges: unexpected argument: "++show l)
    
hausdorffDistance:: (Range,Range) -> Maybe Int
-- ^computes the Hausdorff distance between two intervals. The result Nothing represents Infinity.
hausdorffDistance ((Nothing,Just a), (Nothing,Just b)) = Just (abs (b-a))
hausdorffDistance ((Just a1,Just a2), (Just b1,Just b2)) = Just (abs (b1-a1))
hausdorffDistance ((Just a,Nothing), (Just b,Nothing)) = Just (abs (b-a))
hausdorffDistance (_,_) = Nothing

addHDistances:: [Maybe Int] -> (Int,Int)
-- ^given a list of Hausdorff distances, returns a tuple (m,s), 
-- where m is the number of incompatible dimensions and s is the sum of the distances along the compatible dimensions
addHDistances [] = (0,0)
addHDistances  (Nothing:rest) = let (inc,s) = addHDistances rest in (inc+1,s)
addHDistances ((Just a):rest) = let (inc,s) = addHDistances rest in (inc,s+a)

getDisjuncts:: Formula -> [Formula]
-- requires formula is in DNF-form (result of simplify)
getDisjuncts formula = 
  case formula of
    And _ -> 
      if countDisjuncts formula == 1 then [formula] 
      else error ("getDisjuncts: "++show formula)
    Or fs -> 
      if countDisjuncts formula == length fs then fs 
      else error ("getDisjuncts: "++show formula)
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
  Exists qsvs f -> 
    if countDisjuncts f == 1 then [formula] 
    else error ("getConjuncts: unexpected argument: "++show formula)
  _ -> error ("getConjuncts: unexpected argument: "++show formula)

countConjuncts:: Formula -> Int
-- requires: formula is conjunctive
countConjuncts formula = case formula of
  And fs -> sum (map (\f -> countConjuncts f) fs)
  GEq us -> 1
  EqK us -> 1
  Exists qsvs f -> 
    if countDisjuncts f == 1 then countConjuncts f 
    else error ("countConjuncts: unexpected argument: "++show formula)
  _ -> error ("countConjuncts: unexpected argument: "++show formula)

hullExistentials:: Formula -> FS Formula
hullExistentials disj = 
  if (noExistentialsInDisjuncts==True) && (countExis disj > 0) then 
    when (showDebugMSG>=1) (putStrFS ("EXISTENTIAL that will be hulled:="++showSet disj)) >>
    hull disj
  else return disj

countExis:: Formula -> Int
countExis formula = case formula of
  And fs -> sum (map (\f -> countExis f) fs)
  Or fs -> sum (map (\f -> countExis f) fs)
  GEq us -> 0
  EqK us -> 0
  Exists qsvs f -> 1 + countExis f
  _ -> error ("countExis: unexpected argument: "++show formula)

