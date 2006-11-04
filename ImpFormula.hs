module ImpFormula where
import Fresh(FS(..),fresh,takeFresh,addOmegaStr,getFlags,putStrFS)
import ImpAST
import ImpConfig(isIndirectionIntArray,whatHull,Hull(..))
import InSolver(impSubset,impSimplify,impGist,impHull,impConvexHull,impPairwiseCheck)
import MyPrelude
------------------------------------------
import List(nub,(\\),intersect,union)
import Maybe(catMaybes)

--To decouple the whole project from Omega library (and linux) use dummy functions like below:
--impSimplify:: Relation -> FS Formula
--impSimplify r1 = return r1
--impGist:: Relation -> Relation -> FS Formula
--impGist r1 r2 = return r1
--impSubset:: Relation -> Relation -> FS Bool
--impSubset r1 r2 = return True

equivalent:: Formula -> Formula -> FS Bool
equivalent r1 r2 =
  subset r1 r2 >>= \b1 ->
  subset r2 r1 >>= \b2 ->
  return (b1 && b2)

simplify:: Formula -> FS Formula
simplify f = 
  impSimplify (fqsv f,[],f)

subset:: Formula -> Formula -> FS Bool
subset f1 f2 = impSubset (fqsv f1,[],f1) (fqsv f2,[],f2)

hull:: Formula -> FS Formula
hull f = 
  getFlags >>= \flags ->
  case whatHull of
    Hull -> impHull (fqsv f,[],f)
    ConvexHull -> impConvexHull (fqsv f,[],f)
    
type Range = (Maybe Int,Maybe Int) -- (Nothing,Just 3) = (-inf,3]
-- compute a range for the given qsv
-- from (x+7>=0 && y>=0 && -x>=0) for x, the result is [-7,0]
projectQSV:: Formula -> QSizeVar -> FS Range
-- requires: f1 is in conjunctive form, without quantifiers
-- requires: f1 contains at most 2 conjuncts (one upper bound and one lower bound)
projectQSV f1 qsv = 
  let f2 = fExists (fqsv f1 \\ [qsv]) f1 in
  hull f2 >>= \f3 -> 
  putStrFS ("simpl:= " ++ show f3 ++ "\trange: " ++ show (extractRange f3)) >>
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
hausdorffDistance ((Nothing,Just a), (Nothing,Just b)) = Just (abs (b-a))
hausdorffDistance ((Just a1,Just a2), (Just b1,Just b2)) = Just (abs (b1-a1))
hausdorffDistance ((Just a,Nothing), (Just b,Nothing)) = Just (abs (b-a))
hausdorffDistance (_,_) = Nothing

addHDistances:: [Maybe Int] -> (Int,Int)
addHDistances [] = (0,0)
addHDistances  (Nothing:rest) = let (inc,s) = addHDistances rest in (inc+1,s)
addHDistances ((Just a):rest) = let (inc,s) = addHDistances rest in (inc,s+a)

pairwiseCheck:: Formula -> FS Formula
pairwiseCheck f = impPairwiseCheck (fqsv f,[],f)

--checks that underlying types of ty1 and ty2 are the same
--it does not check whether the indices of an array have the same type. All indices are assumed to be TyInt!
sameBaseTy:: AnnoType -> AnnoType -> Bool
sameBaseTy ty1 ty2 = case (ty1,ty2) of
  (PrimBool{anno=a},PrimBool{anno=b}) -> True
  (PrimFloat{},PrimFloat{}) -> True
  (PrimInt{},PrimInt{}) -> True
  (PrimVoid{},PrimVoid{}) -> True
  (ArrayType{elemType=eTy1,indxTypes=iTys1},ArrayType{elemType=eTy2,indxTypes=iTys2}) -> 
    let sameElem= sameBaseTy eTy1 eTy2 in
    let sameNoDimensions = (length iTys1==length iTys2)
    in and $ sameElem:sameNoDimensions:[]
  (_,_) -> False

-------Rename - construct substitution----
--verifies that ty1 and ty2 have the same underlying type
--if error should be more informative: move sameBaseTy? to place where rename is called
type Subst = [(QSizeVar,QSizeVar)]
inverseSubst:: Subst -> Subst
inverseSubst [] = []
inverseSubst ((x1,x2):xs) = (x2,x1):(inverseSubst xs)

rename:: AnnoType -> AnnoType -> FS (Maybe Subst)
rename ty1 ty2 =
  case (ty1,ty2) of
    (ty1,TopType{}) -> return (Just [])
    (TopType{},ty2) -> return (Just [])
    (_,_) -> 
      fsvPUTy ty1 >>= \svs1 ->
      fsvPUTy ty2 >>= \svs2 ->
      if (sameBaseTy ty1 ty2 && (length svs1 == length svs2)) then
        return $ Just (zip svs1 svs2)
      else return Nothing
  
-------Apply Substitution to Formula------
--prepareSubst is NECESSARY for recursive functions
--checks whether the substitution constructed by rename function has distinct elements. 
--And it SHOULD have: types are fresh, size variables should not be duplicated.
debugApply:: Subst -> Formula -> FS Formula
debugApply subst f = 
  let from = fst (unzip subst) in
  let to = snd (unzip subst) in
  let safeSubstFS = 
        if (length (nub from)) == (length from) then
            if null (from `intersect` to) then
              return subst 
            else prepareSubst subst []
        else error $ "debugApply: substitution does not have unique args: " ++ show subst
  in  safeSubstFS >>= \safeSubst ->
  return (apply safeSubst f)
  
-- Problem: if the input subst is [c->d,d->e], its application depends on the order of its pairs
-- Solution (Florin): transform [c->d,d->e] to [c->f0,d->e,f0->d]
prepareSubst:: Subst -> Subst -> FS Subst
prepareSubst [] putToEnd = return putToEnd
prepareSubst ((s1,s2):ss) putToEnd =
  fresh >>= \fsh ->
  let fshQsv = (SizeVar fsh,Unprimed) in
  prepareSubst ss ((fshQsv,s2):putToEnd) >>= \preparedSS ->
  return ((s1,fshQsv):preparedSS)

apply:: Subst -> Formula -> Formula
apply [] f = f
apply (s:ss) f = apply ss (applyOne (fst s,snd s) f)

applyOne:: (QSizeVar,QSizeVar) -> Formula -> Formula
applyOne (fromSV,toSV) f = case f of
  And formulae -> And (map (\f -> applyOne (fromSV,toSV) f) formulae)
  Or formulae -> Or (map (\f -> applyOne (fromSV,toSV) f) formulae)
  Not formula -> Not (applyOne (fromSV,toSV) formula)
  Exists otherSVs formula -> 
    if (elem fromSV otherSVs) 
      then f 
      else Exists otherSVs (applyOne (fromSV,toSV) formula)
  Forall otherSVs formula -> 
    if (elem fromSV otherSVs) 
      then f 
      else Forall otherSVs (applyOne (fromSV,toSV) formula)
  GEq updates -> GEq (map (\u -> applyOneToUpdate (fromSV,toSV) u) updates)
  EqK updates -> EqK (map (\u -> applyOneToUpdate (fromSV,toSV) u) updates)
--  EqKCond updates -> EqKCond (map (\u -> applyOneToUpdate (fromSV,toSV) u) updates)
  AppCAbst lit otherSVs resultSVs -> 
    if null (otherSVs `intersect` resultSVs) then
      AppCAbst lit (map (\otherSV -> if otherSV==fromSV then toSV else otherSV) otherSVs)
                   (map (\resultSV -> if resultSV==fromSV then toSV else resultSV) resultSVs)
    else error $ "applyOne: malformed AppCAbst: same QSVs for arguments and results\n"++show f
  AppRecPost lit insouts -> 
      AppRecPost lit (map (\insout -> if insout==fromSV then toSV else insout) insouts)
  _ -> error ("applyOne: unexpected argument:" ++ showSet(fqsv f,f))
  
applyOneToUpdate:: (QSizeVar,QSizeVar) -> Update -> Update
applyOneToUpdate (fromSV,toSV) up = case up of
  Const int -> up
  Coef otherSV int -> if otherSV==fromSV then Coef toSV int else up

noChange:: [QSizeVar] -> Formula
noChange qszVars = 
  let {f = \qs -> 
    case qs of
      (s,Primed) -> error $ "noChange: argument should not contain primed size variable"
      (s,Unprimed) -> EqK [Coef (s,Unprimed) 1,Coef (s,Primed) (-1)]}
  in 
  let fs = map f qszVars in
    fAnd fs

-- phi may contain primed qsvs which must be unprimed
composition:: [QSizeVar] -> Formula -> Formula -> FS Formula
composition u delta phi = 
-- Incorrect simplification: (x'=0) compose_{x} (0=0) = (x'=0)
--  let s = assertAllUnprimed (u `intersect` (unprimeTheseQSizeVars $ fqsv phi)) in
  let s = u in
  if (null s) then 
    return $ And[delta,phi]
  else
    takeFresh (length s) >>= \fshies -> 
    let r = map (\f -> (SizeVar f,Unprimed)) fshies in
    let rho = zip s r in
    let sp = map (\(sv,Unprimed) ->(sv,Primed)) s in 
    let rhop = zip sp r in
    debugApply rhop delta >>= \rhopDelta ->
    debugApply rho phi >>= \rhoPhi ->
    return $ Exists r (And[rhopDelta,rhoPhi]) -- r is fresh. Exists can be used instead of fExists

-- phi should not contain primed qsvs 
ctxImplication:: [QSizeVar] -> Formula -> Formula -> FS Bool
ctxImplication u delta phi =
  let s = assertAllUnprimed (u `intersect` (fqsv phi)) in
  let sp = primeTheseQSizeVars s in
  let rhoPhi = apply (zip s sp) phi in
  let relDelta = (fqsv delta,[],delta) in
  let relPhi = (fqsv rhoPhi,[],rhoPhi) in
   		impSubset relDelta relPhi

-- phi should not contain primed qsvs 
-- better hull both formulae before gisting
ctxSimplify::[QSizeVar] -> [QSizeVar] -> Formula -> Formula -> Formula -> FS Formula
ctxSimplify v u delta phi toGistWith = 
  let s = assertAllUnprimed (u `intersect` (fqsv phi)) in
  let sp = primeTheseQSizeVars s in
  let rhoPhi = apply (zip s sp) phi in
--    addOmegaStr ("PHI:=" ++ showSet rhoPhi) >>
  let satisf = (fOr [(fNot delta),rhoPhi]) in
  let f1 = fForall ((fqsv satisf) \\ v) satisf in
--    addOmegaStr ("CTX:=" ++ showSet delta) >>
--    addOmegaStr ("PRE:=" ++ showSet f1) >>
  let f2 = fExists ((fqsv toGistWith) \\ v) toGistWith in
--    addOmegaStr ("TO_GIST_WITH:=" ++ showSet f2) >>
  let rel1 = (fqsv f1,[],f1) in
  let rel2 = (fqsv f2,[],f2) in
    impGist rel1 rel2

-- Before composition, ctxImplication and ctxSimplify(Rec):
-- size variables from U (to be linked) are checked not be Primed! Should not happen - and may be disabled later.
assertAllUnprimed:: [QSizeVar] -> [QSizeVar]
assertAllUnprimed = map (\qs -> case qs of
  (sv,Primed) -> error $ "assertAllUnprimed: arguments should not be primed"
  (sv,Recursive) -> qs
  (sv,Unprimed) -> qs)

---- Removes EqKCond from a formula
--stripCond:: Formula -> Formula
--stripCond (And fs) = And (map stripCond fs)
--stripCond (Or fs) = Or (map stripCond fs)
--stripCond (Not f) = Not (stripCond f)
--stripCond (EqK ups) = EqK ups
--stripCond (EqKCond ups) = tr "\n##" fTrue
--stripCond (GEq ups) = GEq ups
--stripCond (Exists qsvs f) = Exists qsvs (stripCond f)
--stripCond (Forall qsvs f) = Forall qsvs (stripCond f)
--stripCond f@(AppCAbst name _ _) = f


-------Selectors from Formulae------------
outfqsv:: Outcomes -> [QSizeVar]
outfqsv [OK phi1,ERR phi2] = fqsv phi1 ++ fqsv phi2

--extract size variables from a formula without keeping DUPLICATES
fqsv:: Formula -> [QSizeVar]
fqsv f = nub $ case f of 
  And formulae -> concatMap (\f -> fqsv f) formulae
  Or formulae -> concatMap (\f -> fqsv f) formulae
  Not formula -> fqsv formula
  Exists otherSVs formula -> 
    let inside = (fqsv formula) in 
      inside \\ otherSVs
  Forall otherSVs formula -> 
    let inside = (fqsv formula) in
      inside \\ otherSVs
  GEq ups -> fqsvU ups 
  EqK ups -> fqsvU ups 
  AppCAbst lit otherSVs resultSVs -> otherSVs `union` resultSVs
  AppRecPost lit insouts -> insouts
  _ -> error ("fqsv: unexpected argument: " ++ show f)
  

fqsvU:: [Update] -> [QSizeVar]
fqsvU [] = []
fqsvU (up:ups) = 
  let rest=fqsvU ups in 
    case up of
      Const int -> rest
      Coef qsv int -> qsv:rest  -- << Diferent from sizeVarsFromUpdates

-------Selectors from Annotated Types-----
--generates Unprimed versions of SizeVars found in ty, same as unprimeThisTy
fsvTy:: AnnoType -> FS [QSizeVar]
fsvTy ty = 
  sizeVarsFromAnnTy ty >>= \svs ->
  return $ map (\s -> (s,Unprimed)) svs

--generates both Primed and Unprimed versions of SizeVars found in ty
fsvPUTy:: AnnoType -> FS [QSizeVar]
fsvPUTy ty = 
  sizeVarsFromAnnTy ty >>= \svs -> 
  return $ concatMap (\v -> (v,Unprimed):[(v,Primed)]) svs

--collects all size variables from an annotated type
sizeVarsFromAnnTy:: AnnoType -> FS [SizeVar]
sizeVarsFromAnnTy (TopType{}) = return []
sizeVarsFromAnnTy ty@ArrayType{} =
  getFlags >>= \flags -> 
  mapM sizeVarsFromAnnTy (indxTypes ty) >>= \ps ->
  let p = concat ps in
  let e = if isIndirectionIntArray flags then
            case elemType ty of
              PrimInt{anno=Just a} -> (ArrSizeVar a Min):(ArrSizeVar a Max):[]
              PrimInt{anno=Nothing} -> error $ "sizeVarsFromAnnTy: indirection array (Int element type) is not annotated\n " ++ showImpp (elemType ty)
              _ -> []
          else [] in
    return (p++e)
sizeVarsFromAnnTy ty@PrimBool{} = case anno ty of 
  Nothing -> error $ "sizeVarsFromAnnTy: sized type is not annotated\n " ++ showImpp ty
  Just a -> return [(SizeVar a)]
sizeVarsFromAnnTy ty@PrimInt{} = case anno ty of 
  Nothing -> error $ "sizeVarsFromAnnTy: sized type is not annotated\n " ++ showImpp ty
  Just a -> return [(SizeVar a)]
sizeVarsFromAnnTy ty@PrimFloat{} = return []
sizeVarsFromAnnTy ty@PrimVoid{} = return []

--changes all QSizeVars to Primed
--assumes that input list contains no Recursive or Primed QSizeVar
primeTheseQSizeVars:: [QSizeVar] -> [QSizeVar]
primeTheseQSizeVars = map (\q -> case q of 
  (sv,Unprimed) -> (sv,Primed)
  (sv,Primed) -> error $ "primeTheseQSizeVars: size variables from argument SHOULD NOT be primed: "++showImpp q
  )

--changes all QSizeVars to Recursive
--assumes that input list contains no Recursive or Primed QSizeVar
recTheseQSizeVars:: [QSizeVar] -> [QSizeVar]
recTheseQSizeVars = map (\q -> case q of 
  (sv,Unprimed) -> (sv,Recursive)
  (sv,Primed) -> error $ "recTheseQSizeVars: size variables from argument SHOULD NOT be primed: "++showImpp q
  )

--changes all QSizeVars to Unprimed
--assumes that input list contains no Recursive QSizeVar
--for use in the rhs of ctxImplication or ctxSimplify or composition
unprimeTheseQSizeVars:: [QSizeVar] -> [QSizeVar]
unprimeTheseQSizeVars qsv = nub $ map (\q -> case q of
  (sv,Unprimed) -> (sv,Unprimed)
  (sv,Primed) -> (sv,Unprimed)) qsv
