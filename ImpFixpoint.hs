module ImpFixpoint(fixpoint) where
import Fresh(FS,fresh,takeFresh,addOmegaStr,getFlags,putStrFS,getCPUTimeFS)
import ImpAST
import ImpConfig(useTrueFixpoint,useAnnotatedFixpoint,useSelectiveHull,widenEarly,pairwiseDuringFix)
import ImpFormula(inverseSubst,debugApply,noChange,fsvTy,Subst,fqsv,fqsvU,primeTheseQSizeVars,simplify,hull,subset,pairwiseCheck)
import ImpTypeCommon(setsForParamPassing)
import InSolver(impUnion,impCompose)
import MyPrelude(tr,concatMapM,showDiffTimes)
---------------
import List(union,(\\))
import Maybe(catMaybes)

-- fixpoint:: Method_declaration -> (Annotated_Postcondition, Annotated_Invariant) -> (CAbst_not_used) 
-- -> (Good_Postcondition,Good_Invariant)
fixpoint:: MethDecl -> CAbst -> FS (Formula,Formula)
fixpoint m cabst =
  getFlags >>= \flags ->
  let ((_,t,fname):args) = methParams m in
  setsForParamPassing (Meth m) >>= \(_,_,_,qsvByRef,_) ->
  let annPost = strong (methPost m) in
  let annInv = methInv m in
  if useTrueFixpoint then
    return (fTrue,fTrue)
  else
    addOmegaStr ("\nCAbst: " ++ show cabst) >>
    getCPUTimeFS >>= \time1 ->
  prepareCAbstBU cabst qsvByRef >>= \(preparedCAbstBU,rhoBackToPrimesBU) ->
    addOmegaStr ("PreparedRecCAbstBottomUp: " ++ show preparedCAbstBU) >>
  (if widenEarly flags then
    bottomUp3 preparedCAbstBU 
  else bottomUp preparedCAbstBU) >>= \infPost ->
  debugApply rhoBackToPrimesBU infPost >>= \infPost ->
    getCPUTimeFS >>= \time2 -> 
    addOmegaStr ("Post:=" ++ showSet (fqsv infPost,infPost) ++ "\n") >>
  prepareCAbstTD infPost cabst qsvByRef >>= \(preparedCAbstTD,rhoBackToPrimesTD) ->
    addOmegaStr ("PreparedRecCAbstTopDown: " ++ show preparedCAbstTD) >>
  (if widenEarly flags then
    topDown3 preparedCAbstTD rhoBackToPrimesTD
  else topDown preparedCAbstTD rhoBackToPrimesTD) >>= \infInv ->
  debugApply rhoBackToPrimesTD infInv >>= \infInv ->
    getCPUTimeFS >>= \time3 -> putStrFS ("Inferring " ++ methName m ++ "...fixpoint done in (" ++ showDiffTimes time2 time1 ++ ", " ++ showDiffTimes time3 time2 ++ ")") >> 
  let tyFromArgs = map (\(_,tyi,vi) -> tyi) (methParams m) in
  let annTys = tyFromInv fname in
  (if useAnnotatedFixpoint flags && (annPost /= FormulaBogus) 
    then
      postSubst tyFromArgs annTys >>= \subst ->
      debugApply subst annPost >>= \renamedAnnPost ->
      addOmegaStr("annPost:="++showSet (fqsv renamedAnnPost,renamedAnnPost)) >> return renamedAnnPost
    else return infPost) >>= \resultPost ->
  (if useAnnotatedFixpoint flags && (annInv /= FormulaBogus) 
    then
      invSubstFromInv tyFromArgs annTys >>= \subst ->
      debugApply subst annInv >>= \renamedAnnInv ->
      addOmegaStr("annInv:="++showSet (fqsv renamedAnnInv,renamedAnnInv)) >> return renamedAnnInv
    else return infInv) >>= \resultInv ->
  return (resultPost,resultInv)

-------Non-Magic-------------------
-------PostCondition Deriv---------

-- generate fresh vars for all primes inside CAbst -> NO MORE PRIMES
prepareCAbstBU:: CAbst -> [QSizeVar] -> FS (CAbst,Subst)
prepareCAbstBU (CAbst name qsvs formula) qsvByRef =
  allPrimedToFresh formula qsvByRef >>= \(nonPrimedFormula,rho) ->
  let preparedBU = CAbst name qsvs nonPrimedFormula in
--  case checkCAbst preparedBU of
--    Just str -> error $ "prepareCAbstBU internal error: " ++ str
--    Nothing -> 
      return (preparedBU,rho)

-- computes PostCondition from a "prepared" CAbst
bottomUp:: CAbst -> FS Formula
bottomUp cabst@(CAbst name qsvs formula) =  
  subrec cabst fFalse >>= \f1 ->
    addOmegaStr ("\tF1 simplifies to F1r") >>
  (if pairwiseDuringFix then pairwiseCheck f1 else simplify f1) >>= \f1r ->
  subrec cabst f1r >>= \f2 ->
    addOmegaStr ("\tF2 simplifies to F2r") >>
  (if pairwiseDuringFix then pairwiseCheck f2 else simplify f2) >>= \f2r -> 
  subrec cabst f2r >>= \f3 ->
    addOmegaStr ("\tF3 simplifies to F3r") >>
  (if pairwiseDuringFix then pairwiseCheck f3 else simplify f3) >>= \f3r ->
  subrec cabst f3r >>= \f4 ->
    addOmegaStr ("\tF4 simplifies to F4r") >>
  (if pairwiseDuringFix then pairwiseCheck f4 else simplify f4) >>= \f4r ->
  getFlags >>= \flags ->
  if useSelectiveHull flags then -- selective hulling
      addOmegaStr ("\tSelective hull for F3r") >>
    selectiveHull f3r f1r >>= \(f3NonRec,f3HRec) ->
      addOmegaStr ("Disjunction of nonRec cases from selHull:\n" ++ showSet (fqsv f3NonRec,f3NonRec)) >> 
      addOmegaStr ("Disjunction of Rec cases from selHull:\n" ++ showSet (fqsv f3HRec,f3HRec)) >>
      addOmegaStr ("\tSelective hull for F4r") >>
    selectiveHull f4r f1 >>= \(f4NonRec,f4HRec) ->
      addOmegaStr ("Disjunction of nonRec cases from selHull:\n" ++ showSet (fqsv f4NonRec,f4NonRec)) >> 
      addOmegaStr ("Disjunction of Rec cases from selHull:\n" ++ showSet (fqsv f4HRec,f4HRec)) >>
      addOmegaStr ("\tWiden Rec cases from F3 with respect to Rec cases from F4:") >>
    widen f3HRec f4HRec >>= \f3WRec ->
      addOmegaStr ("Widened Rec cases from F3: " ++ showSet (fqsv f3WRec,f3WRec)) >>
      addOmegaStr ("\tWiden NonRec cases from F3 with respect to NonRec cases from F4:") >>
    widen f3NonRec f4NonRec >>= \f3WNonRec ->
      addOmegaStr ("Widened NonRec cases from F3: " ++ showSet (fqsv f3WNonRec,f3WNonRec)) >>
--    let f3WNonRec = f3NonRec in
    let f3W = Or [f3WNonRec,f3WRec] in
    subrec cabst f3W >>= \f4' ->
      addOmegaStr ("\tObtained postcondition?") >>
    subset f4' f3W >>= \subok ->
    if subok then 
      return f3W
    else 
      iterBU cabst f1r f3WNonRec f4r f4HRec (length qsvs -3)
  else -- no selective hulling
    hull f3r >>= \f3H ->
    hull f4r >>= \f4H ->
    widen f3H f4H >>= \f3W ->
    subrec cabst f3W >>= \f4' ->
      addOmegaStr ("\tObtained postcondition?") >>
    subset f4' f3W >>= \subok ->
    if subok then 
      return f3W
    else 
      iterBUNonSel cabst f4r f4H (length qsvs -3)

--widening after 3 (instead of 4) iterations
bottomUp3:: CAbst -> FS Formula
bottomUp3 cabst@(CAbst name qsvs formula) =  
  subrec cabst fFalse >>= \f1 ->
    addOmegaStr ("\tF1 simplifies to F1r") >>
  (if pairwiseDuringFix then pairwiseCheck f1 else simplify f1) >>= \f1r ->
  subrec cabst f1r >>= \f2 ->
    addOmegaStr ("\tF2 simplifies to F2r") >>
  (if pairwiseDuringFix then pairwiseCheck f2 else simplify f2) >>= \f2r -> 
  subrec cabst f2r >>= \f3 ->
    addOmegaStr ("\tF3 simplifies to F3r") >>
  (if pairwiseDuringFix then pairwiseCheck f3 else simplify f3) >>= \f3r ->
  getFlags >>= \flags ->
  if useSelectiveHull flags then -- selective hulling
      addOmegaStr ("\tSelective hull for F2r") >>
    selectiveHull f2r f1r >>= \(f2NonRec,f2HRec) ->
      addOmegaStr ("Disjunction of nonRec cases from selHull:\n" ++ showSet (fqsv f2NonRec,f2NonRec)) >> 
      addOmegaStr ("Disjunction of Rec cases from selHull:\n" ++ showSet (fqsv f2HRec,f2HRec)) >>
      addOmegaStr ("\tSelective hull for F3r") >>
    selectiveHull f3r f1 >>= \(f3NonRec,f3HRec) ->
      addOmegaStr ("Disjunction of nonRec cases from selHull:\n" ++ showSet (fqsv f3NonRec,f3NonRec)) >> 
      addOmegaStr ("Disjunction of Rec cases from selHull:\n" ++ showSet (fqsv f3HRec,f3HRec)) >>
      addOmegaStr ("\tWiden Rec cases from F2 with respect to Rec cases from F3:") >>
    widen f2HRec f3HRec >>= \f2WRec ->
      addOmegaStr ("Widened Rec cases from F2: " ++ showSet (fqsv f2WRec,f2WRec)) >>
      addOmegaStr ("\tWiden NonRec cases from F2 with respect to NonRec cases from F3:") >>
    widen f2NonRec f3NonRec >>= \f2WNonRec ->
      addOmegaStr ("Widened NonRec cases from F2: " ++ showSet (fqsv f2WNonRec,f2WNonRec)) >>
    let f2W = Or [f2WNonRec,f2WRec] in
    subrec cabst f2W >>= \f3' ->
      addOmegaStr ("\tObtained postcondition?") >>
    subset f3' f2W >>= \subok ->
    if subok then 
      return f2W
    else 
      iterBU cabst f1r f2WNonRec f3r f3HRec (length qsvs -2)
  else -- no selective hulling
    hull f2r >>= \f2H ->
    hull f3r >>= \f3H ->
    widen f2H f3H >>= \f2W ->
    subrec cabst f2W >>= \f3' ->
      addOmegaStr ("\tObtained postcondition?") >>
    subset f3' f2W >>= \subok ->
    if subok then 
      return f2W
    else 
      iterBUNonSel cabst f3r f3H (length qsvs -2)

iterBU:: CAbst -> Formula -> Formula -> Formula -> Formula -> Int -> FS Formula
iterBU cabst f1r f4NonRec f4r f4HRec n =
  if n<= 0 then return fTrue
  else
    subrec cabst f4r >>= \f5 ->
      addOmegaStr ("\tFn simplifies to Fn") >>
    simplify f5 >>= \f5r ->
    selectiveHull f5r f1r >>= \(f5NonRec,f5HRec) ->
      addOmegaStr ("Disjunction of Rec cases from selHull:\n" ++ showSet (fqsv f5HRec,f5HRec)) >>
    widen f4HRec f5HRec >>= \f4WRec ->
      addOmegaStr ("Widened Rec cases: " ++ showSet (fqsv f4WRec,f4WRec)) >>
    widen f4NonRec f5NonRec >>= \f4WNonRec ->
      addOmegaStr ("Widened NonRec cases: " ++ showSet (fqsv f4WNonRec,f4WNonRec)) >>
--    let f4WNonRec = f4NonRec in
    let f4W = Or [f4WNonRec,f4WRec] in
    subrec cabst f4W >>= \f5' ->
      addOmegaStr ("\tObtained postcondition?") >>
    subset f5' f4W >>= \subok ->
    if subok then 
      return f4W
    else 
      iterBU cabst f1r f4WNonRec f5r f5HRec (n-1)
    
iterBUNonSel:: CAbst -> Formula -> Formula -> Int -> FS Formula
iterBUNonSel cabst f4r f4H n =
  if n<= 0 then return fTrue
  else
    subrec cabst f4r >>= \f5 ->
      addOmegaStr ("\tFn simplifies to Fn") >>
    simplify f5 >>= \f5r ->
    hull f5r >>= \f5H ->
    widen f4H f5H >>= \f4W ->
    subrec cabst f4W >>= \f5' ->
      addOmegaStr ("\tObtained postcondition?") >>
    subset f5' f4W >>= \subok ->
    if subok then 
      return f4W
    else 
      iterBUNonSel cabst f5r f5H (n-1)


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


---------------------------
subrec :: CAbst -> Formula -> FS Formula
subrec (CAbst formalName formalQsvs f1) f2 =
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
    (AppCAbst actualName actualArgs actualRes) -> 
      if not (formalName==actualName) then
        error "subrec: mutual recursion detected" 
      else
        takeFresh (length formalQsvs) >>= \freshies ->
        let freshQsvs = map (\fsh -> (SizeVar fsh,Unprimed)) freshies in
        let formalArgs = take (length actualArgs) freshQsvs in
        let formalRes = drop (length actualArgs) freshQsvs in
        if not (length formalRes == length actualRes) then
          error $ "subrec found different no of QSVs for CAbst:\n " ++ show f
        else
          let argsPairs = zip formalArgs actualArgs in
          let resPairs = zip formalRes actualRes in
          let newEqs = And $ map (\(f,a) -> EqK [Coef f 1,Coef a (-1)]) (argsPairs++resPairs) in
          let rho = zip formalQsvs freshQsvs in
          debugApply rho g >>= \rhoG ->
          let newG = And [rhoG,newEqs] in
            return (fExists freshQsvs newG)
    _ -> return f
       
selectiveHull:: Formula -> Formula -> FS (Formula,Formula)
selectiveHull f base = case f of
  Or fs -> 
    classify fs base >>= \(nonRec,rec) ->
    hull (Or rec) >>= \recH ->
    return (if (null nonRec) then fTrue else fOr nonRec,recH)
  f -> return (fTrue,f)
--  _ -> error $ "during selectiveHull: formula needs to be in disjunctive form\n " ++ show f
  where
  classify:: [Formula] -> Formula -> FS ([Formula],[Formula])
  classify [] base = return ([],[])
  classify (f:fs) base = 
--    subset f base >>= \subok ->
    subset base f >>= \subok ->
    classify fs base >>= \(restNonRec,restRec) ->
    if subok then 
      return (f:restNonRec,restRec) 
    else return (restNonRec,f:restRec)

widen:: Formula -> Formula -> FS Formula
widen f1 f2 = 
  let f1s = buildClauses f1 in
  mapM (subset f2) f1s >>= \suboks ->
  let f1s' = zip f1s suboks in
  let f1' = filter (\(f,ok) -> ok) f1s' in
  return $ fAnd (map fst f1')
 where 
  buildClauses:: Formula -> [Formula]
  buildClauses f = 
   case f of
     And fs -> concatMap buildClauses fs
     Or fs -> error $ "Or during widen: formula needs to be in conjunctive form\n " ++ show f
     Exists vars f -> error $ "Exists during widen: formula needs to be in conjunctive form\n " ++ show f
     Forall vars f -> error $ "Forall during widen: formula needs to be in conjunctive form\n " ++ show f
     Not f -> error $ "Not during widen: formula needs to be in conjunctive form\n " ++ show f
     GEq ups -> [f]
     EqK ups -> [f]

-------Invariant Deriv-----
-- 1. add postcondition computed by BU (currently only TRUE is used: addPostFromBU needs corrections
-- 2. generate fresh vars for all primes inside CAbst -> NO MORE PRIMES
-- 3. compute a disjunction of the contexts corresponding to recursive calls
-- 4. simplify the resulting CAbst (this simplification cannot be done before 2. and 3.
prepareCAbstTD:: Formula -> CAbst -> [QSizeVar] -> FS (CAbst,Subst)
prepareCAbstTD postFromBU cabst@(CAbst name qsvs formula) qsvByRef =
  addPostFromBU postFromBU name qsvs formula >>= \formulaWithPost ->
  allPrimedToFresh formulaWithPost qsvByRef >>= \(nonPrimedFormula,rho) ->
  let disjCtxRec = fOr $ (snd (getRecCtx (CAbst name qsvs nonPrimedFormula) nonPrimedFormula fTrue)) in
  simplify disjCtxRec >>= \tdFormula ->
  let preparedTD = CAbst name qsvs tdFormula in
--  case checkCAbst preparedTD of
--    Just str -> error $ "prepareCAbstTD internal error: " ++ str ++ show rho
--    Nothing -> 
      return (preparedTD,rho)

checkCAbst:: CAbst -> Maybe String
checkCAbst cabst@(CAbst name qsvs formula) = 
  let fQsvs = fqsv formula in
  let from = qsvs in
  let to = primeTheseQSizeVars from in  
  if length ((fQsvs \\ from) \\ to) /= 0 then 
    Just $ "free size variables not allowed: " ++ show ((fQsvs \\ from) \\ to) ++ "\n" ++ showSet (fqsv formula,formula)
  else 
    Nothing
      
-- computes Invariant from a "prepared" CAbst
topDown:: CAbst -> Subst -> FS Formula
topDown (CAbst name qsvs f) rho =
  let fQsvs = fqsv f in
  let from = qsvs in
  let to = primeTheseQSizeVars from in  
  let g = f in
--  pairwiseCheck g >>= \g ->
  hull g >>= \g1 ->
    addOmegaStr("\tG1:=" ++ showRelation (from,to,g1)) >>

  impCompose (from,to,g1) (from,to,g) >>= \g1Comp ->
  impUnion (from,to,g1) (from,to,g1Comp) >>= \g1Union ->
  hull g1Union >>= \g2 ->
    addOmegaStr("\tG2:=" ++ showRelation (from,to,g2)) >>

  impCompose (from,to,g2) (from,to,g) >>= \g2Comp ->
  impUnion (from,to,g2) (from,to,g2Comp) >>= \g2Union ->
  hull g2Union >>= \g3 ->
    addOmegaStr("\tG3:=" ++ showRelation (from,to,g3)) >>

  impCompose (from,to,g3) (from,to,g) >>= \g3Comp ->
  impUnion (from,to,g3) (from,to,g3Comp) >>= \g3Union ->
  hull g3Union >>= \g4 ->
    addOmegaStr("\tG4:=" ++ showRelation (from,to,g4)) >>

    addOmegaStr ("\tWiden G3 with respect to G4:") >>
  widen g3 g4 >>= \g3W ->
    addOmegaStr ("Widened G3: " ++ showSet (fqsv g3W,g3W)) >>

  impCompose (from,to,g3W) (from,to,g) >>= \g3WComp ->
  impUnion (from,to,g3W) (from,to,g3WComp) >>= \g3WUnion ->
  hull g3WUnion >>= \g4' ->
    addOmegaStr("\tG4':=" ++ showRelation (from,to,g4')) >>

    addOmegaStr ("\tObtained invariant?") >>
  subset g4' g3W >>= \subok ->
  if subok then
    addOmegaStr ("Inv:=" ++ showRelation (from,to,g3W)) >>
    return g3W
  else 
    iterTD (from,to,f) g4 (length qsvs -4)

-- widening after 3 (instead of 4) iterations
topDown3:: CAbst -> Subst -> FS Formula
topDown3 (CAbst name qsvs f) rho =
  let fQsvs = fqsv f in
  let from = qsvs in
  let to = primeTheseQSizeVars from in  
  let ref = fst (unzip rho) in
  let g = fExists ref f in
--  pairwiseCheck g >>= \g ->
  hull g >>= \g1 ->
    addOmegaStr("\tG1:=" ++ showRelation (from,to,g1)) >>

  impCompose (from,to,g1) (from,to,g) >>= \g1Comp ->
  impUnion (from,to,g1) (from,to,g1Comp) >>= \g1Union ->
  hull g1Union >>= \g2 ->
    addOmegaStr("\tG2:=" ++ showRelation (from,to,g2)) >>

  impCompose (from,to,g2) (from,to,g) >>= \g2Comp ->
  impUnion (from,to,g2) (from,to,g2Comp) >>= \g2Union ->
  hull g2Union >>= \g3 ->
    addOmegaStr("\tG3:=" ++ showRelation (from,to,g3)) >>

    addOmegaStr ("\tWiden G2 with respect to G3:") >>
  widen g2 g3 >>= \g2W ->
    addOmegaStr ("Widened G2: " ++ showSet (fqsv g2W,g2W)) >>

  impCompose (from,to,g2W) (from,to,g) >>= \g2WComp ->
  impUnion (from,to,g2W) (from,to,g2WComp) >>= \g2WUnion ->
  hull g2WUnion >>= \g3' ->
    addOmegaStr("\tG3':=" ++ showRelation (from,to,g3')) >>

    addOmegaStr ("\tObtained invariant?") >>
  subset g3' g2W >>= \subok ->
  if subok then
    addOmegaStr ("Inv:=" ++ showRelation (from,to,g2W)) >>
    return g2W
  else 
    iterTD (from,to,g) g3 (length qsvs -3)
    
iterTD:: Relation -> Formula -> Int -> FS Formula
iterTD (from,to,g) g4 n =
  if (n<= 0) then return fTrue
  else
    impCompose (from,to,g4) (from,to,g) >>= \g4Comp ->
    impUnion (from,to,g4) (from,to,g4Comp) >>= \g4Union ->
    hull g4Union >>= \g5 ->
      addOmegaStr("\tGn:=" ++ showRelation (from,to,g5)) >>
    widen g4 g5 >>= \g4W ->
    impCompose (from,to,g4W) (from,to,g) >>= \g4WComp ->
    impUnion (from,to,g4W) (from,to,g4WComp) >>= \g4WUnion ->
    hull g4WUnion >>= \g5' ->
      addOmegaStr("\tGn':=" ++ showRelation (from,to,g5')) >>
      addOmegaStr ("\tObtained invariant?") >>
    subset g5' g4W >>= \subok ->
    if subok then
      addOmegaStr ("Inv:=" ++ showRelation (from,to,g4W)) >>
      return g4W
    else 
      iterTD (from,to,g) g4 (n-1)

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

-- more precise TD, which uses two series of formulae (Gs and Hs), without hulling Gs
-- after a few composition Gs become huge...
topDownPrecise:: CAbst -> FS Formula
topDownPrecise (CAbst name qsvs f) =  
  let from = filter (\qsv -> snd qsv == Unprimed) (fqsv f) in
  let to = filter (\qsv -> snd qsv == Primed) (fqsv f) in
  let g = f in
  let g1 = f in
  hull g >>= \h1H ->
    addOmegaStr("\tH1:=" ++ showRelation (from,to,h1H)) >>
  impCompose (from,to,g1) (from,to,g) >>= \g2 ->
  impUnion (from,to,h1H) (from,to,g2) >>= \h2 ->
  hull h2 >>= \h2H ->
    addOmegaStr("\tH2:=" ++ showRelation (from,to,h2H)) >>
  impCompose (from,to,g2) (from,to,g) >>= \g3 ->
  impUnion (from,to,h2H) (from,to,g3) >>= \h3 ->
  hull h3 >>= \h3H ->
    addOmegaStr("\tH3:=" ++ showRelation (from,to,h3H)) >>
  impCompose (from,to,g3) (from,to,g) >>= \g4 ->
  impUnion (from,to,h3H) (from,to,g4) >>= \h4 ->
  hull h4 >>= \h4H ->
    addOmegaStr("\tH4:=" ++ showRelation (from,to,h4H)) >>
  widen h3H h4H >>= \h3W ->
  impUnion (from,to,h3W) (from,to,g4) >>= \h4' ->
  hull h4' >>= \h4H' ->
    addOmegaStr("\tH4W:=" ++ showRelation (from,to,h4H')) >>
    addOmegaStr ("\tObtained invariant?") >>
  subset h4H' h3W >>= \subok ->
  if subok then 
    return h4H' 
  else return fTrue

getRecCtx:: CAbst -> Formula -> Formula -> (Formula,[Formula])
-- CAbst(cAbstName qsvs _) -> formula from cAbst -> partial Ctx from Top -> (partial Ctx from Bot,contexts already completed)
getRecCtx cAbst@(CAbst formalName formalQsvs _) formula partialCtxFromTop = case formula of
  And [] -> (formula,[])
  Or [] -> (formula,[])
  And (f:fs) -> 
    let (partialCtxFromBot,completedCtx) = getRecCtx cAbst f partialCtxFromTop in
    let (And partialCtxFromBot2,completedCtx2) = getRecCtx cAbst (And fs) (And [partialCtxFromTop,partialCtxFromBot]) in
      (And (partialCtxFromBot:partialCtxFromBot2),completedCtx++completedCtx2)
  Or (f:fs) ->
    let (partialCtxFromBot,completedCtx) = getRecCtx cAbst f partialCtxFromTop in
    let (Or partialCtxFromBot2,completedCtx2) = getRecCtx cAbst (Or fs) partialCtxFromTop in
      (Or (partialCtxFromBot:partialCtxFromBot2),completedCtx++completedCtx2)
  Exists exQsv f -> 
    let (partialCtxFromBot,completedCtx) = getRecCtx cAbst f partialCtxFromTop in
      (Exists exQsv partialCtxFromBot,map (Exists exQsv) completedCtx)
  EqK ups -> (formula,[])
  GEq ups -> (formula,[])
  AppCAbst actualName actualArgs actualRes -> 
    let formalArgs = take (length actualArgs) formalQsvs in
    let formalRes = drop (length actualArgs) formalQsvs in
    if not (length formalRes == length actualRes) then
      error $ "during getRecCtx found different no of QSVs for CAbst:\n " ++ show formula
    else
    let argsPairs = zip (primeTheseQSizeVars formalArgs) actualArgs in
    let newEqs = map (\(f,a) -> EqK [Coef f 1,Coef a (-1)]) argsPairs in
    let replacementForAppCAbst = fAnd (partialCtxFromTop:newEqs) in
    if (actualName == formalName) then (fTrue,[replacementForAppCAbst])
    else error $ "during getRecCtx encountered mutual recursion\n"++show formula

addPostFromBU:: Formula -> Lit -> [QSizeVar] -> Formula -> FS Formula
-- POST -> name -> cAbst_formula: next to each AppCAbst is added rho.POST && noChange(y)
addPostFromBU postFromBU name formalQsvs formula = case formula of
  And fs -> 
    mapM (addPostFromBU postFromBU name formalQsvs) fs >>= \addFs ->
    return (And addFs)
  Or fs -> 
    mapM (addPostFromBU postFromBU name formalQsvs) fs >>= \addFs ->
    return (Or addFs)
  Exists exQsv f -> 
    addPostFromBU postFromBU name formalQsvs f >>= \addF ->
    return (Exists exQsv addF)
  EqK ups -> return formula
  GEq ups -> return formula
  AppCAbst actualName actualArgs actualRes -> 
    let formalArgs = take (length actualArgs) formalQsvs in
    let formalRes = drop (length actualArgs) formalQsvs in
    if not (length formalRes == length actualRes) then
      error $ "during getRecCtx found different no of QSVs for CAbst:\n " ++ show formula
    else
    let rho = zip formalArgs actualArgs ++ zip formalRes actualRes in
    let y = actualArgs ++ actualRes in
    debugApply rho postFromBU >>= \rhoPost ->
-- postcondition is not added properly in the following line :-((
--    return $ tr "##" (And [rhoPost,noChange y,formula])
    return $ formula


-------Invariant Deriv-----

-------Common BU-TD----------------
-- all quantified size variables that are primed are freshened up
-- comapred to shallow apply it DOES replace quantified variables
allPrimedToFresh:: Formula -> [QSizeVar] -> FS (Formula,Subst)
allPrimedToFresh formula qsvByRef =
  let primes = filter isPrimed (fqsv formula) in
  takeFresh (length primes) >>= \freshies ->
  let freshQsvs = map (\fsh -> (SizeVar fsh,Unprimed)) freshies in
  let subst = zip primes freshQsvs in
  let rhoBackToPrimes = filter (\(x,y) -> ((fst x),Unprimed) `elem` qsvByRef) subst in
  debugApply subst formula >>= \npFormula ->
  deepFreshPrimes npFormula >>= \nonPrimedFormula ->
  let primeOk = debugCheckNonPrimes nonPrimedFormula in
  if not primeOk then error $ "allPrimedToFresh does not work as expected\n" ++ show formula ++ "\n to\n " ++ show nonPrimedFormula
  else 
    return (nonPrimedFormula,inverseSubst rhoBackToPrimes)
 
deepFreshPrimes:: Formula -> FS Formula
deepFreshPrimes formula = case formula of
  And formulae -> mapM deepFreshPrimes formulae >>= \fs -> return (And fs)
  Or formulae -> mapM deepFreshPrimes formulae >>= \fs -> return (Or fs)
  Not formula -> deepFreshPrimes formula >>= \f -> return (Not f)
  Forall quantQsvs qFormula -> 
    deepFreshPrimes qFormula >>= \doneFormula ->
    let primesQ = filter isPrimed quantQsvs in
    takeFresh (length primesQ) >>= \freshies ->
    let freshQsvs = map (\fsh -> (SizeVar fsh,Unprimed)) freshies in
    let subst = zip primesQ freshQsvs in
    let unprimesQ = filter (\qsv -> not (isPrimed qsv)) quantQsvs in
    debugApply subst doneFormula >>= \sDoneFormula ->
    return $ fForall (unprimesQ++freshQsvs) sDoneFormula
  Exists quantQsvs qFormula -> 
    deepFreshPrimes qFormula >>= \doneFormula ->
    let primesQ = filter isPrimed quantQsvs in
    takeFresh (length primesQ) >>= \freshies ->
    let freshQsvs = map (\fsh -> (SizeVar fsh,Unprimed)) freshies in
    let subst = zip primesQ freshQsvs in
    let unprimesQ = filter (\qsv -> not (isPrimed qsv)) quantQsvs in
    debugApply subst doneFormula >>= \sDoneFormula ->
    return $ fExists (unprimesQ++freshQsvs) sDoneFormula
  GEq ups -> return formula
  EqK ups -> return formula
  AppCAbst lit qsvs resQsvs -> return formula

-- checks that a formula does not contain any Primed size variables
-- nonDebug version should have removed the call to checkNonPrimesQ
debugCheckNonPrimes:: Formula -> Bool
debugCheckNonPrimes formula = 
  let primes = filter isPrimed (checkNonPrimesQ formula) in
  if null primes then True else False
  where
  checkNonPrimesQ:: Formula -> [QSizeVar]
  checkNonPrimesQ form = case form of
    And formulae -> concatMap checkNonPrimesQ formulae
    Or formulae -> concatMap checkNonPrimesQ formulae
    Not formula -> checkNonPrimesQ formula
    Forall qsvs f -> filter isPrimed qsvs `union` checkNonPrimesQ f
    Exists qsvs f -> filter isPrimed qsvs `union` checkNonPrimesQ f
    GEq ups -> filter isPrimed (fqsvU ups)
    EqK ups -> filter isPrimed (fqsvU ups)
    AppCAbst lit qsvs resQsvs -> filter isPrimed (qsvs `union` resQsvs)

isPrimed:: QSizeVar -> Bool
isPrimed qsv = snd qsv == Primed

replaceOnceXSbyYSinVS:: Eq a => [(a,a)] -> [a] -> [a]
replaceOnceXSbyYSinVS [] vs = vs
replaceOnceXSbyYSinVS ((x,y):rest) vs = 
  let once = replaceOnceXbyYinVS x y vs in
    replaceOnceXSbyYSinVS rest once

replaceOnceXbyYinVS:: Eq a => a -> a -> [a] -> [a]
replaceOnceXbyYinVS x y [] = []
replaceOnceXbyYinVS x y (v:vs) = if x==v then (y:vs) else x:replaceOnceXbyYinVS x y vs

--unused: equalities are added separately for BU and TD
-- add equalities between primed formal args of a CAbst and actual args of AppCAbst inside the first CAbst
-- boolean flag which indicates if BU or TD (for TD, do not add equalities between result Qsvs)
addEqsCAbst:: Bool -> Lit -> [QSizeVar] -> Formula -> Formula
addEqsCAbst isBU formalName formalQsvs formula =
  case formula of
        And fs -> And $ map (addEqsCAbst isBU formalName formalQsvs) fs
        Or fs -> Or $ map (addEqsCAbst isBU formalName formalQsvs) fs
        Not f -> Not (addEqsCAbst isBU formalName formalQsvs f)
        Forall qsvs f -> Forall qsvs (addEqsCAbst isBU formalName formalQsvs f)
        Exists qsvs f -> Exists qsvs (addEqsCAbst isBU formalName formalQsvs f)
        GEq ups -> formula
        EqK ups -> formula
        AppCAbst actualName actualArgs actualRes -> 
          if (formalName==actualName) then 
            let formalArgs = take (length actualArgs) formalQsvs in
            let formalRes = drop (length actualArgs) formalQsvs in
            if not (length formalRes == length actualRes) then
              error $ "during addEqsCAbst found different no of QSVs for CAbst:\n " ++ show formula
            else
            let argsPairs = zip (primeTheseQSizeVars formalArgs) actualArgs in
            let resPairs = if isBU then zip (primeTheseQSizeVars formalRes) actualRes else [] in
            let newEqs = map (\(f,a) -> EqK [Coef f 1,Coef a (-1)]) (argsPairs++resPairs) in
              fAnd (newEqs++[formula])
          else error "addEqsCAbst: mutual recursion detected" 

-- unused
simplifyCAbst:: CAbst -> FS CAbst
simplifyCAbst cabst@(CAbst name qsvs f) = 
    replaceInCAbst f >>= \(replF,replPair) ->
    simplify replF >>= \simplF ->
    let doneF = replaceBackInCAbst replPair simplF in
    return $ CAbst name qsvs doneF
  where
  replaceInCAbst:: Formula -> FS (Formula,[(QSizeVar,Formula)])
  replaceInCAbst formula = case formula of
    And fs -> 
      mapM replaceInCAbst fs >>= \results -> let (replFs,replPair) = unzip results in
      return (And replFs,concat replPair)
    Or fs -> 
      mapM replaceInCAbst fs >>= \results -> let (replFs,replPair) = unzip results in
      return (Or replFs,concat replPair)
    Not f -> 
      replaceInCAbst f >>= \(replF,replPair) ->
      return (Not replF,replPair)
    Exists exQsvs f ->
      replaceInCAbst f >>= \(replF,replPair) ->
      return (Exists exQsvs replF,replPair)
    Forall forQsvs f ->
      replaceInCAbst f >>= \(replF,replPair) ->
      return (Forall forQsvs replF,replPair)
    GEq ups -> return (formula,[])
    EqK ups -> return (formula,[])
    AppCAbst lit qsvs resQsvs ->
      fresh >>= \fsh -> 
      let fshQsv = (SizeVar fsh, Unprimed) in
      let fshEq = EqK [Coef fshQsv 1,Const 0] in --add a marker
      return (fshEq,[(fshQsv,formula)])
    Union fs ->
      mapM replaceInCAbst fs >>= \results -> let (replFs,replPair) = unzip results in
      return (Union replFs,concat replPair)
  replaceBackInCAbst:: [(QSizeVar,Formula)] -> Formula -> Formula
  replaceBackInCAbst replPair formula = case formula of
    And fs ->
      And $ map (replaceBackInCAbst replPair) fs
    Or fs ->
      Or $ map (replaceBackInCAbst replPair) fs
    Not f -> Not $ (replaceBackInCAbst replPair) f
    Exists exQsvs f -> Exists exQsvs (replaceBackInCAbst replPair f)
    Forall forQsvs f -> Forall forQsvs (replaceBackInCAbst replPair f)
    GEq ups -> formula
    EqK ups -> -- any ups contains a marker? replace it back with AppCAbst
      let apps = catMaybes $ map (\(qsv,f) -> if qsv `elem` fqsvU ups then Just f else Nothing) replPair in
      case length apps of
        0 -> formula
        1 -> head apps
        2 -> error $ "during replaceBackInCAbst encountered two fresh variables in the same Equality"++show formula
    AppCAbst lit qsvs resQsvs -> error $ "during replaceBackInCAbst encountered AppCAbst:\n " ++ show formula 
    Union fs ->
      Union$ map (replaceBackInCAbst replPair) fs

-------Non-Magic-------------------
-------Magic-----------------------
-- given [f0,f1...] and [xS,xI..] generates {xS->f0,RECxS->f0',xI->f1,RECxI->f1',...}
invSubstFromInv:: [AnnoType] -> [AnnoType] -> FS Subst
invSubstFromInv tys recTys =
  concatMapM fsvTy tys >>= \qsvTys ->
  concatMapM fsvTy recTys >>= \qsvRecTys ->
  let unprimToUnprim = zip qsvRecTys qsvTys in
  let recToPrim = map (\((rec,Unprimed),(ty,Unprimed)) -> ((rec,Recursive),(ty,Primed))) (zip qsvRecTys qsvTys) in
    return (unprimToUnprim++recToPrim)

-- given [f89,f5,...] and [r,s,...] generates {r->f89,s->f5,PRMs->PRMf5,...}
postSubst:: [AnnoType] -> [AnnoType] -> FS Subst
postSubst tys recTys =
  concatMapM fsvTy tys >>= \tyQSV ->
  concatMapM fsvTy recTys >>= \recQSV ->
  let unprimToUnprim = (zip recQSV tyQSV) in
  let primToPrim = map (\((rec,Unprimed),(ty,Unprimed)) -> ((rec,Primed),(ty,Primed))) (zip recQSV tyQSV) in
    return (unprimToUnprim++primToPrim)

tyFromInv:: String -> [AnnoType]
tyFromInv fname = case fname of
--  "initArr" -> tyFromInvInitArr
--  "lookup" -> tyFromInvLookup
  "mvm" -> tyFromInvMvm
  "mergeF2" -> tyFromInvMergeF2
--  "merge2" -> tyFromInvMerge2
--  "msort" -> tyFromInvMsort
  "move" -> tyFromInvMove
--  "loopb" -> tyFromInvLoopb
  "loop_daxpy2_i" -> tyFromInvloop_daxpy2_i
  "loop_idamax1_i" -> tyFromInvloop_idamax1_i
  "sum" -> tyFromSum
  _ -> error ("missing type signature corresponding to invariant for recursive function " ++ fname)

tyFromInvInitArr = [
  PrimVoid{anno=Nothing},
  ArrayType{elemType=PrimFloat{anno=Nothing},indxTypes=[PrimInt{anno=Just "s"}]},
  PrimInt{anno=Just "i"},
  PrimInt{anno=Just "j"},
  PrimFloat{anno=Nothing}
  ]

tyFromInvLookup = [
  PrimInt{anno=Just "r"},
  ArrayType{elemType=PrimFloat{anno=Nothing},indxTypes=[PrimInt{anno=Just "s"}]},
  PrimFloat{anno=Nothing},
  PrimInt{anno=Just "i"},
  PrimInt{anno=Just "j"}
  ]

tyFromInvMvm = [
  PrimVoid{anno=Nothing},
  ArrayType{elemType=PrimInt{anno=Just "a"},indxTypes=[PrimInt{anno=Just "s1"}]},
  ArrayType{elemType=PrimInt{anno=Just "b"},indxTypes=[PrimInt{anno=Just "s2"}]},
  ArrayType{elemType=PrimFloat{anno=Nothing},indxTypes=[PrimInt{anno=Just "s3"}]},
  ArrayType{elemType=PrimFloat{anno=Nothing},indxTypes=[PrimInt{anno=Just "s4"}]},
  ArrayType{elemType=PrimFloat{anno=Nothing},indxTypes=[PrimInt{anno=Just "s5"}]},
  PrimInt{anno=Just "k"}
  ]

--void merge2 (int<ea>[int<a>] a, int<et>[int<t>] t, int<i> i, int<iu> iu, int<j> j, int<ju> ju, int<k> k)  
tyFromInvMerge2 = [
  ArrayType{elemType=PrimInt{anno=Just "ea"},indxTypes=[PrimInt{anno=Just "a"}]},
  ArrayType{elemType=PrimInt{anno=Just "et"},indxTypes=[PrimInt{anno=Just "t"}]},
  PrimInt{anno=Just "i"},
  PrimInt{anno=Just "iu"},
  PrimInt{anno=Just "j"},
  PrimInt{anno=Just "ju"},
  PrimInt{anno=Just "k"}
  ]

--void mergeF2 (float[int<a>] a, float[int<t>] t, int<i> i, int<iu> iu, int<j> j, int<ju> ju, int<k> k)
tyFromInvMergeF2 = [
  ArrayType{elemType=PrimFloat{anno=Nothing},indxTypes=[PrimInt{anno=Just "a"}]},
  ArrayType{elemType=PrimFloat{anno=Nothing},indxTypes=[PrimInt{anno=Just "t"}]},
  PrimInt{anno=Just "i"},
  PrimInt{anno=Just "iu"},
  PrimInt{anno=Just "j"},
  PrimInt{anno=Just "ju"},
  PrimInt{anno=Just "k"}
  ]

--void msort (int<ea>[int<a>] a, int<i> i, int<j> j)
tyFromInvMsort = [
  ArrayType{elemType=PrimInt{anno=Just "ea"},indxTypes=[PrimInt{anno=Just "a"}]},
  PrimInt{anno=Just "i"},
  PrimInt{anno=Just "j"}
  ]

--void move(Float[Int<s1>,Int<s2>]pole,Int<n> n,Int<sa> sa,Int<a> a
--	,Int<sb> sb,Int<b> b,Int<sc> sc,Int<c> c)
tyFromInvMove = [
  ArrayType{elemType=PrimFloat{anno=Nothing},indxTypes=[PrimInt{anno=Just "s1"},PrimInt{anno=Just "s2"}]},
  PrimInt{anno=Just "n"},
  PrimInt{anno=Just "sa"},
  PrimInt{anno=Just "a"},
  PrimInt{anno=Just "sb"},
  PrimInt{anno=Just "b"},
  PrimInt{anno=Just "sc"},
  PrimInt{anno=Just "c"}
  ]

--Void loopb (Int<b> b, Int<a> a, Int<n> n, Int<dual> dual, Float [Int<data>] data, 
--		Float w_real, Float w_imag)

tyFromInvLoopb = [
  PrimInt{anno=Just "b"},
  PrimInt{anno=Just "a"},
  PrimInt{anno=Just "n"},
  PrimInt{anno=Just "dual"},
  ArrayType{elemType=PrimFloat{anno=Nothing},indxTypes=[PrimInt{anno=Just "data"}]},
  PrimFloat{anno=Nothing},
  PrimFloat{anno=Nothing}
  ]

--void loop_daxpy2_i (int<i> i, int<n> n, float da, float [int<dx>] dx , int<i1> i1, 
--    float [int<dy>] dy, int<i2> i2)

tyFromInvloop_daxpy2_i = [
  PrimInt{anno=Just "i"},
  PrimInt{anno=Just "n"},
  PrimFloat{anno=Nothing},
  ArrayType{elemType=PrimFloat{anno=Nothing},indxTypes=[PrimInt{anno=Just "dx"}]},
  PrimInt{anno=Just "i1"},
  ArrayType{elemType=PrimFloat{anno=Nothing},indxTypes=[PrimInt{anno=Just "dy"}]},
  PrimInt{anno=Just "i2"}
  ]

--int<r> loop_idamax1_i(int<i> i, int<n> n, float [int<dx>] dx, int<i1> i1, float dmax, 
--    int<itemp> itemp)

tyFromInvloop_idamax1_i = [
  PrimInt{anno=Just "r"},
  PrimInt{anno=Just "i"},
  PrimInt{anno=Just "n"},
  ArrayType{elemType=PrimFloat{anno=Nothing},indxTypes=[PrimInt{anno=Just "dx"}]},
  PrimInt{anno=Just "i1"},
  PrimFloat{anno=Nothing},
  PrimInt{anno=Just "itemp"}
  ]

-- Float sum (Float[Int<a>] a, Int<i> i,Int<j> j)

tyFromSum = [
  PrimFloat{anno=Nothing},
  ArrayType{elemType=PrimFloat{anno=Nothing},indxTypes=[PrimInt{anno=Just "a"}]},
  PrimInt{anno=Just "i"},
  PrimInt{anno=Just "j"}
  ]



-------Magic-----------------------t                                                                                                                                                                                                                                                                                                                                                                                                  