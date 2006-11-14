module ImpTypeInfer(typeInferProg) where
import Fresh(runFS,FS(),initialState,fresh,takeFresh,addOmegaStr,writeOmegaStrs,getFlags,putStrFS,getCPUTimeFS)
import ImpAST
import ImpConfig(Flags,checkingAfterInference,noRecPreDerivation,separateFstFromRec,Prederivation(..),prederivation,Postcondition(..),postcondition,useFixpoint2k)
import ImpFormula
import ImpFixpoint(fixpoint)
import ImpFixpoint2k(fixpoint2k)
import ImpSugar(specialize,desugarInfer)
import ImpTypeChecker(typeCheckProg)
import ImpTypeCommon
import MyPrelude
-----------------
import Data.Graph(SCC(..),stronglyConnComp)
import List(union,unzip4,(\\),nub)
import Maybe(catMaybes,fromJust)
import Monad(when)

typeInferProg:: Prog -> FS Prog
typeInferProg prog = 
  getFlags >>= \flags ->  
  sTypeCheck prog >>= \noWhileProg ->
    putStrFS "Simple type-checking...done!" >>
  desugarInfer noWhileProg >>= \dsgProg@(Prog _ dsgPrims dsgMeths) -> 
-- Print C code without any bound-checks.
--  printProgCAll dsgProg >>
  let sccs = stronglyConnComp (methAdjacencies dsgMeths) in
    addOmegaStr "Starting inference..." >>
  getCPUTimeFS >>= \time1 -> typeInferSccs dsgProg sccs >>= \infProg -> getCPUTimeFS >>= \time2 ->
    putStrFS ("Array-bounds inference...done in " ++ showDiffTimes time2 time1) >> 
    addOmegaStr "Inference is finished..." >>
  printProgImpi infProg >>
  getCPUTimeFS >>= \time1 -> specialize infProg >>= \specializedProg -> getCPUTimeFS >>= \time2 ->
    putStrFS ("Specialization...done in " ++ showDiffTimes time2 time1) >> 
  printProgC specializedProg >>
  printProgImpt specializedProg >>
  if (checkingAfterInference flags) then 
    typeCheckProg specializedProg
  else return specializedProg


typeInferSccs:: Prog -> [SCC Node] -> FS Prog
typeInferSccs prog [] = return prog
typeInferSccs prog (scc:sccs) = 
  typeInferScc prog scc >>= \updProg ->
  typeInferSccs updProg sccs

type RecFlags = (Int,[Lit]) -- (whatPhase,nameOfRecFs)
-- whatPhase: 0 - noRecursion; 1 - collect cAbst; 2 - derive preconditions
-- whatPhase: 3 - collect cAbst for OK outcome; 4 - collect cAbst for ERR outcome

typeInferScc:: Prog -> SCC Node -> FS Prog
typeInferScc prog scc =
  case scc of
    AcyclicSCC mDecl ->
      putStrFS ("Inferring " ++ methName mDecl ++ "...") >> getCPUTimeFS >>= \time1 ->
--      typeInferMethDeclNonRec prog mDecl >>= \updProg -> 
      let updProg = prog in
      outInferMethDeclNonRec updProg (findMethod (methName mDecl) updProg) >>= \updProg2 ->
      getCPUTimeFS >>= \time2 ->
      putStrFS ("###Inferring " ++ methName mDecl ++ "...done in " ++ showDiffTimes time2 time1++"###") >> 
      return updProg2
    CyclicSCC mDecls ->
      if (length mDecls /= 1) then error "Mutual recursion is not implemented"
      else
        let mDecl = (head mDecls) in
        putStrFS ("###Inferring " ++ methName mDecl ++ "...###") >> getCPUTimeFS >>= \time1 ->
--        typeInferMethDeclRec prog mDecl >>= \updProg -> 
        let updProg = prog in
        outInferMethDeclRec updProg (findMethod (methName mDecl) updProg) >>= \updProg2 ->  
        getCPUTimeFS >>= \time2 ->
        putStrFS ("Inferring " ++ methName mDecl ++ "...done in " ++ showDiffTimes time2 time1) >> 
        return updProg2

typeInferMethDeclRec:: Prog -> MethDecl -> FS Prog
typeInferMethDeclRec prog m =
  getFlags >>= \flags ->  
  let ((passbyM,t,fname):args) = methParams m in
  addOmegaStr ("Inference for recursive " ++ fname) >>
  setsForParamPassing (Meth m) >>= \(inputs,outputs,res,qsvByRef,qsvByVal) ->
  let gamma = map (\(_,tyi,vi) -> (vi,tyi)) args in initialTransFromTyEnv gamma >>= \deltaInit ->
--phase 1
  typeInferExp prog (methBody m) fname inputs gamma (triple deltaInit) (1,[fname]) >>= \(tp,delta,_,_) ->
  rename tp t >>= \maybeRho ->
  case maybeRho of
    Nothing -> error $ "incompatible types\nfound "++showImpp tp++ "\nrequired: "++showImpp t++"\n "++showImpp m
    Just rho ->
      mapM (debugApply rho) delta >>= \deltap ->
      let delta1 = map (\ctx -> fExists (primeTheseQSizeVars qsvByVal) ctx) deltap in
--        putStrFS("##1"++ showSet(fqsv (strong delta1),(strong delta1))) >>
      let delta2 = case postcondition flags of { WeakPost -> weak delta1; StrongPost -> strong delta1} in
      let recCAbst = CAbst fname (inputs `union` res) delta2 in
      let recPost = RecPost fname (inputs `union` outputs) delta2 (inputs,outputs,qsvByVal) in
        (if useFixpoint2k then fixpoint2k m recPost else fixpoint m recCAbst) >>= \(fixedPost,fixedInv) ->
        (if useFixpoint2k then applyRecToPrimOnInvariant fixedInv else return fixedInv) >>= \inv ->
-- NOT TRUE: If assignments to pass-by-value parameters are disallowed in the method body: adding explicit noChange is not needed
        let noXPost = if useFixpoint2k 
                      then fixedPost
                      else fAnd [fExists (primeTheseQSizeVars qsvByVal) fixedPost,noChange qsvByVal] in
        let preFromPost = if prederivation flags == PostPD 
                          then [(["lPost"],fExists outputs fixedPost)]
                          else [] in
        let fixedM = m{methPost=(triple noXPost),methInv=inv,methPres=preFromPost} in
        let fixedProg = updateMethDecl prog fixedM in
          let deltaInit1 = fAnd (deltaInit:snd (unzip preFromPost)) in -- preFromPost is assumed to be true!
          typeInferExp fixedProg (methBody fixedM) fname inputs gamma (triple deltaInit1) (2,[fname]) >>= \(_,_,newPres,newUpsis) ->
          return (updateMethDecl fixedProg (fixedM{methPres=preFromPost++newPres,methUpsis=newUpsis}))

typeInferMethDeclNonRec:: Prog -> MethDecl -> FS Prog
typeInferMethDeclNonRec prog m =
  let ((passbyM,t,fname):args) = methParams m in
  addOmegaStr ("Inference for " ++ fname) >>
  setsForParamPassing (Meth m) >>= \(v,outputs,_,qsvByRef,qsvByVal) ->
  let gamma = map (\(_,tyi,vi) -> (vi,tyi)) args in initialTransFromTyEnv gamma >>= \deltaInit ->
  typeInferExp prog (methBody m) fname v gamma (triple deltaInit) (0,[]) >>= \(tp,delta,newPres,newUpsis) ->
  rename tp t >>= \maybeRho ->
  case maybeRho of
    Nothing -> error $ "incompatible types\nfound "++showImpp tp++ "\nrequired: "++showImpp t++"\n "++showImpp m
    Just rho -> 
          mapM (debugApply rho) delta >>= \deltap ->
          let delta1 = if useFixpoint2k 
                       then map (\ctx -> fExists (primeTheseQSizeVars qsvByVal) ctx) deltap
                       else map (\ctx -> fAnd [fExists (primeTheseQSizeVars qsvByVal) ctx,noChange qsvByVal]) deltap in
          mapM simplify delta1 >>= \delta2 -> 
          getFlags >>= \flags -> 
          if prederivation flags == PostPD then 
            let preFromPost = [(["lPost"],fExists outputs (strong delta2))] in
          	ctxImplication [] (snd (head preFromPost)) fFalse >>= \impliesF -> 
          	when impliesF (putStrFS ("## Definite error in function "++fname)) >> 
            let fixedM = m{methPost=delta2,methPres=preFromPost,methUpsis=[]} in
            let fixedProg = updateMethDecl prog fixedM in
            let deltaInit1 = fAnd (deltaInit:snd (unzip preFromPost)) in -- preFromPost is assumed to be true!
            typeInferExp fixedProg (methBody fixedM) fname v gamma (triple deltaInit1) (0,[]) >>= \(tp,delta,newPres,newUpsis) ->
            return (updateMethDecl fixedProg fixedM{methUpsis=newUpsis})
          else 
            return (updateMethDecl prog m{methPost=delta2,methPres=newPres,methUpsis=newUpsis})

-- Program -> Exp -> Method_name -> Variables_to_Quantify -> Type_Environment -> RecFlags
-- -> (Type_for_exp,Context,Preconditions,RuntimeExps)
typeInferExp:: Prog -> Exp -> Lit -> [QSizeVar] -> TypeEnv -> Formulae -> RecFlags 
  -> FS (AnnoType,Formulae,[LabelledFormula],[QLabel])
-------KTrue-----------------------
typeInferExp prog KTrue mn _ gamma delta recFlags = 
  fresh >>= \s ->
  let ty = PrimBool{anno=Just s} in
  let ctx = map (\context -> And [context,EqK[Coef (SizeVar s,Unprimed) (-1),Const 1]]) delta in
  return (ty,ctx,[],[])
-------KFalse----------------------
typeInferExp prog KFalse mn _ gamma delta recFlags = fresh >>= \s ->
  let ty = PrimBool{anno=Just s} in
  let ctx = map (\context -> And [context,EqK[Coef (SizeVar s,Unprimed) (-1),Const 0]]) delta in
  return (ty,ctx,[],[])
-------KInt------------------------
typeInferExp prog (KIntNum n) _ _ _ delta recFlags = fresh >>= \s ->
  let ty = PrimInt{anno=Just s} in
  let ctx = map (\context -> And [context,EqK[Coef (SizeVar s,Unprimed) (-1),Const n]]) delta in
  return (ty,ctx,[],[])
-------KFloat----------------------
typeInferExp prog (KFloatNum f) _ _ _ delta recFlags = 
  let ty = PrimFloat{anno=Nothing} in
  return (ty,delta,[],[])
-------KVoid-----------------------
typeInferExp prog (KVoid) _ _ _ delta recFlags = 
  let ty = PrimVoid{anno=Nothing} in
  return (ty,delta,[],[])
-------ExpBogus--------------------
typeInferExp prog ExpBogus mn _ _ _ recFlags =
  error $ "ExpBogus: variable declaration without initialization??\n in function: " ++ mn
-------Var-------------------------
typeInferExp prog (ExpVar lit) mn v gamma delta recFlags= 
  case lookupVar lit gamma of
    Nothing -> error $ "undefined variable " ++ lit ++ "\n in function " ++ mn
    Just ty -> freshTy ty >>= \typ ->
      equate (typ,ty) (Unprimed,Primed) >>= \(Just phi) ->
      let deltap = map (\context -> fAnd [context,phi]) delta in
      return (typ,deltap,[],[])
-------VarAssign-------------------
typeInferExp prog@(Prog _ _ meths) exp@(AssignVar lit e1) mn v gamma delta recFlags=
---- Disallow pass-by-val parameters to be assigned to:
--  let crtDef = findCallable mn (map (\m -> Meth m) meths) in
--  let params = case crtDef of
--        Just (Meth m) -> (methParams m)
--        Nothing -> error $ "assertion failed: crt-function definition not found\n " ++ showImppTabbed exp 1 in
--  if (fst3 (head params) == PassByVal) && any (\(p,ty,name) -> p==PassByVal && name==lit) (tail params) then 
--    error $ "assignment to pass-by-val parameter " ++ lit ++ "\n "++showImppTabbed exp 1++"\n in function " ++ mn
--  else
  case lookupVar lit gamma of
    Nothing -> error $ "undefined variable " ++ lit ++ "\n "++showImppTabbed exp 1++"\n in function " ++ mn
    Just ty ->
      typeInferExp prog e1 mn v gamma delta recFlags >>= \(ty1,delta1,phis,upsis) ->
      equate (ty,ty1) (Primed,Unprimed) >>= \subst ->
      case subst of
        Nothing -> error $ "incompatible types\nfound: " ++ showImpp ty1 ++ "\nrequired: " ++ showImpp ty ++ "\n "++ showImppTabbed exp 1
        Just phi ->
              fsvTy ty1 >>= \x ->
              impFromTy ty >>= \u ->
              mapM (\context -> composition u context phi) delta1 >>= \deltaA ->
              return (PrimVoid{anno=Nothing},map (fExists x) deltaA,phis,upsis) 

-------Seq-------------------------
typeInferExp prog (Seq e1 e2) mn v gamma delta recFlags = 
  typeInferExp prog e1 mn v gamma delta recFlags >>= \(ty1,delta1,phis1,upsis1) ->
    fsvTy ty1 >>= \x ->
      typeInferExp prog e2 mn v gamma (map (fExists x) delta1) recFlags >>= \(ty2,delta2,phis2,upsis2) ->
        let phis = phis1 `union` phis2 in
        let upsis = upsis1 `union` upsis2 in
        return $ (ty2,delta2,phis,upsis)

-------If--------------------------
typeInferExp prog exp@(If nonDet (ExpVar lit) exp1 exp2) mn v gamma delta recFlags = 
  let bty = case lookupVar lit gamma of
        Nothing -> error $ "undefined variable " ++ lit ++ "\n "++showImppTabbed exp 1++"\n in function " ++ mn
        Just ty@PrimBool{} -> ty
        Just ty -> error $ "incompatible types in conditional test\nfound: "++showImpp ty++"\nrequired: Bool\n "++showImppTabbed exp 1 in
    case bty of
      PrimBool{anno=Just b} ->
        let qb = (SizeVar b,Primed) in
-- deltaNoCond is used only if SelectivePD is enabled
        let deltab1 = map (\context -> fAnd [context,EqK [Coef qb (-1),Const 1]]) (take 3 delta) in
        let deltab0 = map (\context -> fAnd [context,EqK [Coef qb 1]]) (take 3 delta) in 
        getFlags >>= \flags -> 
        let (tripleDeltab1,tripleDeltab0) = 
              (if prederivation flags==SelectivePD then 
                --(cond delta) is used for more precise gisting in mkChk, but is expensive to compute (LU,linpack)
                ((take 2 deltab1)++[cond delta],(take 2 deltab0)++[cond delta])
               else (deltab1,deltab0)) in
        typeInferExp prog exp1 mn v gamma tripleDeltab1 recFlags >>= \(ty1,delta1,phis1,upsis1) ->
        typeInferExp prog exp2 mn v gamma tripleDeltab0 recFlags >>= \(ty2,delta2,phis2,upsis2) ->
            (case (ty1,ty2) of
              (_,TopType{}) -> error $ "assertion failed: TyTop during typeInference. error?\n "++showImppTabbed exp 1;
              (TopType{},_) -> error $ "assertion failed: TyTop during typeInference. error?\n "++showImppTabbed exp 1;
              (_,_) -> freshTy ty1) >>= \ty ->
              rename ty1 ty >>= \(Just rho1) -> --can't fail
              rename ty2 ty >>= \maybeRho ->
              case maybeRho of
                Nothing -> error $ "incompatible types in branches of conditional\nfound: "++showImpp ty1++"\nand: "++showImpp ty2++"\n "++showImppTabbed exp 1
                Just rho2 ->
                  mapM (debugApply rho1) delta1 >>= \rho1Delta1 ->
                  mapM (debugApply rho2) delta2 >>= \rho2Delta2 ->
                  let deltap = map (\(context1,context2) -> Or [context1,context2]) (zip rho1Delta1 rho2Delta2) in
                  let phis = phis1 `union` phis2 in
                  let upsis = upsis1 `union` upsis2 in
                    return (ty,deltap,phis,upsis)
      PrimBool{anno=Nothing} ->
        error $ "no annotation for the test value in conditional\n "++showImppTabbed exp 1
typeInferExp prog exp@(If nonDet _ exp1 exp2) mn v gamma delta recFlags = 
  error $ "test in conditional is not NQVar -- not implemented" ++ showImppTabbed exp 1

-------Empty Block-----------------
typeInferExp prog (ExpBlock [] exp1) mn v gamma delta recFlags = 
  typeInferExp prog exp1 mn v gamma delta recFlags 

-------Block1-DeclVar--------------
typeInferExp prog exp@(ExpBlock [VarDecl ty lit exp1] exp2) mn v gamma delta recFlags = 
  typeInferExp prog exp1 mn v gamma delta recFlags >>= \(ty1,delta1,phis1,upsis1) ->
  impFromTyEnv gamma >>= \u ->
  initialTransFromTy ty >>= \psi ->
--  equate (ty1,ty) (Unprimed,Unprimed) >>= \subst ->
  equate (ty1,ty) (Unprimed,Primed) >>= \subst ->
  case subst of
    Nothing -> error $ "incompatible types\nfound: " ++ showImpp ty1 ++ "\nrequired: " ++ showImpp ty ++ "\n "++ showImppTabbed exp 1
    Just equ ->
          let delta1p = map (\context -> fAnd[context,equ]) delta1 in
          let extGamma = extendTypeEnv gamma (lit,ty) in
          (fsvTy ty1) >>= \x ->
          let deltaP = map (\context -> And  [fExists x context,psi]) delta1p in
          typeInferExp prog exp2 mn v extGamma deltaP recFlags >>= \(ty2,delta2,phis2,upsis2) ->
          fsvTy ty >>= \svty -> impFromTy ty >>= \isvty ->
          let y = svty `union` primeTheseQSizeVars isvty in
          let phis = phis1 `union` phis2 in
          let upsis = upsis1 `union` upsis2 in
          return (ty2,map (fExists y) delta2,phis,upsis)

-------Block2-DeclArr--------------
typeInferExp prog exp@(ExpBlock [LblArrVarDecl lbl ty indxs lit exp1] exp2) mn v gamma delta recFlags = 
  case ty of
    ArrayType{elemType=elemTy,indxTypes=iTys} ->
      let lits = map(\i -> case i of 
            ExpVar lit -> lit
            _ -> error $ "incompatible expressions in array declaration\n found: " ++ showImppTabbed i 1 ++ "\nrequired: variable.\n") indxs in
      let tyvs = map (\l -> case lookupVar l gamma of
            Nothing -> error $ "undefined variable " ++ lit ++ " in function " ++ mn ++ "\n "++showImppTabbed exp 1
            Just ty@PrimInt{} -> ty
            Just ty -> error $ "incompatible types in array declaration - indexes must be integers\nfound: "++showImpp ty++"\nrequired: "++showTy PrimInt{anno=Nothing}++"\n "++showImppTabbed exp 1) lits in
      let sisPair = map (\tyv -> case tyv of {
                                PrimInt{anno=Just s} -> ((SizeVar s,Unprimed),(SizeVar s,Primed));
                                _ -> error $ "variable used for initialization of dimensions of array is not annotated: " ++ showImpp tyv ++ "\n "++showImppTabbed exp 1}
                    ) tyvs in
      let (sisU,sisP) = unzip sisPair in
      -- check same no of dimensions
      if not (length iTys == length tyvs) then 
        error $ "incompatible no. of dimensions in array declaration: " ++ concatSepByCommaImpp iTys ++ " and " ++ concatSepByCommaImpp tyvs ++ "\n "++showImppTabbed exp 1
      else
      -- check same type for each dimension: should be TyInt
      let sGT0sUnprimed = map (\si -> fGT[Coef si 1]) sisU in
      let sGT0sPrimed = map (\si -> fGT[Coef si 1]) sisP in
      mapM (\(n,s) -> equate (n,s) (Unprimed,Primed) >>= \eqF -> case eqF of {
                                  Nothing -> error $ "incompatible types\nfound: " ++ showImpp s ++ "\nrequired: " ++ showImpp n ++ "\n "++ showImppTabbed exp 1;
                                  Just equ -> return equ}
                      ) (zip iTys tyvs) >>= \nEqs -> -- no need for zipOrFail
      let checks = map (\(sGT0,cnt) -> (genLabelArr lbl cnt,sGT0)) (zip sGT0sUnprimed (enumFrom 1)) in -- no need for zipOrFail
      typeInferExp prog exp1 mn v gamma delta recFlags >>= \(tp,delta1,phis1,upsis1) ->
      -- check init value is of the same type as elemTy
      initArrFormula tp ty >>= \arrFormula ->
      case arrFormula of
        Nothing -> error $ "incompatible types in array declaration\nfound: " ++ showImpp tp ++ "\ndeclared array: " ++ showImpp ty ++ "\n " ++showImppTabbed exp 1
        Just indirPsi ->
          let fstComp = map (\context -> fAnd [indirPsi,context]) delta1 in
          let sndComp = fAnd (sGT0sPrimed++nEqs) in
          let gammap = extendTypeEnv gamma (lit,ty) in
          impFromTyEnv gammap >>= \u ->
          let delta1p = map (\context -> fAnd[context,sndComp]) fstComp in
            addOmegaStr ("=========\nDuring inference: declaration of array " ++ lit ++ "\n=========") >>
            initialTransFromTyEnv gamma >>= \invFromGamma ->
            mkChks v u delta1 invFromGamma checks >>= \(phisp,errs) ->
              fsvTy tp >>= \x ->
              fsvTy ty >>= \svty -> 
              impFromTy ty >>= \isvty ->
              let y = svty `union` primeTheseQSizeVars isvty in
                typeInferExp prog exp2 mn v gammap (map (fExists x) delta1p) recFlags >>= \(ty2,delta2,phis2,upsis2) ->
                let phis = phis1 `union` phisp `union` phis2 in
                let upsis = upsis1 `union` upsis2 `union` errs in
                  return $ (ty2,map (fExists y) delta2,phis,upsis)
    _ -> error $ "incompatible types\n found: " ++ showImpp ty ++ "\nrequired: array type in declaration of " ++ lit ++ "\n "++showImppTabbed exp 1

typeInferExp prog exp@(ExpBlock varDecls e1) mn v gamma delta recFlags = 
  error $ "MultiDecls in ExpBlock - program is not desugared? \n function: " ++ mn ++ "\n " ++ showImppTabbed exp 1
    
-------Call------------------------
typeInferExp (Prog _ prims meths) exp@(LblMethCall (Just lbl) fName argsIdent) 
  mn v gamma delta (wPhase,sccFs) =
  addOmegaStr ("=========\nDuring inference: call to " ++ fName ++ "\n=========") >>
  let getArgsTypes = \argIdent -> 
        case argIdent of
          ExpVar lit -> case lookupVar lit gamma of{Just ty -> ty;Nothing -> error $ "undefined variable " ++ lit ++ " in function " ++ mn ++ "\n "++showImppTabbed exp 1}
          arg -> error $ "found non-variable as arguments to primitive function\n:" ++ showImppTabbed arg 1++ "\n "++showImppTabbed exp 1
    in
    let argsTyps = map getArgsTypes argsIdent in 
    impFromTyEnv gamma >>= \u ->
    concatMapM impFromTy argsTyps >>= \wWithDup -> let w = nub wWithDup in
    qsvFromTyEnv gamma >>= \uRec -> -- to derive preRec, nonImp must be in U
    let callables = map (\p -> Prim p) prims ++ map (\m -> Meth m) meths in
    let calleeDef = findCallable fName callables in
    (case calleeDef of
          Nothing -> error $ "call to undefined function " ++ fName ++ "\n " ++ showImppTabbed exp 1
          Just (Meth m) -> 
            setsForParamPassing (fromJust calleeDef) >>= \(_,_,_,_,qsvByVal) ->
            let delta = if useFixpoint2k  --for fixpoint2k: add noX(qsvByVal) to method postcondition
                        then map (\ctx -> fAnd [ctx,noChange qsvByVal]) (methPost m)
                        else (methPost m) in
            return (fst3(unzip3(methParams m)),snd3(unzip3(methParams m)),delta,methPres m)
          Just (Prim p) -> 
            let strongPost = And ((primPost p):(map (\(lbl,f) -> f) (primPres p))) in
            let triplePost = [strongPost,primPost p,primPost p] in
            return (fst3(unzip3(primParams p)),snd3(unzip3(primParams p)),triplePost,primPres p)
    ) >>= \(formalPassBy,formalTyps,deltam,phim) ->
    freshTy (head formalTyps) >>= \typ ->
    let actualTyps = typ:argsTyps in
    if (length formalTyps /= length actualTyps) then
      error $ "call to function " ++ fName ++ " with incompatible argument types\n "++showImppTabbed exp 1
    else
    let zipped = zip formalTyps actualTyps in
    concatMapM(\(t,tp) -> rename t tp >>= \subst -> case subst of {
                      Just rho -> return rho;
                      Nothing -> error $ "incompatible types\nfound "++showImpp tp++ "\nrequired: "++showImpp t++"\n "++showImppTabbed exp 1;}
              ) zipped >>= \rho ->
    mapM (\(lbls,f) -> debugApply rho f >>= \rhoF -> return (lbl:lbls,rhoF)) phim >>= \rhoPhim ->
    let isRecCall = fName `elem` sccFs in 
    case wPhase of
      0 -> -- caller (current funtion) is a non-recursive function
-- Point? 
          mapM simplify delta >>= \delta ->
          initialTransFromTyEnv gamma >>= \invFromGamma ->
          mkChks v u delta invFromGamma rhoPhim >>= \(phis,upsis) ->
          mapM (debugApply rho) deltam >>= \rhoDeltam ->
          mapM (\(context1,context2) -> composition w context1 context2) (zip delta rhoDeltam) >>= \delta2 ->
          return (typ,delta2,phis,upsis)
      1 -> -- caller is recursive: gather recursive CAbst
          if isRecCall then 
            let zp = zip3 formalPassBy actualTyps (replicate (length actualTyps) undefined) in
            let methForSets = (case (fromJust calleeDef) of {Meth m -> m;_->error ""}){methParams=zp} in
            setsForParamPassing (Meth methForSets) >>= \(inputs,outputs,res,_,qsvByVal) ->
            let insouts = inputs `union` outputs in
-- NOT TRUE: If assignments to pass-by-value parameters are disallowed in the method body: adding explicit noChange is not needed
            let delta1 = if useFixpoint2k 
                         then (And [noChange qsvByVal,AppRecPost fName insouts])
                         else (And [noChange qsvByVal,AppCAbst fName inputs res]) in
            mapM (\context -> composition w context delta1) delta >>= \delta2 ->
            return $ (typ,delta2,[],[]) -- when wPhase is 1, pres and upsis are not collected
          else
            mapM (debugApply rho) deltam >>= \rhoDeltam ->
            mapM (\(context1,context2) -> composition w context1 context2) (zip delta rhoDeltam) >>= \delta2 ->
            return $ (typ,delta2,[],[]) -- when wPhase is 1, pres and upsis are not collected
      2 -> -- caller is recursive: after fixpoint
          let crtName = (head sccFs) in -- assumes sccFs is singleton: no mutual recursion!!
          let crtDef = findCallable crtName callables in
          let (crtArgs,crtInv) = case crtDef of
                Just (Meth m) -> (methParams m,methInv m)
                Nothing -> error $ "assertion failed: function not-found at recursive call\n " ++ showImppTabbed exp 1 in
          let realTys = map (\(_,tyi,vi) -> tyi) crtArgs in
          if isRecCall then 
               getFlags >>= \flags -> 
              (if (prederivation flags == PostPD) then --if self-Recursive call and PostPD - enable checking!!
                initialTransFromTyEnv gamma >>= \invFromGamma ->
                mkChksRec v u uRec realTys delta crtInv invFromGamma rhoPhim >>= \(phis,upsis) -> return upsis
              else --if self-Recursive call - disable checking!!
                return []) >>= \newUpsis ->
              mapM (debugApply rho) deltam >>= \rhoDeltam ->
              mapM (\(context1,context2) -> composition w context1 context2) (zip delta rhoDeltam) >>= \delta2 ->
              return $ (typ,delta2,[],newUpsis) 
          else --derive preFst and preRec
-- Point? 
              mapM simplify delta >>= \delta ->
              initialTransFromTyEnv gamma >>= \invFromGamma ->
              mkChksRec v u uRec realTys delta crtInv invFromGamma rhoPhim >>= \(phis,upsis) ->
              mapM (debugApply rho) deltam >>= \rhoDeltam ->
              mapM (\(context1,context2) -> composition w context1 context2) (zip delta rhoDeltam) >>= \deltap ->
              return $ (typ,deltap,phis,upsis)

typeInferExp prog exp@(ExpError) mn v gamma delta recFlags = 
  error $ "ExpError encountered during type inference?\n "++showImppTabbed exp 1
-------The Rest--------------------
typeInferExp prog e _ _ _ _ _ = error $ "typeInferExp not implemented for the following construct\n " ++ showImppTabbed e 1

applyRecToPrimOnInvariant:: Formula -> FS Formula
applyRecToPrimOnInvariant inv =
  let qsv = fqsv inv in
  let recs = filter (\q -> case q of {(s,Recursive) -> True;_ -> False} ) qsv in
  let prims = map (\q -> case q of {(s,Recursive) -> (s,Primed);_ -> error "assertion failed in applyRecToPrimOnInvariant"}) recs in
  debugApply (zip recs prims) inv

extract :: [LabelledFormula] -> String
extract rhoPhim =
  if length rhoPhim == 0 then ""
  else concatLabels (fst (head rhoPhim))

-------MkChk-----------------------
mkChks:: [QSizeVar] -> [QSizeVar] -> Formulae -> Formula -> [LabelledFormula] -> FS ([LabelledFormula],[QLabel])
mkChks v u delta typeInv lblChks =
  mapM (mkChk v u delta typeInv) lblChks >>= \mays ->
  let (maybePhis,maybeUpsis) = unzip mays in
    return $ (catMaybes maybePhis,catMaybes maybeUpsis)

mkChk:: [QSizeVar] -> [QSizeVar] -> Formulae -> Formula -> LabelledFormula -> FS (Maybe LabelledFormula,Maybe QLabel)
mkChk v u [deltaS,deltaW,deltaC] typeInv (lbl,phi) = 
  getFlags >>= \flags ->  
      if prederivation flags == PostPD then 
          addOmegaStr (concatLabels lbl) >>
          addOmegaStr ("Total redundant check?") >> ctxImplication u deltaS phi >>= \impliesT ->
          if impliesT then 
            return (Nothing,Nothing)
          else return (Nothing,Just lbl)
      else
  addOmegaStr (concatLabels lbl) >>
  addOmegaStr ("Total redundant check?") >> ctxImplication u deltaS phi >>= \impliesT ->
  if impliesT then return (Nothing,Nothing)
  else 
    mapM hull [deltaS,deltaW,deltaC] >>= \[deltaSH,deltaWH,deltaCH] ->
    let toGistWith = case prederivation flags of { WeakPD -> typeInv; StrongPD -> deltaSH; SelectivePD -> deltaCH} in
    let ctx = case postcondition flags of {WeakPost -> deltaWH; StrongPost -> deltaSH} in
    addOmegaStr ("gist PHI given CTX ") >> ctxSimplify v u ctx phi toGistWith >>= \simple ->
  	addOmegaStr ("gisted PHI subset False?") >> ctxImplication [] simple fFalse >>= \impliesF ->
    if impliesF then return (Nothing,Just lbl)
    else addOmegaStr ("propagate gisted PHI") >> return (Just (lbl,simple),Nothing)

-------MkChkRec--------------------
mkChksRec:: [QSizeVar] -> [QSizeVar] -> [QSizeVar] -> [AnnoType] -> Formulae -> Formula -> Formula -> [LabelledFormula] -> FS ([LabelledFormula],[QLabel])
mkChksRec v u uRec typs delta inv typeInv lblChks =
  mapM (mkChkRec v u uRec typs delta inv typeInv) lblChks >>= \mays ->
  let (maybePhis,maybeUpsis) = unzip mays in
    return $ (catMaybes maybePhis,catMaybes maybeUpsis)

mkChkRec:: [QSizeVar] -> [QSizeVar] -> [QSizeVar] -> [AnnoType] -> Formulae -> Formula -> Formula -> LabelledFormula -> FS (Maybe LabelledFormula,Maybe QLabel)
mkChkRec v u uRec typs [deltaS,deltaW,deltaC] inv typeInv (lbl,phi) = 
  getFlags >>= \flags ->  
      if prederivation flags == PostPD then -- prederivation using necessary preconditions
          addOmegaStr (concatLabels lbl) >>
          nonImpLinkedToPrim typs >>= \nonImpToPrim ->
          let ctxRec = fExists v (fAnd [deltaS,nonImpToPrim]) in
          addOmegaStr ("Total redundant check?") >> ctxImplication uRec ctxRec phi >>= \impliesT ->
          if impliesT then 
            return (Nothing,Nothing)
          else return (Nothing,Just lbl)
      else
  addOmegaStr (concatLabels lbl) >>
  nonImpLinkedToPrim typs >>= \nonImpToPrim ->
  let ctxRec = fExists v (fAnd [deltaS,nonImpToPrim]) in
  addOmegaStr ("Total redundant check?") >> ctxImplication uRec ctxRec phi >>= \impliesT ->
  if impliesT then return (Nothing,Nothing)
  else
    mapM hull [deltaS,deltaW,deltaC] >>= \[deltaSH,deltaWH,deltaCH] ->
    let ctxRecS = fAnd [inv,fExists v (fAnd [deltaSH,nonImpToPrim])] in
    let ctxRecW = fAnd [inv,fExists v (fAnd [deltaWH,nonImpToPrim])] in
    let ctxRecC = fAnd [inv,fExists v (fAnd [deltaCH,nonImpToPrim])] in
    mapM simplify [ctxRecS,ctxRecW,ctxRecC] >>= \[ctxRecS,ctxRecW,ctxRecC] ->
    addOmegaStr ("pR_cR = gist PHI_REC given CTX_REC") >> 
    let toGistWith = case prederivation flags of { WeakPD -> typeInv; StrongPD -> ctxRecS; SelectivePD -> ctxRecC} in
    let ctxRec = case postcondition flags of { WeakPost -> ctxRecW; StrongPost -> ctxRecS} in
    ctxSimplify v uRec ctxRec phi toGistWith >>= \simpleRecWithRec ->
    addOmegaStr ("test the precondition: pR_cR && ctxFst => chk") >> 
    ctxImplication u (And [simpleRecWithRec,deltaSH]) phi >>= \phiUseful ->
    if phiUseful then
      let simple = simpleRecWithRec in
    	addOmegaStr ("pR_cR subset False?") >> ctxImplication [] simple fFalse >>= \impliesF ->
      if impliesF then return (Nothing,Just lbl)
      else addOmegaStr ("propagate pR_cR") >> return (Just (lbl,simple),Nothing)
    else
      if separateFstFromRec flags then
        addOmegaStr ("pF_cF = gist PHI_FST given CTX_FST ") >> 
        let toGistWith = case prederivation flags of { WeakPD -> typeInv; StrongPD -> deltaSH; SelectivePD -> deltaCH} in
        let delta = case postcondition flags of { WeakPost -> deltaWH; StrongPost -> deltaSH } in
        ctxSimplify v u delta phi toGistWith >>= \simpleFstWithFst ->
        addOmegaStr ("test the precondition: (pF_cF && pR_cR) && ctxFst => chk") >> 
        ctxImplication u (And [simpleFstWithFst,simpleRecWithRec,deltaSH]) phi >>= \phiUseful ->
        if phiUseful then --even if phiUseful is True, specialization may be needed to type check the recursive function
          let simple = fAnd [simpleFstWithFst,simpleRecWithRec] in
        	addOmegaStr ("(pF_cF && pR_cR) subset False?") >> ctxImplication [] simple fFalse >>= \impliesF ->
          if impliesF then return (Nothing,Just lbl)
          else addOmegaStr ("propagate (pF_cF && pR_cR)") >> return (Just (lbl,simple),Nothing)
        else
          addOmegaStr ("derived precondition does not type-check; so I propagate false")>> 
          return (Nothing, Just lbl)
      else
        addOmegaStr ("pF_tI = gist PHI_FST given TYPE_INV ") >> 
        let toGistWith = typeInv in
        let delta = case postcondition flags of { WeakPost -> deltaWH; StrongPost -> deltaSH } in
        ctxSimplify v u delta phi toGistWith >>= \simpleFstWithSta ->
        addOmegaStr ("test the precondition: (pF_tI && pR_cR) && ctxFst => chk") >> 
        ctxImplication u (And [simpleFstWithSta,simpleRecWithRec,deltaSH]) phi >>= \phiUseful ->
        if phiUseful then
          let simple = fAnd [simpleFstWithSta,simpleRecWithRec] in
        	addOmegaStr ("(pF_tI && pR_cR) subset False?") >> ctxImplication [] simple fFalse >>= \impliesF ->
          if impliesF then return (Nothing,Just lbl)
          else
              addOmegaStr ("propagate (pF_tI && pR_cR)") >> return (Just (lbl,simple),Nothing)
        else
          addOmegaStr ("derived precondition does not type-check; so I propagate false")>> 
          return (Nothing, Just lbl)

-------Meth SCC--------------------
type Key=Int
type Node=MethDecl

methAdjacencies:: [Node] -> [(Node, Key, [Key])]
methAdjacencies meths  = 
  let sccMeths = zip meths (enumFrom 0) in
    zip3 meths (enumFrom 0) (map (callees sccMeths) sccMeths)

callees:: [(MethDecl,Key)] -> (MethDecl,Key) -> [Key]
callees kmeths (m,k) =
  catMaybes $ map (getKeyForMeth kmeths) (getCalleesFromExp (methBody m))

getCalleesFromExp:: Exp -> [Lit]
getCalleesFromExp exp = case exp of
  LblMethCall lbl id exps -> id : (concatMap getCalleesFromExp exps)
  AssignVar id exp -> getCalleesFromExp exp
  If nonDet test exp1 exp2 -> concatMap getCalleesFromExp [test,exp1,exp2]
  Seq exp1 exp2 -> concatMap getCalleesFromExp [exp1,exp2]
  ExpBlock varDecls exp -> (concatMap getCalleesFromDecl varDecls) ++ getCalleesFromExp exp
  _ -> []

getCalleesFromDecl:: VarDecl -> [Lit]
getCalleesFromDecl varDecl = case varDecl of
  VarDecl ty lit exp -> getCalleesFromExp exp
  LblArrVarDecl lbl ty indxs lit exp -> getCalleesFromExp exp

getKeyForMeth:: [(MethDecl,Key)] -> Lit -> Maybe Key
getKeyForMeth kmeths lit = 
  let keys = catMaybes $ map (\(m,k) -> if getNameForMethDecl m == lit then Just k else Nothing) kmeths in
  case length keys of
    0 -> Nothing
    1 -> Just (head keys)
    _ -> error $ "More than one function defined with name: " ++ lit 
    
getNameForMethDecl:: MethDecl -> Lit
getNameForMethDecl m =
  let ((_,_,fname):_) = methParams m in fname

-- for debug: textual represetntation of SCCs
printSCCs:: [SCC Node] -> String
printSCCs [] = ""
printSCCs (n:ns) = (case n of
    AcyclicSCC v -> getNameForMethDecl v
    CyclicSCC vs -> "CYCLE " ++ concatMap getNameForMethDecl vs ++ " CYCLE"
  )
  ++"##"++printSCCs ns

------------------------
----OUTCOMES------------
------------------------
outAnd::Outcomes -> Formula -> Outcomes
outAnd [OK f1,ERR f2] f = [OK (And [f1,f]), ERR f2] 
outoutAnd::Outcomes -> Outcomes -> Outcomes
outoutAnd [OK f1,ERR f2] [OK fa,ERR fb] = [OK (And [f1,fa]),ERR (Or [f2,And [f1,fb]])]
outOr:: Outcomes -> Outcomes -> Outcomes
outOr [OK f1,ERR f2] [OK fa,ERR fb] = [OK (Or [f1,fa]),ERR (Or [f2,fb])]
outExists:: [QSizeVar] -> Outcomes -> Outcomes
outExists x [OK f1,ERR f2]  = [OK (fExists x f1), ERR (fExists x f2)]
outcomposition:: [QSizeVar] -> Outcomes -> Formula -> FS Outcomes
outcomposition u [OK f1,ERR f2] f = composition u f1 f >>= (\compF -> return [OK compF,ERR f2])
outdebugApply:: Subst -> Outcomes -> FS Outcomes
outdebugApply rho [OK f1,ERR f2] = debugApply rho f1 >>= \rhof1 -> debugApply rho f2 >>= \rhof2 -> 
  return [OK rhof1, ERR rhof2]
outsimplify:: Outcomes -> FS Outcomes
outsimplify [OK f1,ERR f2] = simplify f1 >>= \sf1 -> simplify f2 >>= \sf2 -> return [OK sf1,ERR sf2]
outoutcomposition:: [QSizeVar] -> Outcomes -> Outcomes -> FS Outcomes
outoutcomposition u [OK f1,ERR f2] [OK fa,ERR fb] = 
  composition u f1 fa >>= \f1a -> composition u f1 fb >>= \f1b ->
  return [OK f1a,ERR (Or [f2,f1b])]
outNonDet:: [QSizeVar] -> Outcomes -> Outcomes -> FS Outcomes
outNonDet ress [OK f1, ERR f3] [OK f2, ERR f4] =
  takeFresh (length ress) >>= \freshies1 ->
  let freshQsvs1 = map (\fsh -> (SizeVar fsh,Unprimed)) freshies1 in
  let subst1 = zip ress freshQsvs1 in
  debugApply subst1 f1 >>= \rhof1 ->
  takeFresh (length ress) >>= \freshies2 ->
  let freshQsvs2 = map (\fsh -> (SizeVar fsh,Unprimed)) freshies2 in
  let subst2 = zip ress freshQsvs2 in
  debugApply subst2 f2 >>= \rhof2 ->
  let outOK = fAnd [fExists freshQsvs1 rhof1,fExists freshQsvs2 rhof2,fOr[f1,f2]] in
  let outERR = fOr [f3,f4] in
  return [OK outOK, ERR outERR]

outInferMethDeclRec:: Prog -> MethDecl -> FS Prog
outInferMethDeclRec prog m =
  let ((passbyM,t,fname):args) = methParams m in
  setsForParamPassing (Meth m) >>= \(inputs,outputs,res,qsvByRef,qsvByVal) ->
  let gamma = map (\(_,tyi,vi) -> (vi,tyi)) args in initialTransFromTyEnv gamma >>= \deltaInit ->
  outInferExp prog (methBody m) fname inputs gamma [OK deltaInit,ERR fFalse] (3,[fname]) >>= \(tp,out,_) ->
  rename tp t >>= \(Just rho) -> 
  outdebugApply rho out >>= \outp -> 
  let out1 = outExists (primeTheseQSizeVars qsvByVal) outp in
      invFromTyEnv gamma >>= \typeInv ->
      let recPostOK = RecPost fname (inputs `union` outputs) (getOKOutcome out1) (inputs,outputs,qsvByVal) in
      putStrFS("###Fixpoint for OK outcome:###") >>
      fixpoint2k m recPostOK  >>= \(fixedPostOK,fixedInvOK) ->
      gistCtxGivenInv fixedPostOK typeInv >>= \gistedOK ->
      let fixOKProg = updateMethDecl prog m{methOut=[OK gistedOK,ERR FormulaBogus]} in
-----------------Alternative: without TransInv (fixpoint for each ERR)
--      outInferExp fixOKProg (methBody m) fname inputs gamma [OK deltaInit,ERR fFalse] (4,[fname]) >>= \(tp,out,errF) ->
--      outdebugApply rho out >>= \outp -> 
--      let out1 = outExists (primeTheseQSizeVars qsvByVal) outp in
--        mapM (\(lbl,f) -> case f of 
--                          EqK [Const 0,Const 1] -> return (lbl,f)
--                          _ ->
--                            replaceLblWithFormula (lbl,f) (getERROutcome out1) >>= \replF ->
--                            replaceAllWithFalse replF >>= \replAllF ->
--                            let recPostERR= RecPost fname (inputs `union` outputs) replAllF (inputs,outputs,qsvByVal) in
--                            putStrFS("###Fixpoint for ERR outcome:###") >>
--                            fixpoint2k m recPostERR >>= \(fixedPostERR,_) ->
--                            gistCtxGivenInv fixedPostERR typeInv >>= \gf ->
--                            putStrFS("ERR"++concat lbl++":="++showSet(fqsv gf,gf)) >>
--                            return (lbl,gf)) errF >>= \newMethErrs ->
--        gistCtxGivenInv (fOr (map (\(lbl,f) -> f) newMethErrs)) typeInv >>= \gistedERR ->
--        let gistedOut = [OK gistedOK,ERR gistedERR] in
-------------------Alternative: using TransInv
          outInferExp fixOKProg (methBody m) fname inputs gamma [OK deltaInit,ERR fFalse] (5,[fname]) >>= \(tp,out,errs) ->
          outdebugApply rho out >>= \outp -> 
          let out1 = outExists (primeTheseQSizeVars qsvByVal) outp in
          impFromTyEnv gamma >>= \u ->
          nonimpFromTyEnv gamma >>= \nonimp -> 
          applyRecToPrimOnInvariant fixedInvOK >>= \primInv ->
          let inv = fExists (primeTheseQSizeVars nonimp) primInv in
          composition u deltaInit inv >>= \deltaTransInv ->

---- each ERR separately
--          mapM (\(lbl,f) -> case f of 
--                            EqK [Const 0,Const 1] -> return (lbl,f)
--                            _ ->
--                              replaceLblWithFormula (lbl,f) (getERROutcome out1) >>= \replF ->
--                              replaceAllWithFalse replF >>= \fstf ->
--                              --gistCtxGivenInv fstf typeInv >>= \gfstf ->
--                              simplify fstf >>= \gfstf ->
--                              putStrFS("fstERR"++concat lbl++":="++showSet(fqsv gfstf,gfstf)) >>
--                              composition u deltaTransInv gfstf >>= \recf ->                              
--                              --gistCtxGivenInv recf typeInv >>= \grecf ->
--                              simplify recf >>= \grecf ->
--                              putStrFS("recERR"++concat lbl++":="++showSet(fqsv grecf,grecf)) >>
--                              return (lbl,Or [gfstf,grecf])) errs >>= \newMethErrs ->
--          gistCtxGivenInv (fOr (map (\(lbl,f) -> f) newMethErrs)) typeInv >>= \gistedERR ->
-- all ERRs at once
          replaceAllWithFormula errs (getERROutcome out1) >>= \replF ->
          simplify replF >>= \fstf ->
          putStrFS("fstERR:="++showSet(fqsv fstf,fstf)) >>
          composition u deltaTransInv fstf >>= \recf ->
          simplify recf >>= \grecf ->
          putStrFS("recERR:="++showSet(fqsv grecf,grecf)) >>
          let newMethErrs = [(["ERR"],Or [fstf,grecf])] in
          let gistedERR = Or [fstf,grecf] in
---COMMON: each or all ERRs
          let gistedOut = [OK gistedOK,ERR gistedERR] in
------prederivation
--                simplify (And [fExists outputs (getOKOutcome gistedOut),fNot (getERROutcome gistedOut)]) >>= \pre1 ->
--                simplify (And[getERROutcome gistedOut,fNot(fExists outputs (getOKOutcome  gistedOut))]) >>= \pre2 ->
--                simplify (And[getERROutcome gistedOut,fExists outputs (getOKOutcome  gistedOut)]) >>= \pre3 ->
--                let lpre1 = (["NEVER_BUG"],pre1) in
--                let lpre2 = (["MUST_BUG"],pre2) in
--                let lpre3 = (["MAY_BUG"],pre3) in
--                return (updateMethDecl prog m{methOut=gistedOut,methErrs=newMethErrs,methOutBugs=[lpre1,lpre2,lpre3]})
                return (updateMethDecl prog m{methOut=gistedOut,methErrs=newMethErrs})

outInferMethDeclNonRec:: Prog -> MethDecl -> FS Prog
outInferMethDeclNonRec prog m =
  let ((passbyM,t,fname):args) = methParams m in
  setsForParamPassing (Meth m) >>= \(v,outputs,_,qsvByRef,qsvByVal) ->
  let gamma = map (\(_,tyi,vi) -> (vi,tyi)) args in initialTransFromTyEnv gamma >>= \deltaInit ->
  outInferExp prog (methBody m) fname v gamma [OK deltaInit, ERR fFalse] (0,[]) >>= \(tp,out,errF) ->
  rename tp t >>= \(Just rho) ->
  outdebugApply rho out >>= \outp ->
  let out1 = outExists (primeTheseQSizeVars qsvByVal) outp in
          invFromTyEnv gamma >>= \typeInv ->
          gistCtxGivenInv (getOKOutcome out1) typeInv >>= \gistedOK ->
-- each ERR separately
--          mapM (\(lbl,f) -> case f of 
--                            EqK [Const 0,Const 1] -> return (lbl,f)
--                            _ ->
--                              replaceLblWithFormula (lbl,f) (getERROutcome out1) >>= \replF ->
--                              replaceAllWithFalse replF >>= \replAllF ->
--                              gistCtxGivenInv replAllF typeInv >>= \f ->
--                              --simplify replAllF >>= \f ->
--                              putStrFS("ERR"++concat lbl++":="++showSet(fqsv f,f)) >>
--                              return (lbl,f)) errF >>= \newMethErrs ->
--          gistCtxGivenInv (fOr (map (\(lbl,f) -> f) newMethErrs)) typeInv >>= \gistedERR ->
-- all ERRs at once
          replaceAllWithFormula errF (getERROutcome out1) >>= \replF ->
          simplify replF >>= \f ->
          putStrFS("ERR:="++showSet(fqsv f,f)) >>
          let newMethErrs = [(["ERR"],f)] in
          let gistedERR = f in
---COMMON: each or all ERRs
          let gistedOut = [OK gistedOK,ERR gistedERR] in
------prederivation
          if (methName m=="main") then
            simplify (And [fExists outputs (getOKOutcome gistedOut),fNot (getERROutcome gistedOut)]) >>= \pre1 ->
            simplify (And[getERROutcome gistedOut,fNot(fExists outputs (getOKOutcome  gistedOut))]) >>= \pre2 ->
            simplify (And[getERROutcome gistedOut,fExists outputs (getOKOutcome  gistedOut)]) >>= \pre3 ->
            let lpre1 = (["NEVER_BUG"],pre1) in
            let lpre2 = (["MUST_BUG"],pre2) in
            let lpre3 = (["MAY_BUG"],pre3) in
            when (methName m=="main") (putStrFS ("Set of ERRs["++show (length newMethErrs)++"]:= {" ++ showImpp newMethErrs++"};")) >> 
            let notFalse = (filter (\(lbl,f) -> case f of {EqK [Const 0,Const 1] -> False;_ -> True}) newMethErrs) in
            when (methName m=="main") (putStrFS ("Set of ERRs not False["++show (length notFalse)++"]:= {"++ showImpp notFalse++"};")) >> 
            return (updateMethDecl prog m{methOut=gistedOut,methErrs=newMethErrs,methOutBugs=[lpre1,lpre2,lpre3]})
          else
            return (updateMethDecl prog m{methOut=gistedOut,methErrs=newMethErrs})

replaceAllWithFormula:: [LabelledFormula] -> Formula -> FS Formula
replaceAllWithFormula [] formula = return formula
replaceAllWithFormula ((thislbl,thisf):ls) formula = 
  replaceLblWithFormula (thislbl,thisf) formula >>= \replF ->
  replaceAllWithFormula ls replF
  
replaceLblWithFormula:: LabelledFormula -> Formula -> FS Formula
replaceLblWithFormula (thislbl,thisf) formula = case formula of 
  And fs -> mapM (replaceLblWithFormula (thislbl,thisf)) fs >>= \repls -> return (And repls)
  Or fs -> mapM (replaceLblWithFormula (thislbl,thisf)) fs >>= \repls -> return (Or repls)
  Not f -> replaceLblWithFormula (thislbl,thisf) f >>= \repl -> return (Not repl)
  Exists qsvs f -> replaceLblWithFormula (thislbl,thisf) f >>= \repl -> return (Exists qsvs repl)
  GEq us -> return formula
  EqK us -> return formula
  AppRecPost mn insouts -> return formula
  QLabelSubst subst lbl -> if (lbl==thislbl) then lblApply subst thisf else return formula
  _ -> error ("unexpected argument: "++show formula)

replaceAllWithFalse:: Formula -> FS Formula
replaceAllWithFalse formula = case formula of
  And fs -> mapM replaceAllWithFalse fs >>= \repls -> return (And repls)
  Or fs -> mapM replaceAllWithFalse fs >>= \repls -> return (Or repls)
  Not f -> replaceAllWithFalse f >>= \repl -> return (Not repl)
  Exists qsvs f -> replaceAllWithFalse f >>= \repl -> return (Exists qsvs repl)
  GEq us -> return formula
  EqK us -> return formula
  AppRecPost mn insouts -> return formula
  QLabelSubst subst lbl -> return fFalse
  _ -> error ("unexpected argument: "++show formula)

outInferExp:: Prog -> Exp -> Lit -> [QSizeVar] -> TypeEnv -> Outcomes -> RecFlags 
  -> FS (AnnoType,Outcomes,[LabelledFormula])
-------KTrue-----------------------
outInferExp prog KTrue mn _ gamma outcomes recFlags = 
  fresh >>= \s ->
  let ty = PrimBool{anno=Just s} in
  let out = outAnd outcomes (EqK[Coef (SizeVar s,Unprimed) (-1),Const 1]) in
  return (ty,out,[])
-------KFalse----------------------
outInferExp prog KFalse mn _ gamma outcomes recFlags = fresh >>= \s ->
  let ty = PrimBool{anno=Just s} in
  let out = outAnd outcomes (EqK[Coef (SizeVar s,Unprimed) (-1),Const 0]) in
  return (ty,out,[])
-------KInt------------------------
outInferExp prog (KIntNum n) _ _ _ outcomes recFlags = fresh >>= \s ->
  let ty = PrimInt{anno=Just s} in
  let out = outAnd outcomes (EqK[Coef (SizeVar s,Unprimed) (-1),Const n]) in
  return (ty,out,[])
-------KFloat----------------------
outInferExp prog (KFloatNum f) _ _ _ outcomes recFlags = 
  let ty = PrimFloat{anno=Nothing} in
  return (ty,outcomes,[])
-------KVoid-----------------------
outInferExp prog (KVoid) _ _ _ outcomes recFlags = 
  let ty = PrimVoid{anno=Nothing} in
  return (ty,outcomes,[])
-------ExpBogus--------------------
outInferExp prog ExpBogus mn _ _ _ recFlags =
  error $ "ExpBogus: variable declaration without initialization??\n in function: " ++ mn
-------Var-------------------------
outInferExp prog (ExpVar lit) mn v gamma outcomes recFlags= 
  case lookupVar lit gamma of
    Nothing -> error $ "undefined variable " ++ lit ++ "\n in function " ++ mn
    Just ty -> freshTy ty >>= \typ ->
      equate (typ,ty) (Unprimed,Primed) >>= \(Just phi) ->
      let out = outAnd outcomes phi in
      return (typ,out,[])
-------VarAssign-------------------
outInferExp prog@(Prog _ _ meths) exp@(AssignVar lit e1) mn v gamma outcomes recFlags=
  case lookupVar lit gamma of
    Nothing -> error $ "undefined variable " ++ lit ++ "\n "++showImppTabbed exp 1++"\n in function " ++ mn
    Just ty ->
      outInferExp prog e1 mn v gamma outcomes recFlags >>= \(ty1,outcomes1,errF) ->
      equate (ty,ty1) (Primed,Unprimed) >>= \(Just phi) ->
      fsvTy ty1 >>= \x ->
      impFromTy ty >>= \u ->
      outcomposition u outcomes1 phi >>= \outcomesA ->
      return (PrimVoid{anno=Nothing},outExists x outcomesA,errF) 

-------Seq-------------------------
outInferExp prog (Seq e1 e2) mn v gamma outcomes recFlags = 
  outInferExp prog e1 mn v gamma outcomes recFlags >>= \(ty1,outcomes1,errF1) ->
  fsvTy ty1 >>= \x ->
  outInferExp prog e2 mn v gamma (outExists x outcomes1) recFlags >>= \(ty2,outcomes2,errF2) ->
  return $ (ty2,outcomes2,errF1++errF2)

-------If--------------------------
outInferExp prog exp@(If False (ExpVar lit) exp1 exp2) mn v gamma outcomes recFlags = 
  let bty = (case lookupVar lit gamma of Just ty@PrimBool{} -> ty) in
  case bty of
      PrimBool{anno=Just b} ->
        let qb = (SizeVar b,Primed) in
        let outcomesb1 = outAnd outcomes (EqK [Coef qb (-1),Const 1])  in
        let outcomesb0 = outAnd outcomes (EqK [Coef qb 1]) in 
        outInferExp prog exp1 mn v gamma outcomesb1 recFlags >>= \(ty1,outcomes1,errF1) ->
        outInferExp prog exp2 mn v gamma outcomesb0 recFlags >>= \(ty2,outcomes2,errF2) ->
            (case (ty1,ty2) of
              (_,_) -> freshTy ty1) >>= \ty ->
              rename ty1 ty >>= \(Just rho1) -> --can't fail
              rename ty2 ty >>= \(Just rho2) -> 
                  outdebugApply rho1 outcomes1 >>= \rho1outcomes1 ->
                  outdebugApply rho2 outcomes2 >>= \rho2outcomes2 ->
                  let outcomesp = outOr rho1outcomes1 rho2outcomes2 in
                    return (ty,outcomesp,errF1++errF2)

-------IfNonDet--------------------------
outInferExp prog exp@(If {-nonDet-} True (ExpVar lit) exp1 exp2) mn v gamma outcomes recFlags = 
  initialTransFromTyEnv gamma >>= \deltaInit ->
  let outcomes0 = [OK deltaInit, ERR fFalse] in 
  outInferExp prog exp1 mn v gamma outcomes0 recFlags >>= \(ty1,outcomes1,errF1) ->
  outInferExp prog exp2 mn v gamma outcomes0 recFlags >>= \(ty2,outcomes2,errF2) ->
  (case (ty1,ty2) of
    (_,_) -> freshTy ty1) >>= \ty ->
    rename ty1 ty >>= \(Just rho1) -> --can't fail
    rename ty2 ty >>= \(Just rho2) -> 
        outdebugApply rho1 outcomes1 >>= \rho1outcomes1 ->
        outdebugApply rho2 outcomes2 >>= \rho2outcomes2 ->
        impFromTyEnv gamma >>= \imp -> impFromTy ty >>= \res -> 
        let v = primeTheseQSizeVars imp ++ res in
        outNonDet v rho1outcomes1 rho2outcomes2 >>= \outcomesNonDet ->
        outoutcomposition imp outcomes outcomesNonDet >>= \outcomesp ->
          return (ty,outcomesp,errF1++errF2)
        
-------Empty Block-----------------
outInferExp prog (ExpBlock [] exp1) mn v gamma outcomes recFlags = 
  outInferExp prog exp1 mn v gamma outcomes recFlags 

-------Block1-DeclVar--------------
outInferExp prog exp@(ExpBlock [VarDecl ty lit exp1] exp2) mn v gamma outcomes recFlags = 
  outInferExp prog exp1 mn v gamma outcomes recFlags >>= \(ty1,outcomes1,errF1) ->
  impFromTyEnv gamma >>= \u ->
  initialTransFromTy ty >>= \psi ->
  equate (ty1,ty) (Unprimed,Primed) >>= \(Just equ) ->
  let outcomes1p = outAnd outcomes1 equ in
  let extGamma = extendTypeEnv gamma (lit,ty) in
  (fsvTy ty1) >>= \x ->
  let outcomesP = outAnd (outExists x outcomes1p) psi in
  outInferExp prog exp2 mn v extGamma outcomesP recFlags >>= \(ty2,outcomes2,errF2) ->
  fsvTy ty >>= \svty -> impFromTy ty >>= \isvty ->
  let y = svty `union` primeTheseQSizeVars isvty in
  return (ty2,outExists y outcomes2,errF1++errF2)

-------Block2-DeclArr--------------
outInferExp prog exp@(ExpBlock [LblArrVarDecl lbl ty indxs lit exp1] exp2) mn v gamma outcomes recFlags = 
  case ty of
    ArrayType{elemType=elemTy,indxTypes=iTys} ->
      let lits = map(\i -> case i of 
            ExpVar lit -> lit
            _ -> error $ "incompatible expressions in array declaration\n found: " ++ showImppTabbed i 1 ++ "\nrequired: variable.\n") indxs in
      let tyvs = map (\l -> case lookupVar l gamma of
            Nothing -> error $ "undefined variable " ++ lit ++ " in function " ++ mn ++ "\n "++showImppTabbed exp 1
            Just ty@PrimInt{} -> ty
            Just ty -> error $ "incompatible types in array declaration - indexes must be integers\nfound: "++showImpp ty++"\nrequired: "++showTy PrimInt{anno=Nothing}++"\n "++showImppTabbed exp 1) lits in
      let sisPair = map (\tyv -> case tyv of {
                                PrimInt{anno=Just s} -> ((SizeVar s,Unprimed),(SizeVar s,Primed));
                                _ -> error $ "variable used for initialization of dimensions of array is not annotated: " ++ showImpp tyv ++ "\n "++showImppTabbed exp 1}
                    ) tyvs in
      let (sisU,sisP) = unzip sisPair in
      -- check same no of dimensions
      if not (length iTys == length tyvs) then 
        error $ "incompatible no. of dimensions in array declaration: " ++ concatSepByCommaImpp iTys ++ " and " ++ concatSepByCommaImpp tyvs ++ "\n "++showImppTabbed exp 1
      else
      -- check same type for each dimension: should be TyInt
      let sGT0sUnprimed = map (\si -> fGT[Coef si 1]) sisU in
      let sGT0sPrimed = map (\si -> fGT[Coef si 1]) sisP in
      mapM (\(n,s) -> equate (n,s) (Unprimed,Primed) >>= \eqF -> case eqF of {
                                  Nothing -> error $ "incompatible types\nfound: " ++ showImpp s ++ "\nrequired: " ++ showImpp n ++ "\n "++ showImppTabbed exp 1;
                                  Just equ -> return equ}
                      ) (zip iTys tyvs) >>= \nEqs -> -- no need for zipOrFail
      let checks = map (\(sGT0,cnt) -> (genLabelArr lbl cnt,sGT0)) (zip sGT0sUnprimed (enumFrom 1)) in -- no need for zipOrFail
      let errF0 = map (\(lbl,f) -> (lbl,fNot f)) checks in
      outInferExp prog exp1 mn v gamma outcomes recFlags >>= \(tp,outcomes1,errF1) ->
      -- check init value is of the same type as elemTy
      initArrFormula tp ty >>= \arrFormula ->
      case arrFormula of
        Nothing -> error $ "incompatible types in array declaration\nfound: " ++ showImpp tp ++ "\ndeclared array: " ++ showImpp ty ++ "\n " ++showImppTabbed exp 1
        Just indirPsi ->
          let outWithChecks = outoutAnd outcomes1 [OK fTrue,ERR (fOr (map (\(lbl,_) -> QLabelSubst [] lbl) checks))] in
          let fstComp = outAnd outWithChecks indirPsi in 
          let sndComp = fAnd (sGT0sPrimed++nEqs) in
          let gammap = extendTypeEnv gamma (lit,ty) in
          impFromTyEnv gammap >>= \u ->
          let outcomes1p = outAnd fstComp sndComp in 
            addOmegaStr ("=========\nDuring inference: declaration of array " ++ lit ++ "\n=========") >>
            initialTransFromTyEnv gamma >>= \invFromGamma ->
            mkChks v u (triple (getOKOutcome outcomes1)) invFromGamma checks >>= \(phisp,errs) ->
              fsvTy tp >>= \x ->
              fsvTy ty >>= \svty -> 
              impFromTy ty >>= \isvty ->
              let y = svty `union` primeTheseQSizeVars isvty in
                outInferExp prog exp2 mn v gammap (outExists x outcomes1p) recFlags >>= \(ty2,outcomes2,errF2) ->
                  return $ (ty2,outExists y outcomes2,errF0++errF1++errF2)
--                  return $ (ty2,outExists y outcomes2,errF1++errF2)
    _ -> error $ "incompatible types\n found: " ++ showImpp ty ++ "\nrequired: array type in declaration of " ++ lit ++ "\n "++showImppTabbed exp 1

outInferExp (Prog _ prims meths) exp@(LblMethCall (Just crtlbl) fName argsIdent) 
  mn v gamma out (wPhase,sccFs) =
  let getArgsTypes = \argIdent -> case argIdent of ExpVar lit -> case lookupVar lit gamma of{Just ty -> ty} in
    let argsTyps = map getArgsTypes argsIdent in 
    impFromTyEnv gamma >>= \u ->
    concatMapM impFromTy argsTyps >>= \wWithDup -> let w = nub wWithDup in
    qsvFromTyEnv gamma >>= \uRec -> -- to derive preRec, nonImp must be in U
    let callables = map (\p -> Prim p) prims ++ map (\m -> Meth m) meths in
    let calleeDef = findCallable fName callables in
    (case calleeDef of
          Just (Meth m) -> 
            setsForParamPassing (fromJust calleeDef) >>= \(_,_,_,_,qsvByVal) ->
            let outOK = getOKOutcome $ outAnd (methOut m) (noChange qsvByVal) in
            let outERR = fOr $ map (\(lbl,_) -> QLabelSubst [] (crtlbl:lbl)) (methErrs m) in 
            let errFormulae = map (\(lbl,f) -> (crtlbl:lbl,f)) (methErrs m) in --retrieve methErrs
            return (fst3(unzip3(methParams m)),snd3(unzip3(methParams m)),[OK outOK, ERR outERR],errFormulae)
          Just (Prim p) -> 
            let strongPost = And ((primPost p):(map (\(lbl,f) -> f) (primPres p))) in
            let outERR = fOr (map (\ (lbl,f) -> QLabelSubst [] (crtlbl:lbl)) (primPres p)) in
            let errFormulae = map (\ (lbl,f) -> (crtlbl:lbl,fNot f)) (primPres p) in
            return (fst3(unzip3(primParams p)),snd3(unzip3(primParams p)),[OK strongPost, ERR outERR],errFormulae)
    ) >>= \(formalPassBy,formalTyps,outm,errF) ->
    freshTy (head formalTyps) >>= \typ ->
    let actualTyps = typ:argsTyps in
    let zipped = zip formalTyps actualTyps in
    concatMapM(\(t,tp) -> rename t tp >>= \(Just rho) -> return rho) zipped >>= \rho ->
    let isRecCall = fName `elem` sccFs in 
    case wPhase of
      0 -> -- caller (current funtion) is a non-recursive function
          outdebugApply rho outm >>= \rhooutm ->
          outoutcomposition w out rhooutm >>= \out2 ->
          return (typ,out2,errF)
      3 -> -- caller is recursive: gather recursive CAbst for OK-outcome
          if isRecCall then 
            let zp = zip3 formalPassBy actualTyps (replicate (length actualTyps) undefined) in
            let methForSets = (case (fromJust calleeDef) of {Meth m -> m;_->error ""}){methParams=zp} in
            setsForParamPassing (Meth methForSets) >>= \(inputs,outputs,res,_,qsvByVal) ->
            let insouts = inputs `union` outputs in
            let delta1 = (And [noChange qsvByVal,AppRecPost fName insouts]) in
            let out1 = [OK delta1, ERR fFalse] in
            outoutcomposition w out out1 >>= \out2 ->
            return $ (typ,out2,errF) 
          else
            outdebugApply rho outm >>= \rhooutm ->
            outoutcomposition w out rhooutm >>= \out2 ->
            return $ (typ,out2,errF)
      4 -> -- caller is recursive: gather recursive CAbst for ERR-outcome (after fixpoint for OK-outcome)
          if isRecCall then 
            let zp = zip3 formalPassBy actualTyps (replicate (length actualTyps) undefined) in
            let methForSets = (case (fromJust calleeDef) of {Meth m -> m;_->error ""}){methParams=zp} in
            setsForParamPassing (Meth methForSets) >>= \(inputs,outputs,res,_,qsvByVal) ->
            let insouts = inputs `union` outputs in
            let delta1 = (And [noChange qsvByVal,AppRecPost fName insouts]) in
            outdebugApply rho outm >>= \rhooutm ->
            let out1 = [OK (getOKOutcome rhooutm), ERR delta1] in -- retrieve result of fixpoint for OK
            outoutcomposition w out out1 >>= \out2 ->
            return $ (typ,out2,errF) 
          else
            outdebugApply rho outm >>= \rhooutm ->
            outoutcomposition w out rhooutm >>= \out2 ->
            return $ (typ,out2,errF) 
      5 -> -- caller is recursive: using TransInv derive fstERRs/recERRs. For the crt call use: [OK fixOK, ERR fFalse]
          if isRecCall then 
            outdebugApply rho outm >>= \rhooutm ->
            let out1 = [OK (getOKOutcome rhooutm), ERR fFalse] in -- retrieve result of fixpoint for OK
            outoutcomposition w out out1 >>= \out2 ->
            return $ (typ,out2,errF) 
          else
            outdebugApply rho outm >>= \rhooutm ->
            outoutcomposition w out rhooutm >>= \out2 ->
            return $ (typ,out2,errF) 


getNeverBug:: [LabelledFormula] -> [LabelledFormula]
getNeverBug phis = -- [head phis]
  [] -- disable checking of the preconditions