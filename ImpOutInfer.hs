module ImpOutInfer(outInferSccs,applyRecToPrimOnInvariant,RecFlags) where
import Fresh(runFS,FS(),initialState,fresh,takeFresh,addOmegaStr,writeOmegaStrs,getFlags,putStrFS,getCPUTimeFS)
import ImpAST
import ImpConfig(Flags,checkingAfterInference,noRecPreDerivation,separateFstFromRec,Prederivation(..),prederivation,Postcondition(..),postcondition,useFixpoint2k)
import ImpFormula
import ImpFixpoint(fixpoint)
import ImpFixpoint2k(fixpoint2k)
import ImpTypeCommon
import MyPrelude
-----------------
import Data.Graph(SCC(..),stronglyConnComp)
import List(union,unzip4,(\\),nub)
import Maybe(catMaybes,fromJust)
import Monad(when)

type RecFlags = (Int,[Lit]) -- (whatPhase,nameOfRecFs)
-- whatPhase: 0 - noRecursion; 1 - collect cAbst; 2 - derive preconditions
-- whatPhase: 3 - collect cAbst for OK outcome; 4 - collect cAbst for ERR outcome

applyRecToPrimOnInvariant:: Formula -> FS Formula
applyRecToPrimOnInvariant inv =
  let qsv = fqsv inv in
  let recs = filter (\q -> case q of {(s,Recursive) -> True;_ -> False} ) qsv in
  let prims = map (\q -> case q of {(s,Recursive) -> (s,Primed);_ -> error "assertion failed in applyRecToPrimOnInvariant"}) recs in
  debugApply (zip recs prims) inv

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

outInferSccs:: Prog -> [SCC MethDecl] -> FS Prog
outInferSccs prog [] = return prog
outInferSccs prog (scc:sccs) = 
  outInferScc prog scc >>= \updProg ->
  outInferSccs updProg sccs

outInferScc:: Prog -> SCC MethDecl -> FS Prog
outInferScc prog scc =
  case scc of
    AcyclicSCC mDecl ->
      putStrFS ("Inferring " ++ methName mDecl ++ "...") >> getCPUTimeFS >>= \time1 ->
      outInferMethDeclNonRec prog (findMethod (methName mDecl) prog) >>= \updProg2 ->
      getCPUTimeFS >>= \time2 ->
      putStrFS ("###Inferring " ++ methName mDecl ++ "...done in " ++ showDiffTimes time2 time1++"###") >> 
      return updProg2
    CyclicSCC mDecls ->
      if (length mDecls /= 1) then error "Mutual recursion is not implemented"
      else
        let mDecl = (head mDecls) in
        putStrFS ("###Inferring " ++ methName mDecl ++ "...###") >> getCPUTimeFS >>= \time1 ->
        outInferMethDeclRec prog (findMethod (methName mDecl) prog) >>= \updProg2 ->  
        getCPUTimeFS >>= \time2 ->
        putStrFS ("Inferring " ++ methName mDecl ++ "...done in " ++ showDiffTimes time2 time1) >> 
        return updProg2

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
--          mapM (\fdecl@(FormulaDecl lbl qsvs f) -> case f of 
--                            EqK [Const 0,Const 1] -> return ([lbl],f)
--                            _ ->
--                              replaceLblWithFormula (getERROutcome out1) fdecl >>= \replF ->
--                              replaceAllWithFalse replF >>= \fstf ->
--                              gistCtxGivenInv fstf typeInv >>= \gfstf ->
--                              putStrFS("fstERR"++lbl++":="++showSet gfstf) >>
--                              composition u deltaTransInv gfstf >>= \recf ->                              
--                              gistCtxGivenInv recf typeInv >>= \grecf ->
--                              putStrFS("recERR"++lbl++":="++showSet grecf) >>
--                              return ([lbl],Or [gfstf,grecf])) errs >>= \newMethErrs ->
--          gistCtxGivenInv (fOr (map (\(lbl,f) -> f) newMethErrs)) typeInv >>= \gistedERR ->
-- all ERRs at once
          replaceAllWithFormula (getERROutcome out1) errs >>= \replF ->
          simplify replF >>= \fstf ->
          putStrFS("fstERR:="++showSet fstf) >>
          composition u deltaTransInv fstf >>= \recf ->
          simplify recf >>= \grecf ->
          putStrFS("recERR:="++showSet grecf) >>
          let newMethErrs = [(["ERR"],Or [fstf,grecf])] in
          let gistedERR = Or [fstf,grecf] in
---COMMON: each or all ERRs
          let gistedOut = [OK gistedOK,ERR gistedERR] in
------prederivation
                simplify (And [fExists outputs (getOKOutcome gistedOut),fNot (getERROutcome gistedOut)]) >>= \pre1 ->
                simplify (And[getERROutcome gistedOut,fNot(fExists outputs (getOKOutcome  gistedOut))]) >>= \pre2 ->
                simplify (And[getERROutcome gistedOut,fExists outputs (getOKOutcome  gistedOut)]) >>= \pre3 ->
                let lpre1 = (["NEVER_BUG"],pre1) in
                let lpre2 = (["MUST_BUG"],pre2) in
                let lpre3 = (["MAY_BUG"],pre3) in
                return (updateMethDecl prog m{methOut=gistedOut,methErrs=newMethErrs,methOutBugs=[lpre1,lpre2,lpre3]})

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
------ each ERR separately
--          mapM (\fdecl@(FormulaDecl lbl qsvs f) -> case f of 
--                            EqK [Const 0,Const 1] -> return ([lbl],f)
--                            _ ->
--                              replaceLblWithFormula (getERROutcome out1) fdecl >>= \replF ->
--                              replaceAllWithFalse replF >>= \replAllF ->
--                              gistCtxGivenInv replAllF typeInv >>= \f ->
--                              putStrFS("ERR"++lbl++":="++showSet f) >>
--                              return ([lbl],f)) errF >>= \newMethErrs ->
--          gistCtxGivenInv (fOr (map (\(lbl,f) -> f) newMethErrs)) typeInv >>= \gistedERR ->
-- all ERRs at once
          replaceAllWithFormula (getERROutcome out1) errF >>= \replF ->
          simplify replF >>= \f ->
          putStrFS("ERR:="++showSet f) >>
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

replaceAllWithFormula:: Formula -> [FormulaDecl] -> FS Formula
replaceAllWithFormula formula [] = return formula
replaceAllWithFormula formula (f:fs) = 
  replaceLblWithFormula formula f >>= \replF ->
  replaceAllWithFormula replF fs
  
replaceLblWithFormula:: Formula -> FormulaDecl -> FS Formula
-- ^similar function to ImpFixpoint2k.subrec.
-- For example: replaceLblWithFormula (...lblH(f0,f1)...) [FormulaDecl lblH [i,s] (i<s)] = (...(f0<f1)...)
replaceLblWithFormula formula fdecl@(FormulaDecl lbl formalQsvs formalf) = case formula of 
  And fs -> mapM (\f -> replaceLblWithFormula f fdecl) fs >>= \repls -> return (And repls)
  Or fs -> mapM (\f -> replaceLblWithFormula f fdecl) fs >>= \repls -> return (Or repls)
--  Not f -> replaceLblWithFormula f (thislbl,thisf) >>= \repl -> return (Not repl)
  Exists qsvs f -> replaceLblWithFormula f fdecl >>= \repl -> return (Exists qsvs repl)
  GEq us -> return formula
  EqK us -> return formula
  AppRecPost mn insouts -> 
    if (mn ==lbl) then let rho = zip formalQsvs insouts in debugApply rho formalf
    else return formula
  _ -> error ("unexpected argument: "++show formula)

replaceAllWithFalse:: Formula -> FS Formula
replaceAllWithFalse formula = case formula of
  And fs -> mapM replaceAllWithFalse fs >>= \repls -> return (And repls)
  Or fs -> mapM replaceAllWithFalse fs >>= \repls -> return (Or repls)
--  Not f -> replaceAllWithFalse f >>= \repl -> return (Not repl)
  Exists qsvs f -> replaceAllWithFalse f >>= \repl -> return (Exists qsvs repl)
  GEq us -> return formula
  EqK us -> return formula
  AppRecPost mn insouts -> return fFalse
  _ -> error ("unexpected argument: "++show formula)

outInferExp:: Prog -> Exp -> Lit -> [QSizeVar] -> TypeEnv -> Outcomes -> RecFlags 
  -> FS (AnnoType,Outcomes,[FormulaDecl])
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
-- Point?
        outsimplify outcomes >>= \outcomesSimpl -> 
        let qb = (SizeVar b,Primed) in
        let outcomesb1 = outAnd outcomesSimpl (EqK [Coef qb (-1),Const 1])  in
        let outcomesb0 = outAnd outcomesSimpl (EqK [Coef qb 1]) in 
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
        error $ "incompatible no. of dimensions in array declaration: " ++ concatSepBy "," (map showImpp iTys) ++ " and " ++ concatSepBy "," (map showImpp tyvs) ++ "\n "++showImppTabbed exp 1
      else
      -- check same type for each dimension: should be TyInt
      let sGT0sUnprimed = map (\si -> fGT[Coef si 1]) sisU in
      let sGT0sPrimed = map (\si -> fGT[Coef si 1]) sisP in
      mapM (\(n,s) -> equate (n,s) (Unprimed,Primed) >>= \eqF -> case eqF of {
                                  Nothing -> error $ "incompatible types\nfound: " ++ showImpp s ++ "\nrequired: " ++ showImpp n ++ "\n "++ showImppTabbed exp 1;
                                  Just equ -> return equ}
                      ) (zip iTys tyvs) >>= \nEqs -> -- no need for zipOrFail
      let checks = map (\(sGT0,cnt) -> (genLabelArr lbl cnt,sGT0)) (zip sGT0sUnprimed (enumFrom 1)) in -- no need for zipOrFail
      outInferExp prog exp1 mn v gamma outcomes recFlags >>= \(tp,outcomes1,errF1) ->
      -- check init value is of the same type as elemTy
      initArrFormula tp ty >>= \arrFormula ->
      case arrFormula of
        Nothing -> error $ "incompatible types in array declaration\nfound: " ++ showImpp tp ++ "\ndeclared array: " ++ showImpp ty ++ "\n " ++showImppTabbed exp 1
        Just indirPsi ->
          mapM (\(lbl,f) -> simplify (fNot f) >>= \negf -> return (FormulaDecl (concat lbl) (fqsv f) negf)) checks >>= \errF0 ->
          let outWithChecks = outoutAnd outcomes1 [OK fTrue,ERR (fOr (map (\(lbl,chk) -> AppRecPost (concat lbl) (fqsv chk)) checks))] in
          let fstComp = outAnd outWithChecks indirPsi in 
          let sndComp = fAnd (sGT0sPrimed++nEqs) in
          let gammap = extendTypeEnv gamma (lit,ty) in
          impFromTyEnv gammap >>= \u ->
          let outcomes1p = outAnd fstComp sndComp in 
            addOmegaStr ("=========\nDuring inference: declaration of array " ++ lit ++ "\n=========") >>
            initialTransFromTyEnv gamma >>= \invFromGamma ->
              fsvTy tp >>= \x ->
              fsvTy ty >>= \svty -> 
              impFromTy ty >>= \isvty ->
              let y = svty `union` primeTheseQSizeVars isvty in
                outInferExp prog exp2 mn v gammap (outExists x outcomes1p) recFlags >>= \(ty2,outcomes2,errF2) ->
                  return $ (ty2,outExists y outcomes2,errF0++errF1++errF2)
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
            let outERR = fOr (map (\(lbl,f) -> AppRecPost (concat (crtlbl:lbl)) (fqsv f)) (methErrs m)) in 
            let errFormulae = map (\(lbl,f) -> FormulaDecl (concat (crtlbl:lbl)) (fqsv f) f) (methErrs m) in --retrieve methErrs
            return (fst3(unzip3(methParams m)),snd3(unzip3(methParams m)),[OK outOK, ERR outERR],errFormulae)
          Just (Prim p) -> 
            let strongPost = And ((primPost p):(map (\(lbl,f) -> f) (primPres p))) in
            let outERR = fOr (map (\ (lbl,f) -> AppRecPost (concat (crtlbl:lbl)) (fqsv f)) (primPres p)) in
            mapM (\ (lbl,f) -> simplify (fNot f) >>= \negf -> return (FormulaDecl (concat (crtlbl:lbl)) (fqsv f) negf)) (primPres p) >>= \errFormulae ->
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