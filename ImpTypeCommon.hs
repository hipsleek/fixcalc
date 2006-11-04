-------Common to checking and inference
module ImpTypeCommon where
import ImpAST
import ImpConfig(isIndirectionIntArray)
import Fresh(FS,fresh,takeFresh,getFlags,putStrFS)
import ImpFormula(fsvTy,noChange,primeTheseQSizeVars,sameBaseTy,sizeVarsFromAnnTy)
import MyPrelude(tr,concatMapM,snd3,fst3)
------------------------------------------
import List(nub,union)
import Maybe(fromJust)

-----SimpleTypeChecking----------
-------SimpleTypeChecking----------
sTypeCheck:: Prog -> FS Prog
sTypeCheck prog@(Prog incls prims meths) = 
  let dupMeth = checkMethDuplicates meths in
  case dupMeth of
    Just m -> error $ "Double definition for method " ++ m ++ "\n"
    Nothing -> 
      mapM (sTypeCheckMethDecl prog) meths >>= \res ->
      mapM sTypeCheckPrimDecl prims >>= \primRes ->
      let primok = and primRes in
      if not primok then
        error $ ""
      else
        let (newMdss,newMeths) = unzip res in
        let allMeths = newMeths++(concat newMdss) in
        return (Prog incls prims allMeths)

sTypeCheckPrimDecl:: PrimDecl -> FS Bool
sTypeCheckPrimDecl p =
  getFlags >>= \flags ->  
  let ((_,retTy,fname):args) = primParams p in
  if (isIndirectionIntArray flags) && not (isPrimitiveType retTy) then
    error $ "Analysis of array indirection is enabled.\nReturn type of primitive "++fname++" must be a primitive type.\n"
  else 
    return True

sTypeCheckMethDecl:: Prog -> MethDecl -> FS ([MethDecl],MethDecl)
sTypeCheckMethDecl prog m =
  getFlags >>= \flags ->  
  let ((_,retTy,fname):args) = methParams m in
  if (isIndirectionIntArray flags) && not (isPrimitiveType retTy) then
    error $ "Analysis of array indirection is enabled.\nReturn type of any method must be a primitive type.\n" ++ showImpp m
  else 
    let (_,annTys,lits) = unzip3 args in
    let gamma = zip lits annTys in
    sTypeCheckExp prog (methBody m) fname gamma >>= \(newMds,newEb,ty) ->
    if not (sameBaseTy ty retTy) then
      error $ "incompatible types\nfound "++showTy ty++ "\nrequired: "++showTy retTy++"\n "++showImpp m
    else
      let newMDecl = m{methBody=newEb} in
      return (newMds,newMDecl)

checkMethDuplicates:: [MethDecl] -> Maybe String
checkMethDuplicates [] = Nothing
checkMethDuplicates (m:ms) = 
  if null (filter (\m2 -> methName m == methName m2) ms) then
    checkMethDuplicates ms
  else
    Just (methName m)

sTypeCheckExp:: Prog -> Exp -> Lit -> TypeEnv -> FS ([MethDecl],Exp,AnnoType)
sTypeCheckExp prog exp@KTrue mn gamma = return ([],exp,PrimBool{anno=Nothing})
sTypeCheckExp prog exp@KFalse mn gamma = return ([],exp,PrimBool{anno=Nothing})
sTypeCheckExp prog exp@(KIntNum n) mn gamma = return ([],exp,PrimInt{anno=Nothing})
sTypeCheckExp prog exp@(KFloatNum n) mn gamma = return ([],exp,PrimFloat{anno=Nothing})
sTypeCheckExp prog exp@KVoid mn gamma = return ([],exp,PrimVoid{anno=Nothing})
sTypeCheckExp prog exp@(ExpError) mn gamma = error $ "ExpError encountered during simple type checking?\n "++showImppTabbed exp 1
sTypeCheckExp prog exp@(ExpBogus) mn gamma = error $ "ExpBogus: variable declaration without initialization??\n"

sTypeCheckExp prog exp@(ExpVar lit) mn gamma =
  case lookupVar lit gamma of
    Nothing -> error $ "undefined variable " ++ lit ++ "\n in function " ++ mn
    Just ty -> return ([],exp,ty)

sTypeCheckExp prog exp@(AssignVar lit e1) mn gamma =
  sTypeCheckExp prog e1 mn gamma >>= \(newMds1,newE1,ty1) ->
  case lookupVar lit gamma of
    Nothing -> error $ "undefined variable " ++ lit ++ "\n in function " ++ mn
    Just ty -> 
      if not (sameBaseTy ty1 ty) then
        error $ "incompatible types\nfound: " ++ showTy ty1 ++ "\nrequired: " ++ showTy ty ++ "\n "++showImppTabbed exp 1
      else
        return (newMds1,(AssignVar lit newE1),PrimVoid{anno=Nothing})

sTypeCheckExp prog exp@(Seq e1 e2) mn gamma =
  sTypeCheckExp prog e1 mn gamma >>= \(newMds1,newE1,ty1) ->
  sTypeCheckExp prog e2 mn gamma >>= \(newMds2,newE2,ty2) ->
  return (newMds1++newMds2,Seq newE1 newE2,ty2)

sTypeCheckExp prog exp@(If e1 e2 e3) mn gamma = 
  sTypeCheckExp prog e1 mn gamma >>= \(newMds1,newE1,ty1) ->
  if not (sameBaseTy ty1 (PrimBool{anno=Nothing})) then
    error $ "incompatible types in conditional test\nfound: "++showTy ty1++"\nrequired: Bool\n "++showImppTabbed exp 1
  else  
    sTypeCheckExp prog e2 mn gamma >>= \(newMds2,newE2,ty2) ->
    sTypeCheckExp prog e3 mn gamma >>= \(newMds3,newE3,ty3) ->
    if not (sameBaseTy ty2 ty3) then
      error $ "incompatible types in branches of conditional\nfound: "++showTy ty2++"\nand: "++showTy ty3++"\n "++showImppTabbed exp 1
    else
      return (newMds1++newMds2++newMds3,If newE1 newE2 newE3,ty2)

sTypeCheckExp prog@(Prog incls prims meths) exp@(LblMethCall lbl fName args) mn gamma =
  mapM (\arg -> sTypeCheckExp prog arg mn gamma) args >>= \triples ->
  let (newMdss,newArgs,actualTys) = unzip3 triples in
  let newMds = concat newMdss in
  let callables = map (\p -> Prim p) prims ++ map (\m -> Meth m) meths in
  let calleeDef = findCallable fName callables in
  let ((_,retTy,_):formalArgs) = case calleeDef of
          Nothing -> error $ "call to undefined function " ++ fName ++ "\n " ++ showImppTabbed exp 1
          Just (Meth m) -> methParams m
          Just (Prim p) -> primParams p in
  let formalTys = map snd3 formalArgs in
  let argsok = all (\(formalTy,actualTy) -> 
                          if not (sameBaseTy formalTy actualTy) then
                            error $ "incompatible types\nfound "++showTy actualTy++ "\nrequired: "++showTy formalTy++"\n "++showImppTabbed exp 1
                          else True
                   ) (zip formalTys actualTys) in
  return (newMds,LblMethCall lbl fName newArgs,retTy)

sTypeCheckExp prog exp@(While e1 eb) mn gamma = 
  sTypeCheckExp prog e1 mn gamma >>= \(newMd1,newE1,newTy1) ->
  if not (sameBaseTy newTy1 PrimBool{anno=Nothing}) then
    error $ "incompatible types in while test\nfound: "++showTy newTy1++"\nrequired: Bool\n "++showImppTabbed exp 1
  else
    sTypeCheckExp prog eb mn gamma >>= \(newMdEb,newEb,tyEb) ->
    if not (sameBaseTy tyEb PrimVoid{anno=Nothing}) then
      error $ "incompatible types in while body\nfound: "++showTy tyEb++"\nrequired: Void\n "++showImppTabbed exp 1
    else
      fresh >>= \freshNo -> let freshMname = "while"++freshNo in
      let retTy = PrimVoid{anno=Nothing} in
      let whileLits = nub (concatMap freeVars [e1,eb]) in
      let whileArgs = map (\lit -> ExpVar lit) whileLits in
      mapM (\arg -> case lookupVar arg gamma of
                                Nothing -> error $ "undefined variable "++arg++"\n "++ showImppTabbed exp 1
                                Just ty -> 
                                  freshTy ty >>= \annTy ->
                                  return (PassByRef,annTy,arg)
           ) whileLits >>= \argsAndTys ->
      let whileCall = LblMethCall Nothing freshMname whileArgs in
      let newWhileEb = ExpBlock [] (If newE1 (Seq newEb whileCall) KVoid) in
      let newMD = MethDecl {methParams=((PassByRef,retTy,freshMname):argsAndTys),
                            methPost=(triple FormulaBogus),
                            methPres=[],
                            methUpsis=[],
                            methInv=FormulaBogus,
			    methOut=[],
                            methOutPres=[],
                            methBody=newWhileEb} in
      return (newMD:newMd1++newMdEb,whileCall,PrimVoid{anno=Nothing})

sTypeCheckExp prog exp@(For e1 e2 e3 eb) mn gamma = 
  sTypeCheckExp prog e1 mn gamma >>= \(newMd1,newE1,newTy1) ->
  if not (sameBaseTy newTy1 PrimVoid{anno=Nothing}) then
    error $ ""
  else
    sTypeCheckExp prog e2 mn gamma >>= \(newMd2,newE2,newTy2) ->
    sTypeCheckExp prog e3 mn gamma >>= \(newMd3,newE3,newTy3) ->
    sTypeCheckExp prog eb mn gamma >>= \(newMdEb,newEb,newTyEb) ->
    fresh >>= \freshNo -> let freshMname = "for"++freshNo in
    let retTy = PrimVoid{anno=Nothing} in
    let forLits = nub (concatMap freeVars [e2,e3,eb]) in
    let forArgs = map (\lit -> ExpVar lit) forLits in
    mapM (\arg -> case lookupVar arg gamma of
                              Nothing -> error $ "undefined variable "++arg++"\n "++ showImppTabbed exp 1
                              Just ty -> 
                                freshTy ty >>= \annTy ->
                                return (PassByRef,annTy,arg)
         ) forLits >>= \argsAndTys ->
    let forCall = LblMethCall Nothing freshMname forArgs in
    let newForEb = ExpBlock [] (If newE2 (Seq newEb (Seq newE3 forCall)) KVoid) in
    let newMD = MethDecl {methParams=((PassByRef,retTy,freshMname):argsAndTys),
                          methPost=(triple FormulaBogus),
                          methPres=[],
                          methUpsis=[],
                          methInv=FormulaBogus,
			  methOut=[],methOutPres=[],
                          methBody=newForEb} in
    return (newMD:newMd1++newMd2++newMd3++newMdEb,forCall,PrimVoid{anno=Nothing})

sTypeCheckExp prog exp@(ExpBlock varDecls eb) mn gamma =
  sTypeCheckVarDecls prog varDecls mn ([],[],gamma) >>= \(newMds,newVds,gamma1) ->
  sTypeCheckExp prog eb mn gamma1 >>= \(newMdsEb,newEb,tyEb) -> 
  return (newMds++newMdsEb,ExpBlock newVds newEb,tyEb)
  
sTypeCheckVarDecls::Prog -> [VarDecl] -> Lit -> ([MethDecl],[VarDecl],TypeEnv) -> FS ([MethDecl],[VarDecl],TypeEnv)
sTypeCheckVarDecls prog [] mn (partMds,partVds,gamma) = return (partMds,reverse partVds,gamma)
sTypeCheckVarDecls prog (vd:vds) mn (partMds,partVds,gamma) = 
  sTypeCheckVarDecl prog vd mn gamma >>= \(newMds,newVd,gamma1) ->
  sTypeCheckVarDecls prog vds mn (partMds++newMds,newVd:partVds,gamma1)
  
sTypeCheckVarDecl:: Prog -> VarDecl -> Lit -> TypeEnv -> FS ([MethDecl],VarDecl,TypeEnv)
sTypeCheckVarDecl prog vd@(VarDecl declTy lit e1) mn gamma =
  sTypeCheckExp prog e1 mn gamma >>= \(newMd1,newE1,newTy1) ->
  let gamma1 = extendTypeEnv gamma (lit,declTy) in
  if not (sameBaseTy declTy newTy1) then
    error $ "incompatible types\nfound: " ++ showTy newTy1 ++ "\nrequired: " ++ showTy declTy ++ "\n "++ showImppTabbed vd 1
  else
    return (newMd1,VarDecl declTy lit newE1,gamma1)

sTypeCheckVarDecl prog vd@(LblArrVarDecl lbl annTy indxs lit e1) mn gamma =
  sTypeCheckExp prog e1 mn gamma >>= \(newMd1,newE1,newTy1) ->
  mapM (\i -> sTypeCheckExp prog i mn gamma) indxs >>= \triple ->
  let (emptyMds,sameIndxs,indxTys) = unzip3 triple in
  if not $ all (\iTy -> sameBaseTy iTy PrimInt{anno=Nothing}) indxTys then
    error $ "incompatible types in array declaration - indexes must be integers\n "++showImppTabbed vd 1
  else
    let gamma1 = extendTypeEnv gamma (lit,annTy) in
    case annTy of
      ArrayType{elemType=eTy,indxTypes=iTys} ->
        if (length iTys /= length indxs) then
          error $ "incompatible no. of dimension is array declaration\n " ++ showImppTabbed vd 1
        else
          if not (sameBaseTy newTy1 eTy) then 
            error $ "incompatible types\nfound: " ++ showTy newTy1 ++ "\nrequired: " ++ showTy eTy  ++ "\n "++ showImppTabbed vd 1
          else
            return (newMd1,LblArrVarDecl lbl annTy indxs lit newE1,gamma1)

-- remove duplicates before using this: nub
freeVars:: Exp -> [Lit]
freeVars (ExpVar lit) = [lit]
freeVars (AssignVar lit e) = lit:freeVars e
freeVars (If e1 e2 e3) = concatMap freeVars [e1,e2,e3]
freeVars (LblMethCall lbl id es) = concatMap freeVars es
freeVars (Seq e1 e2) = freeVars e1 ++ freeVars e2
freeVars (ExpBlock vds eb) = concatMap freeVarsVarDecl vds++freeVars eb
freeVars (While e1 eb) = freeVars e1 ++ freeVars eb
freeVars (For e1 e2 e3 eb) = concatMap freeVars [e1,e2,e3,eb]
freeVars _ = []

freeVarsVarDecl:: VarDecl -> [Lit]
freeVarsVarDecl (VarDecl primTy lit e1) = lit:freeVars e1
freeVarsVarDecl (LblArrVarDecl lbl arrTy indxs lit e1) = lit:concatMap freeVars (e1:indxs)

-------TypeEnvironment-------------
type TypeEnv = [(Lit,AnnoType)]

emptyTypeEnv :: TypeEnv
emptyTypeEnv = []

extendTypeEnv :: TypeEnv -> (Lit,AnnoType) -> TypeEnv
extendTypeEnv gamma (var,ty) = 
  (var,ty):gamma

lookupVar :: Lit -> TypeEnv -> Maybe AnnoType
lookupVar lit [] = Nothing
lookupVar lit env@((v,ty):rest) | (lit == v) = Just ty
  | otherwise = lookupVar lit rest

freshTy:: AnnoType -> FS AnnoType
freshTy ty = case ty of
  PrimBool{} -> fresh >>= \fsh -> return $ PrimBool{anno=Just fsh}
  PrimFloat{} -> return $ PrimFloat{anno=Nothing}
  PrimInt{} -> fresh >>= \fsh -> return $ PrimInt{anno=Just fsh}
  PrimVoid{} -> return $ PrimVoid{anno=Nothing}
  ArrayType{elemType=eTy,indxTypes=iTys} ->
    mapM freshTy iTys >>= \fshITys ->
    freshTy eTy >>= \fshETy ->
    return $ ArrayType{elemType=fshETy,indxTypes=fshITys}

-- Given a function: compute five sets of QSizeVar:
-- inputs: set of boundary size variables. To be used in type judgement (V)
-- outputs: primed qsvByRef + return
-- res: set of size variables in return type
-- qsvByRef: imperative size variables that are passed by reference. x \subset Imp(v)
-- qsvByVal: imperative size variables that are passed by value. y \subset Imp(v) and x+y = Imp(v)
setsForParamPassing:: Callable -> FS ([QSizeVar],[QSizeVar],[QSizeVar],[QSizeVar],[QSizeVar])
setsForParamPassing (Meth m) = 
  let ((passbyM,t,fname):args) = methParams m in
  concatMapM (\(_,tyi,argi) -> fsvTy tyi) args >>= \inputs ->
  fsvTy t >>= \res ->
  impFromTy t >>= \impRes ->
  case passbyM of
    PassByRef ->
      return [] >>= \qsvByVal ->
      concatMapM (\(_,tyi,namei) -> impFromTy tyi) args >>= \qsvByRef ->
      let outputs = primeTheseQSizeVars qsvByRef ++ impRes in
--      putStrFS ("Sets-FnByRef: " ++ show inputs ++ "\t" ++ show res ++ "\t" ++ show qsvByRef ++ "\t" ++ show qsvByVal ++ "\n") >>
      return (inputs,outputs,res,qsvByRef,qsvByVal)
    PassByVal ->
      concatMapM (\(passbyi,tyi,namei) -> case tyi of {ArrayType{} -> return [];_ -> if (passbyi==PassByVal) then impFromTy tyi else return []}) args >>= \qsvByVal ->
      concatMapM (\(passbyi,tyi,namei) -> case tyi of {ArrayType{} -> minmaxFromTy tyi;_ -> if (passbyi==PassByRef) then impFromTy tyi else return []}) args >>= \qsvByRef ->
      let outputs = primeTheseQSizeVars qsvByRef ++ impRes in
--      putStrFS ("Sets-FnByVal: " ++ show inputs ++ "\t" ++ show res ++ "\t" ++ show qsvByRef ++ "\t" ++ show qsvByVal ++ "\n") >>
      return (inputs,outputs,res,qsvByRef,qsvByVal)

setsForParamPassing (Prim p) = 
  let ((_,t,fname):args) = primParams p in
  concatMapM (\(_,tyi,argi) -> fsvTy tyi) args >>= \inputs ->
  concatMapM (\(_,tyi,argi) -> impFromTy tyi) args >>= \impInputs ->
  fsvTy t >>= \res ->
  impFromTy t >>= \impRes ->
  let outputs = primeTheseQSizeVars impInputs `union` impRes in
  concatMapM (\(_,tyi,namei) -> case tyi of {ArrayType{} -> return [];_ -> impFromTy tyi}) args >>= \qsvByVal ->
  concatMapM (\(_,tyi,namei) -> minmaxFromTy tyi) args >>= \qsvByRef ->
    return (inputs,outputs,res,qsvByRef,qsvByVal)

--used in DeclArray rule
--appends a counter to the label: label corresponding to dimension 1, dim 2,...
genLabelArr:: (Maybe Label) -> Int -> QLabel
genLabelArr (Just lbl) cnt = lbl:['D':show cnt]
genLabelArr Nothing cnt = error $ "no label for array declaration: type annotation process not done??"

-------Equate types -> Formula------------
--generates equality constraints from ty1 and ty2
--resulting size variables from ty1 (ty2) are primed/unprimed depending on pORu1 (pORu2)
--verifies that ty1 and ty2 have the same underlying type
--the error could be more informative if sameBaseTy is moved to place from where equate is called
equate:: (AnnoType,AnnoType) -> (PorU,PorU) -> FS (Maybe Formula)
equate (ty1,ty2) (pORu1,pORu2) = 
  if (sameBaseTy ty1 ty2) then
    (if (pORu1==Primed) then primeThisTy ty1 else unprimeThisTy ty1) >>= \pORuTy1 ->
    (if (pORu2==Primed) then primeThisTy ty2 else unprimeThisTy ty2) >>= \pORuTy2 ->
    if (length pORuTy1 /= length pORuTy2) then return Nothing
    else
      let zippedPU = zip pORuTy1 pORuTy2 in
      let eqs = map (\pair -> EqK [Coef (fst pair) 1,Coef (snd pair) (-1)]) zippedPU in
      if (null eqs) then 
        return (Just fTrue)
      else return $ Just (fAnd eqs)
  else return Nothing

--returns a primed version of all size variables from primTy
primeThisTy:: AnnoType -> FS [QSizeVar]
primeThisTy ty = 
  impFromTy ty >>= \ity ->
  nonImpFromTy ty >>= \nity ->
  return (primeTheseQSizeVars ity ++ nity)
--returns an unprimed version of all size variables from primTy
unprimeThisTy:: AnnoType -> FS [QSizeVar]
unprimeThisTy ty = 
  sizeVarsFromAnnTy ty >>= \svs -> 
  return $ map (\s -> (s,Unprimed)) svs

----To do: simplify true
invFromTyEnv:: TypeEnv -> FS Formula
invFromTyEnv tenv = 
  mapM (\(v,ty) -> invFromTy ty) tenv >>= \fs ->
  return (fAnd fs)

invFromTy:: AnnoType -> FS Formula
invFromTy ty = 
  isIndirectionArrTy ty >>= \isIndir ->
  impFromTy ty >>= \tys ->
  let noX = noChange tys in
  let initp = case ty of
        PrimBool{anno=Just a} ->
          let qb = (SizeVar a,Unprimed) in
            fOr [EqK [Coef qb (-1),Const 1],EqK [Coef qb 1]]
        ArrayType{elemType=eTy,indxTypes=iTys} ->
          let sGT0 s = fGT[Coef (SizeVar s,Unprimed) 1] in
          let sGT0s = map (\PrimInt{anno=Just s} -> sGT0 s) iTys in
          if isIndir then
            case anno eTy of
              Just elemAnno ->
                let min = ((ArrSizeVar elemAnno Min),Unprimed) in
                let max = ((ArrSizeVar elemAnno Max),Primed) in
                let minLTEmax = GEq [Coef max 1,Coef min (-1)] in
                  fAnd (minLTEmax:sGT0s) 
              Nothing -> error $ "indirection array without annotation ??" ++ showImpp ty
          else 
            fAnd sGT0s
        _ -> fTrue 
  in return $ (fAnd [noX,initp])

qsvFromTyEnv:: TypeEnv -> FS [QSizeVar]
qsvFromTyEnv tenv = 
  mapM (\(v,ty) -> fsvTy ty) tenv >>= \vs ->
  return (concat vs)

impFromTyEnv:: TypeEnv -> FS [QSizeVar]
impFromTyEnv tenv = 
  mapM (\(v,ty) -> impFromTy ty) tenv >>= \imps ->
  return (concat imps)

-- result: list containing imperative size variables (all but size of array)
impFromTy:: AnnoType -> FS [QSizeVar]
impFromTy ty | isPrimitiveType ty = 
  unprimeThisTy ty >>= \uty ->
  return uty
impFromTy ty@ArrayType{} =
  sizeVarsFromAnnTy ty{indxTypes=[]} >>= \svs ->
  return $ map (\s -> (s,Unprimed)) svs

-- result: list containing non-imperative size variables (size of array)
nonImpFromTy:: AnnoType -> FS [QSizeVar]
nonImpFromTy ArrayType{elemType=eTy,indxTypes=iTys} =
  let qsvIndx = map (\PrimInt{anno=Just ann} -> (SizeVar ann,Unprimed)) iTys in
  return (qsvIndx)
nonImpFromTy _ = return []

-- result: list containing min-max size variables (passed by reference)
minmaxFromTy:: AnnoType -> FS [QSizeVar]
minmaxFromTy ty | isPrimitiveType ty = return []
minmaxFromTy ArrayType{elemType=eTy,indxTypes=iTys} =
  getFlags >>= \flags ->
  if (isIndirectionIntArray flags && (sameBaseTy eTy (PrimInt{anno=Nothing}))) then
    return [(ArrSizeVar (fromJust (anno eTy)) Min,Unprimed),(ArrSizeVar (fromJust (anno eTy)) Max,Unprimed)]
  else return []

-- given [f0,f1,...] generates (f0=f0',...) but not (..f1=f1'..)
nonImpLinkedToPrim:: [AnnoType] -> FS Formula
nonImpLinkedToPrim tys = 
  mapM nonImpFromTy tys >>= \nitys ->
  let qsvNonImps = concat nitys in
  let fs = map (\(ty,Unprimed) -> EqK [Coef (ty,Unprimed) 1,Coef (ty,Primed) (-1)]) qsvNonImps in
    return (fAnd fs)

initArrFormula:: AnnoType -> AnnoType -> FS (Maybe Formula)
initArrFormula tp arrTy = 
  isIndirectionArrTy arrTy >>= \isIndir ->
  case arrTy of
    ArrayType{elemType=eTy,indxTypes=iTys} ->
      if not (sameBaseTy tp eTy) then return Nothing
      else
        impFromTy arrTy >>= \arrtys ->
        if isIndir then
          let elemBounds = arrtys in
          let primedBounds = primeTheseQSizeVars elemBounds in
          case tp of
            PrimInt{anno=Just a} ->
                let formula = fAnd $ map (\bnd -> EqK [Coef bnd (1),Coef (SizeVar a,Unprimed) (-1)]) primedBounds in
                return (Just formula)
            PrimFloat{} -> return (Just fTrue)
            _ -> return Nothing
        else 
          return $ Just (noChange arrtys)

updateMethDecl (Prog incls prims oldMeths) newm = 
  let newMeths = map (
                        \oldm -> 
                          if methName oldm == methName newm then 
                            newm 
                          else oldm
                      ) oldMeths in
    (Prog incls prims newMeths)
