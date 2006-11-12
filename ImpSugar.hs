module ImpSugar(specialize,desugarInfer,desugarChecker) where
import ImpAST
import Fresh(FS,fresh,freshVar,freshLabel)
import ImpConfig(prederivation,Prederivation(..))
import ImpTypeCommon(freshTy)
import MyPrelude
------------------------------------------
import Maybe(catMaybes)

-------Specialization--------------    
specialize:: Prog -> FS Prog
specialize prog@(Prog incls prims meths) = 
  rtt meths >>= \varsigma ->
  mapM (specializeM prog varsigma) meths >>= \newMeths ->
  return (Prog incls prims newMeths)
  where
    rtt:: [MethDecl] -> FS [QLabel]
    rtt meths = return $ concatMap methUpsis meths
  
specializeM:: Prog -> [QLabel] -> MethDecl -> FS MethDecl 
specializeM prog varsigma methDecl@MethDecl{methPres=pres, methBody=eb} =
  specializeE prog varsigma eb >>= \newEb -> 
  let newPres = dropUnsafe varsigma pres  in
  return $ methDecl{methPres=newPres,
                    methUpsis=[],
                    methBody=newEb}

dropUnsafe:: [QLabel] -> [LabelledFormula] -> [LabelledFormula]
dropUnsafe varsigma [] = []
dropUnsafe varsigma (pre:pres) = 
  let lbl = primOne (fst pre) in
    if lbl `elem` (primAll varsigma) then dropUnsafe varsigma pres
    else pre:dropUnsafe varsigma pres

primOne:: QLabel -> QLabel
primOne [] = error "inconsistent label: detected in primOne"
primOne [x] = if x=="lPost" then [] else error ("inconsistent label: detected in primOne "++ x)
primOne xs = drop (length xs - 2) xs

primAll::[QLabel] -> [QLabel]
primAll labels = map primOne labels

makeIf:: [(Exp,Exp)] -> Exp -> [Exp] -> Exp
makeIf rho exp [] = exp
makeIf rho exp (cond:conds) = 
  let substFirst = applySubstExpAll cond rho in
    If False substFirst (makeIf rho exp conds) ExpError

applySubstExpAll:: Exp -> [(Exp,Exp)] -> Exp
applySubstExpAll cond [] = cond
applySubstExpAll cond (p:pairs) = 
  let newCond = applySubstExpOne cond p in
    applySubstExpAll newCond pairs

applySubstExpOne:: Exp -> (Exp,Exp) -> Exp
applySubstExpOne cond (formal,actual) = case cond of
  LblMethCall lbl id exps ->
    let newExps = map (\e -> applySubstExpOne e (formal,actual)) exps in
      LblMethCall lbl id newExps
  AssignVar id exp -> -- <-- not checked if a variable with the same name is introduced. If so do not do newEb
    let newExp = applySubstExpOne exp (formal,actual) in
      AssignVar id newExp
  If nonDet test exp1 exp2 -> 
    let newTest = applySubstExpOne test (formal,actual) in
    let newExp1 = applySubstExpOne exp1 (formal,actual) in
    let newExp2 = applySubstExpOne exp2 (formal,actual) in
      If nonDet newTest newExp1 newExp2
  Seq exp1 exp2 ->
    let newExp1 = applySubstExpOne exp1 (formal,actual) in
    let newExp2 = applySubstExpOne exp2 (formal,actual) in
      Seq newExp1 newExp2
  ExpBlock varDecls eb ->     -- <-- not checked if a variable with the same name is introduced. If so do not do newEb
    let newEb = applySubstExpOne eb (formal,actual) in
      ExpBlock varDecls newEb
  initial_e@(ExpVar initial_lit) -> 
    let (ExpVar formalLit) = formal in
      if (formalLit == initial_lit) 
        then actual     --change
        else initial_e  --no change
  _ -> cond

specializeE:: Prog -> [QLabel] -> Exp -> FS Exp
specializeE (Prog incls prims meths) varsigma (exp@(LblMethCall (Just lblCall) id actuals)) = 
  let foundCallable = findCallable id ((map (\p -> Prim p) prims)++(map (\m -> Meth m) meths)) in
    case foundCallable of
      Nothing -> error $ "call to undefined function " ++ id ++ "\nError detected during specialization - specializeE function."
      Just (Prim p) -> 
        let formals = map (\lit -> ExpVar lit) (thd3 (unzip3 (tail $ primParams p))) in
        if (length formals /= length actuals) then
          error $ "call to function " ++ id ++ " with incompatible argument types\n "++showImppTabbed exp 1
        else
          let rho = zip formals actuals in
          let ep = catMaybes $ map (\(lblPrim,rExp) -> 
                if [lblCall,lblPrim] `elem` (primAll varsigma)
                then Just rExp
                else Nothing) (primTests p) in
            if (null ep) then return exp
            else return $ (makeIf rho exp ep)
      Just (Meth m) -> 
        if [lblCall,"lPost"] `elem` (primAll varsigma) then
            let runtimeTest = (LblMethCall (Just "l_") "runtimePost" []) in
            return (makeIf [] exp [runtimeTest])
        else return exp

-------Traverse - No Change--------
specializeE prog varsigma e = case e of 
  AssignVar id exp -> 
    specializeE prog varsigma exp >>= \newExp ->
      return $ AssignVar id newExp 
  If nonDet test exp1 exp2 ->
    specializeE prog varsigma test >>= \newTest ->
    specializeE prog varsigma exp1 >>= \newExp1 ->
    specializeE prog varsigma exp2 >>= \newExp2 ->
      return $ If nonDet newTest newExp1 newExp2
  Seq exp1 exp2 ->
    specializeE prog varsigma exp1 >>= \newExp1 ->
    specializeE prog varsigma exp2 >>= \newExp2 ->
      return $ Seq newExp1 newExp2
  ExpBlock varDecls eb ->
    mapM (specializeVD prog varsigma) varDecls >>= \newVarDecls ->
    specializeE prog varsigma eb >>= \newEb ->
    return (ExpBlock newVarDecls newEb)
  _ -> return e

specializeVD:: Prog -> [QLabel] -> VarDecl -> FS VarDecl
specializeVD prog varsigma vd = case vd of
  VarDecl ty lit exp ->
    specializeE prog varsigma exp >>= \newExp ->
      return $ VarDecl ty lit newExp
  LblArrVarDecl lbl ty indxs lit exp ->
    specializeE prog varsigma exp >>= \newExp ->
      return $ LblArrVarDecl lbl ty indxs lit newExp

-------DeSugaring------------------
-- Overloading? Because types are not available during desugaring, restrictions are needed to enable overloading for primitives:
--1. no MethDecl should have primitive names: sub,assign,plus,minus,mul,div2,eq,lt,gt,gte,lte.....and maybe others
-- how to check? for each name in MethDecl, check whether it appears in PrimDecl
--2. two MethDecl should not have the same name
-- how to check? look for duplicates in MethDecl
--3. primitives should be called with variables as arguments. For expressions, temporary variables need to be introduced,
-- and type for these is not known.
-- how to check? during desugaring, allow expToVar only for MethDecl
--------------------------------
-- Without overloading for primitives: symbols like +,-,[] cannot be used. 
-- If they are used, they can be disambiguated only after simple type checking.
desugarChecker:: Prog -> FS Prog
desugarChecker prog@(Prog incls prims meths) = 
  mapM typeAnnoChkM meths >>= \newMeths1 ->
  mapM (desugarM prog) newMeths1 >>= \newMeths2 ->
  return (Prog incls prims newMeths2)

desugarInfer:: Prog -> FS Prog
desugarInfer prog@(Prog incls prims meths) = 
  mapM typeAnnoInfM meths >>= \newMeths1 ->
  mapM (desugarM prog) newMeths1 >>= \newMeths2 ->
  return (Prog incls prims newMeths2)

desugarM:: Prog -> MethDecl -> FS MethDecl
desugarM prog m@MethDecl{methBody=eb} = 
  desugarE prog eb >>= \newEB ->
  return $ m{methBody=newEB}

-- order in which different desugaring are done IS IMPORTANT
-- sgArgIsExp introduces MultiDeclBlock <- do it before sgMultiDeclExp
desugarE:: Prog -> Exp -> FS Exp
desugarE prog e = 
  sgArgIsExp prog e >>= \e1 -> 
  sgTestIsExp e1 >>= \e2 -> 
  let e3 = sgMultiDeclExp e2 in
  return (sgFwDecl e3)

-------Label & Size Annotation-----
-- Before checking: freshes types of local variables (but not types of method arguments)
-- freshes labels (were they are not provided)
typeAnnoChkM:: MethDecl -> FS MethDecl
typeAnnoChkM m@MethDecl{methBody=eb} =
  typeAnnoChkE eb >>= \neweb ->
  return $ m{methBody=neweb}

typeAnnoChkE:: Exp -> FS Exp
typeAnnoChkE e = case e of 
  LblMethCall lbl id exps -> 
    mapM typeAnnoChkE exps >>= \newExps ->  
    case lbl of 
      Nothing -> 
        freshLabel >>= \newlbl ->
        return $ LblMethCall (Just newlbl) id newExps  
      Just oldlbl ->
        return $ LblMethCall (Just oldlbl) id newExps  
  AssignVar id exp ->
    typeAnnoChkE exp >>= \newExp ->
    return $ AssignVar id newExp
  If nonDet test exp1 exp2 ->
    typeAnnoChkE test >>= \newTest ->
    typeAnnoChkE exp1 >>= \newExp1 ->
    typeAnnoChkE exp2 >>= \newExp2 ->
    return $ If nonDet newTest newExp1 newExp2
  Seq exp1 exp2 -> 
    typeAnnoChkE exp1 >>= \newExp1 ->
    typeAnnoChkE exp2 >>= \newExp2 ->
    return $ Seq newExp1 newExp2
  ExpBlock varDecls eb -> 
    mapM typeAnnoChkInDecl varDecls >>= \newVarDecls ->
    typeAnnoChkE eb >>= \newEb ->
    return $ ExpBlock newVarDecls newEb
  _ -> return $ e

typeAnnoChkInDecl:: VarDecl -> FS VarDecl
typeAnnoChkInDecl varDecl = 
  case varDecl of
    VarDecl ty lit exp -> 
      freshTy ty >>= \newTy ->
      typeAnnoChkE exp >>= \newExp ->
      return $ VarDecl newTy lit newExp
    LblArrVarDecl lbl ty indxs lit exp -> 
      freshTy ty >>= \newTy ->
      typeAnnoChkE exp >>= \newExp ->
      case lbl of
        Nothing ->
          freshLabel >>= \newlbl ->
          return $ LblArrVarDecl (Just newlbl) newTy indxs lit newExp
        Just oldlbl ->
          return $ LblArrVarDecl (Just oldlbl) newTy indxs lit newExp

-- Before inference: freshes types of local variables AND types of method arguments
-- freshes labels (EVEN if they are provided)
typeAnnoInfM:: MethDecl -> FS MethDecl
typeAnnoInfM m@MethDecl{methParams=params,methBody=eb} =
  let (refs,tys,names) = unzip3 params in
    mapM freshTy tys >>= \newtys -> 
    typeAnnoInfE eb >>= \neweb ->
    return $ m{methParams=(zip3 refs newtys names),methBody=neweb}

typeAnnoInfE:: Exp -> FS Exp
typeAnnoInfE e = case e of 
  LblMethCall lbl id exps -> 
    mapM typeAnnoInfE exps >>= \newExps ->  
    freshLabel >>= \newlbl ->
    return $ LblMethCall (Just newlbl) id newExps  
  AssignVar id exp ->
    typeAnnoInfE exp >>= \newExp ->
    return $ AssignVar id newExp
  If nonDet test exp1 exp2 ->
    typeAnnoInfE test >>= \newTest ->
    typeAnnoInfE exp1 >>= \newExp1 ->
    typeAnnoInfE exp2 >>= \newExp2 ->
    return $ If nonDet newTest newExp1 newExp2
  Seq exp1 exp2 -> 
    typeAnnoInfE exp1 >>= \newExp1 ->
    typeAnnoInfE exp2 >>= \newExp2 ->
    return $ Seq newExp1 newExp2
  ExpBlock varDecls eb -> 
    mapM typeAnnoInfInDecl varDecls >>= \newVarDecls ->
    typeAnnoInfE eb >>= \newEb ->
    return $ ExpBlock newVarDecls newEb
  _ -> return $ e

typeAnnoInfInDecl:: VarDecl -> FS VarDecl
typeAnnoInfInDecl varDecl = 
  case varDecl of
    VarDecl ty lit exp -> 
      freshTy ty >>= \newTy ->
      typeAnnoInfE exp >>= \newExp ->
      return $ VarDecl newTy lit newExp
    LblArrVarDecl lbl ty indxs lit exp -> 
      freshTy ty >>= \newTy ->
      typeAnnoInfE exp >>= \newExp ->
      freshLabel >>= \newlbl ->
      return $ LblArrVarDecl (Just newlbl) newTy indxs lit newExp

-------MultiDecl-------------------
sgMultiDeclExp:: Exp -> Exp
sgMultiDeclExp (ExpBlock [] exp) = ExpBlock [] (sgMultiDeclExp exp)
sgMultiDeclExp (ExpBlock [varDecl] exp) = 
  let newVarDecl = sgMultiDeclExpInDecl varDecl in
    ExpBlock [newVarDecl] (sgMultiDeclExp exp)
sgMultiDeclExp (ExpBlock (varDecl:rest) exp) = 
  let newVarDecl = sgMultiDeclExpInDecl varDecl in
    ExpBlock [newVarDecl] (sgMultiDeclExp (ExpBlock rest exp))

-------Traverse - No change--------
sgMultiDeclExp e = case e of
  If nonDet ident exp1 exp2 -> If nonDet ident (sgMultiDeclExp exp1) (sgMultiDeclExp exp2)
  Seq exp1 exp2 -> Seq (sgMultiDeclExp exp1) (sgMultiDeclExp exp2)
  AssignVar id exp -> AssignVar id (sgMultiDeclExp exp)
--  LblMethCall _ _ _ -> arguments should not be expression. sgArgIsExp has been done
  _ -> e
  
sgMultiDeclExpInDecl::VarDecl -> VarDecl
sgMultiDeclExpInDecl varDecl = case varDecl of
  VarDecl primTy lit exp -> VarDecl primTy lit (sgMultiDeclExp exp)
  LblArrVarDecl lbl ty indxs lit exp -> LblArrVarDecl lbl ty indxs lit (sgMultiDeclExp exp)

-------Sequence VarDeclarations----
sgFwDecl:: Exp -> Exp
sgFwDecl e = 
  let (e',vds) = sgFwDeclInExp e in
    seqVds vds e'

sgFwDeclInExp:: Exp -> (Exp,[VarDecl])
sgFwDeclInExp (Seq e1 e2) =
  let (e1',vds1) = sgFwDeclInExp e1 in
  let (e2',vds2) = sgFwDeclInExp e2 in
    (Seq (seqVds vds1 e1') (seqVds vds2 e2'),[])
sgFwDeclInExp (If nonDet v e1 e2) = --assumes v is a simple expression
  let (e1',vds1) = sgFwDeclInExp e1 in
  let (e2',vds2) = sgFwDeclInExp e2 in
    (If nonDet v (seqVds vds1 e1') (seqVds vds2 e2'),[])
sgFwDeclInExp (AssignVar v (If nonDet vCond eThen eElse)) = 
  error "sgFwDeclInExp: initializer for VarDecl is a conditional. Causes code duplication.\nNot Implemented (yet) because C does not allow this."
sgFwDeclInExp (AssignVar v e) =
  let (e',vds) = sgFwDeclInExp e in
    (AssignVar v e',vds)
sgFwDeclInExp (ExpBlock [] e) =
  let (e',vds) = sgFwDeclInExp e in
    (e',vds)
sgFwDeclInExp (eb@(ExpBlock [VarDecl ty v (If nonDet vCond eThen eElse)] e2)) =
  error "sgFwDeclInExp: initializer for VarDecl is a conditional. Causes code duplication.\nNot Implemented (yet) because C does not allow this."
sgFwDeclInExp (eb@(ExpBlock [VarDecl ty v e1] e2)) =
  let (e1',vds1) = sgFwDeclInExp e1 in
  let (e2',vds2) = sgFwDeclInExp e2 in
    (e2',vds1++[(VarDecl ty v e1')]++vds2)

sgFwDeclInExp (eb@(ExpBlock [LblArrVarDecl lbl ty indxs v (If nonDet vCond eThen eElse)] e2)) =
  error "sgFwDeclInExp: initializer for VarDecl is a conditional. Causes code duplication.\nNot Implemented (yet) because C does not allow this."
sgFwDeclInExp (eb@(ExpBlock [LblArrVarDecl lbl ty indxs v e1] e2)) =
  let (e1',vds1) = sgFwDeclInExp e1 in
  let (e2',vds2) = sgFwDeclInExp e2 in
    (e2',((LblArrVarDecl lbl ty indxs v e1'):vds1)++vds2)
  
sgFwDeclInExp (eb@(ExpBlock vDecls e)) = error $ "assertion failed: moving forward vDecls through a MultiDecl block:\n " ++ showImppTabbed eb 1
sgFwDeclInExp e = (e,[]) --assumes that args of functions are simple expressions

-- given a list of n VarDecl, it creates n nested ExpBlock
seqVds:: [VarDecl] -> Exp -> Exp
seqVds [] e = e
seqVds (vd:vds) e = ExpBlock [vd] (seqVds vds e)

-------TestExp -> TestVar----------
sgTestIsExp:: Exp -> FS Exp
sgTestIsExp (If nonDet (ExpVar e) exp1 exp2) = 
  sgTestIsExp exp1 >>= \newExp1 ->
  sgTestIsExp exp2 >>= \newExp2 ->
  return $ If nonDet (ExpVar e) newExp1 newExp2

sgTestIsExp (If nonDet test exp1 exp2) = 
  fresh >>= \fshAnn ->
  freshVar >>= \fshV -> 
    sgTestIsExp exp1 >>= \newExp1 ->
    sgTestIsExp exp2 >>= \newExp2 ->
    let varDecl = VarDecl (PrimBool{anno=Just fshAnn}) fshV test in
    let newTest = ExpVar fshV in
      return $ ExpBlock [varDecl] (If nonDet newTest newExp1 newExp2)

-------Traverse - No Change--------
sgTestIsExp e = 
  case e of
    ExpBlock varDecls eb -> 
      sgTestIsExp eb >>= \newEB ->
      mapM sgTestIsExpInDecl varDecls >>= \newVarDecls ->
      return $ ExpBlock newVarDecls (newEB)
    Seq exp1 exp2 -> 
      sgTestIsExp exp1 >>= \newExp1 ->
      sgTestIsExp exp2 >>= \newExp2 ->
      return $ Seq newExp1 newExp2
    AssignVar id exp -> 
      sgTestIsExp exp >>= \newExp ->
      return $ AssignVar id newExp
    LblMethCall lbl id args -> 
      mapM sgTestIsExp args >>= \newExps ->
      return $ LblMethCall lbl id newExps
    _ -> return $ e

sgTestIsExpInDecl:: VarDecl -> FS VarDecl
sgTestIsExpInDecl varDecl = case varDecl of   
  VarDecl ty lit exp -> 
    sgTestIsExp exp >>= \newExp -> 
    return $ VarDecl ty lit newExp
  LblArrVarDecl lbl ty indxs lit exp -> 
    sgTestIsExp exp >>= \newExp -> 
    return $ LblArrVarDecl lbl ty indxs lit newExp

-------ArgExp -> ArgVar------------
getTypes:: Prog -> Lit -> Int -> FS [AnnoType]
-- ignore first type - which is the type of the function
getTypes (Prog incls prims meths) fName noArgs =
  let callables = map (\p -> Prim p) prims ++ map (\m -> Meth m) meths in
  let foundCallable = findCallable fName callables in
  let idTys = case foundCallable of
        Nothing -> error $ "call to undefined function " ++ show fName ++ "\nError detected during desugaring - getTypes function"
        Just (Meth m) -> methParams m
        Just (Prim p) -> primParams p in
  let argTys = tail (snd3 (unzip3 idTys)) in -- at least one argument: function type
  return argTys

sgExpToVarDecl:: (AnnoType,Exp) -> FS (Maybe VarDecl,Exp)
sgExpToVarDecl (ty,exp) = 
  case exp of 
    (ExpVar lit) -> return (Nothing,exp) -- input is already variable - no varDecl needed
    _ -> 
      freshTy ty >>= \fshTy ->
      freshVar >>= \fshV ->
      let decl = case fshTy of {
            ArrayType{} -> error $ "while desugaring found expression of Array type given as function argument:\n " ++ showImppTabbed exp 1;
            _ -> VarDecl fshTy fshV exp
      } in
      return $ (Just decl,ExpVar fshV)

sgArgIsExp:: Prog -> Exp -> FS Exp
sgArgIsExp prog (LblMethCall lbl id args) = 
  getTypes prog id (length args) >>= \tys ->
  mapM sgExpToVarDecl (zip tys args) >>= \new ->  
    let (maybeVarDecls,newVars) = unzip new in
      let varDecls = catMaybes maybeVarDecls in
      if (null varDecls) then return $ LblMethCall lbl id newVars
      else
        mapM (sgArgIsExpInDecl prog) varDecls >>= \newVarDecls ->
        return $ ExpBlock newVarDecls (LblMethCall lbl id newVars)

-------Traverse - No Change--------
sgArgIsExp prog e =
  case e of
    ExpBlock varDecls eb -> 
      mapM (sgArgIsExpInDecl prog) varDecls >>= \newVarDecls ->
      sgArgIsExp prog eb >>= \newEB ->
        return $ ExpBlock newVarDecls (newEB)
    Seq exp1 exp2 ->
      sgArgIsExp prog exp1 >>= \newExp1 ->
      sgArgIsExp prog exp2 >>= \newExp2 ->
        return $ Seq newExp1 newExp2
    If nonDet test exp1 exp2 ->
      sgArgIsExp prog test >>= \newTest ->
      sgArgIsExp prog exp1 >>= \newExp1 ->
      sgArgIsExp prog exp2 >>= \newExp2 ->
        return $ If nonDet newTest newExp1 newExp2
    AssignVar id exp ->
      sgArgIsExp prog exp >>= \newExp ->
          return $ AssignVar id newExp
    _ -> return $ e

sgArgIsExpInDecl:: Prog -> VarDecl -> FS VarDecl
sgArgIsExpInDecl prog varDecl = case varDecl of
  VarDecl ty lit exp -> 
    sgArgIsExp prog exp >>= \newExp ->
      return $ VarDecl ty lit newExp
  LblArrVarDecl lbl ty indxs lit exp -> 
    sgArgIsExp prog exp >>= \newExp ->
      return $ LblArrVarDecl lbl ty indxs lit newExp


 