module ImpAST where
import Fresh(getFlags,FS(..))
import ImpConfig(isIndirectionIntArray,outputFile)
import List(nub,(\\))
import MyPrelude
import System.IO.Unsafe(unsafePerformIO)
------------------------------------------
import List(union)

-------AST-------------------------
data Prog = Prog [String] [PrimDecl] [MethDecl]

data PrimDecl = PrimDecl {
-- Arguments, Postcondition, PreconditionS, Runtime-testS
  primParams:: [(PassBy,AnnoType,Lit)],
  primPost:: Formula,
  primPres:: [LabelledFormula],
  primTests:: [LabelledExp]
}
primName:: PrimDecl -> Lit
primName p = thd3 (head (primParams p))

data MethDecl = MethDecl {
-- Arguments, Postcondition, PreconditionS, Runtime-checkS, Invariant, Body
  methParams:: [(PassBy,AnnoType,Lit)],
  methPost:: [Formula],
  methPres:: [LabelledFormula],
  methUpsis:: [QLabel],
  methInv:: Formula,
  methOut:: Outcomes, --length methOut == 2, ["OK", "ERR"]
  methErrs:: [LabelledFormula],
  methOutBugs:: [LabelledFormula], --length methOutBugs == 3, ["NEVER_BUG","MUST_BUG","MAY_BUG"]
  methBody:: Exp
}
methName:: MethDecl -> Lit 
methName m = thd3 (head (methParams m))

type LabelledFormula = (QLabel,Formula) --precondition
type LabelledExp = (Label,Exp) --runtime test
type Label = String
type QLabel = [Label]
-------Find Method-----------------
data Callable = Prim PrimDecl
  | Meth MethDecl
  
data PassBy = PassByRef | PassByVal deriving (Show,Eq)

type Outcomes = [Outcome]
data Outcome = OK Formula | ERR Formula
getOKOutcome [OK f1, ERR f2] = f1
getERROutcome [OK f1, ERR f2] = f2

-- Types for 3Contexts version
type Formulae = [Formula]
triple:: a -> [a]
triple = replicate 3
strong::Formulae -> Formula
strong = head
weak::Formulae -> Formula
weak (x:xs) = head xs
cond::Formulae -> Formula
cond (x1:x2:xs) = head xs
-- Types for 3Contexts version

-- list of [MethOrPrim] is assumed not to contain duplicates (same criteria of equality)
findCallable:: Lit -> [Callable] -> Maybe Callable
findCallable lit [] = Nothing

findCallable fName (c:cs) =
  case c of
    Meth m ->
      if methName m == fName then 
        Just c 
      else findCallable fName cs
    Prim p ->
      if primName p == fName then 
        Just c 
      else findCallable fName cs

-- requires:: mn method should be defined in Prog (findMethod cannot fail)
findMethod:: Lit -> Prog -> MethDecl
findMethod mn (Prog _ prims meths) = findMethod1 mn meths where
  findMethod1 mn (m:ms) | methName m == mn = m
  findMethod1 mn (m:ms) | methName m /= mn = findMethod1 mn ms

-------Annotated Types-------------
data AnnoType = PrimInt {anno:: Maybe Anno}
  | PrimVoid {anno:: Maybe Anno}
  | PrimBool {anno:: Maybe Anno}
  | PrimFloat {anno:: Maybe Anno}
  | ArrayType {elemType::AnnoType, indxTypes::[AnnoType]}
  | TopType {anno:: Maybe Anno}

type Anno = String
-----------------------------------
isPrimitiveType:: AnnoType -> Bool
isPrimitiveType PrimBool{} = True
isPrimitiveType PrimFloat{} = True
isPrimitiveType PrimInt{} = True
isPrimitiveType PrimVoid{} = True
isPrimitiveType TopType{} = error "isPrimitiveType: argument must not be TopType"
isPrimitiveType _ = False

isIndirectionArrTy:: AnnoType -> FS Bool
isIndirectionArrTy ArrayType{elemType=PrimInt{}} = 
  getFlags >>= \flags ->
  return (isIndirectionIntArray flags)
isIndirectionArrTy _ = return False
-------Exp-------------------------
data Exp = KTrue
  | KFalse
  | KVoid
  | KIntNum Int
  | KFloatNum Float
  | ExpVar Lit
  | If Bool Exp Exp Exp -- the Bool flag: is the conditional nonDet
  | LblMethCall (Maybe Label) Lit [Exp]
  | AssignVar Lit Exp
  | Seq Exp Exp
  | ExpBlock [VarDecl] Exp
  | ExpError
  | ExpBogus  --used for variable declaration without initialization
  | While Exp Exp
  | For Exp Exp Exp Exp
--  | Plus Exp Exp | Minus Exp Exp | Mul Exp Exp | Div Exp Exp
--  | ExpGT Exp Exp | ExpGTE Exp Exp | ExpLT Exp Exp | ExpLTE Exp Exp | ExpEq Exp Exp
--  | AssignArr Lit [Exp] Exp | SubArr Lit [Exp]

data VarDecl = VarDecl AnnoType Lit Exp
--  | PrimVarDecl AnnoType Lit Exp
--  | ArrVarDecl AnnoType Lit Exp -- To be implemented later!!
  | LblArrVarDecl (Maybe Label) AnnoType [Exp] Lit Exp

type Lit=String
-------Formula---------------------
data CAbst = CAbst Lit [QSizeVar] Formula
data RecPost = RecPost Lit [QSizeVar] Formula ([QSizeVar],[QSizeVar],[QSizeVar])
-- RecPost represents a Const-Abstraction with: name arguments formula (inputs,outputs,imperByValue)
-- typeInv: (arguments = inputs+outputs)
-- meaning: (fExists (primeTheseSizeVars imperByValue) formula) && noChange(imperByValue)

type Relation = ([QSizeVar],[QSizeVar],Formula)
data Formula = And [Formula]
  | Or [Formula]
  | Not Formula
  | Exists [QSizeVar] Formula
  | GEq [Update]
  | EqK [Update] --EqK instead of Eq: be careful to check some Updates to be positive, others to be negative
  | AppRecPost Lit [QSizeVar]
  | QLabelSubst [(QSizeVar,QSizeVar)] QLabel
-- deprecated Constructors: do not use them anymore
  | Forall [QSizeVar] Formula
  | AppCAbst Lit [QSizeVar] [QSizeVar]
  | Union [Formula]
  | FormulaBogus
  deriving Eq

data Update = Const Int
  | Coef QSizeVar Int
  deriving Eq

-------SizeVar---------------------
type QSizeVar = (SizeVar,PorU) 
data SizeVar = SizeVar Anno
  | ArrSizeVar Anno MorM
  deriving Eq
data PorU= Primed
  | Unprimed
  | Recursive
  deriving Eq
data MorM = Min | Max 
  deriving (Eq)

-------Canonical Formula-----------
fTrue::Formula
fTrue = EqK [Const 0]

fFalse::Formula
fFalse = EqK [Const 1]

fAnd:: [Formula] -> Formula
fAnd fs = 
  if (null fs) then fTrue -- error $ "And formula without any clauses -- should I return True?"
  else if (singleton fs) then head fs else And fs

fOr:: [Formula] -> Formula
fOr fs = 
  if (null fs) then fFalse -- error $ "Or formula without any clauses - should I return False?"
  else if (singleton fs) then head fs else Or fs

fNot:: Formula -> Formula
fNot f = Not f

fExists:: [QSizeVar] -> Formula -> Formula
fExists vs f = if (null vs) then f 
  else (Exists vs f)

fForall:: [QSizeVar] -> Formula -> Formula
fForall vs f = if (null vs) then f else (Forall vs f)  

fGT:: [Update] -> Formula
fGT ups = GEq (Const (-1):ups)

-------Selectors from Formulae------------
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
  QLabelSubst subst lbls -> snd (unzip subst)
  _ -> error ("fqsv: unexpected argument: " ++ show f)

fqsvU:: [Update] -> [QSizeVar]
fqsvU [] = []
fqsvU (up:ups) = 
  let rest=fqsvU ups in 
    case up of
      Const int -> rest
      Coef qsv int -> qsv:rest  -- << Diferent from sizeVarsFromUpdates
-------Show Prog-------------------
--Problematic !!
-- multi-dimensional arrays as function arguments: all sizes (but the last) must be filled - with what??
-- test in conditional, init value in varDecl, arguments of function and rhs of assign must be proper expressions (no varDecl, if, seq)
      
tabs:: Int -> String
tabs x = replicate x ' '

--showC - C code (as close as possible)
class ShowC a where
  showC:: a -> String
  showC a = showCTabbedRet a (False,"") 0
  -- showCTabbed with "return" or without (inserting only ;)
  showCTabbedRet:: a -> (Bool,String) -> Int -> String
  showCTabbedRet a (b,pre) cnt = showC a

instance ShowC Prog where
  showC (Prog inclFilenames prims meths) = showPreludeC inclFilenames ++ concatMap showC meths

showPreludeC:: [String] -> String
showPreludeC _ = "#include \"Primitives.h\"\n\n"

instance ShowC MethDecl where
  showC m =
    let ((_,t,fname):args) = methParams m in
    let strArgs = concatArgsC args in
      showC t ++ " " ++ fname ++ "(" ++ strArgs ++ ")" ++ showExpAsBlockC (methBody m) (True,"return ") 1 ++ "\n\n"

concatArgsC:: [(PassBy,AnnoType,Lit)] -> String
concatArgsC [] = ""
concatArgsC [(_,ty,arg)] = showC ty ++ " " ++ arg
concatArgsC ((_,ty,arg):strs) = showC ty ++ " " ++ arg ++ "," ++ concatArgsC strs

instance ShowC AnnoType where
  showC ty = 
    case ty of
      PrimBool{} -> "bool"
      PrimFloat{} -> "float"
      PrimInt{} -> "int"
      PrimVoid{} -> "void"
      ArrayType{elemType=PrimInt{}} -> 
            case length (indxTypes ty) of
              1 -> "arr"
              2 -> "arr2"
      ArrayType{elemType=PrimFloat{}} -> 
            case length (indxTypes ty) of
              1 -> "arrF"
              2 -> "arrF2"
      ArrayType{} -> "no_C_type" --no C counterpart yet

instance ShowC Exp where
  showCTabbedRet e (addRet@(b,pre)) cnt = 
    case e of
      KTrue -> if b then pre ++ "TRUE" else "TRUE"
      KFalse -> if b then pre ++ "FALSE" else "FALSE"
      KIntNum i -> if b then pre ++ show i else show i
      KFloatNum f -> if b then pre ++ show f else show f
      KVoid -> if b then pre else ";"
      ExpError -> "printf(\"ABC failed.\\n\");exit(1)"
      ExpBogus -> "NO INITIALIZATION"
      ExpVar id -> if b then pre ++ id else id
      AssignVar id exp -> id ++ "=" ++ showCTabbedRet exp addRet cnt
      LblMethCall lbl id args -> 
        let call = id ++ "(" ++ concatSepByComma (map (\arg -> showCTabbedRet arg (False,"") cnt) args) ++ ")" in
        if b then pre++call else call
      ExpBlock _ _ -> showExpAsBlockC e addRet cnt
      If _ test exp1 exp2 -> 
        "if (" ++ showCTabbedRet test (False,"") cnt ++ ")" ++ showExpAsBlockC exp1 addRet (cnt+1) ++
        " else" ++ showExpAsBlockC exp2 addRet (cnt+1)
      Seq exp1 exp2 -> showCTabbedRet exp1 (False,"") cnt ++ ";\n" ++ tabs cnt ++ showCTabbedRet exp2 addRet cnt
      
showExpAsBlockC:: Exp -> (Bool,String) -> Int -> String
showExpAsBlockC e addRet cnt = 
  case e of
    ExpBlock varDecls eb -> " {\n" ++ tabs cnt ++ concatMap (\vd -> showCTabbedRet vd (False,"") cnt) varDecls ++ 
      showBlockAsExpC eb addRet (cnt+1) ++ tabs cnt ++ "}"
    _ -> " {\n" ++ tabs cnt ++ showCTabbedRet e addRet cnt ++ ";\n" ++ tabs cnt ++ "}"

showBlockAsExpC:: Exp -> (Bool,String) -> Int -> String
showBlockAsExpC e addRet cnt =
  case e of
    ExpBlock varDecls eb -> concatMap (\vd -> showCTabbedRet vd (False,"") cnt) varDecls ++ showBlockAsExpC eb addRet cnt
    _ -> showCTabbedRet e addRet cnt ++ ";\n"

instance ShowC VarDecl where
  showCTabbedRet vd addRet cnt = 
    case vd of
      VarDecl ty lit exp -> 
        case exp of
          If _ e1 e2 e3 -> 
            showC ty ++ " " ++ lit ++ "; " ++
            showCTabbedRet exp (True,lit++" = ") (cnt+1) ++ ";\n" ++ tabs cnt          
          _ -> 
            showC ty ++ " " ++ lit ++ " = " ++ showCTabbedRet exp addRet (cnt+1) ++ ";\n" ++ tabs cnt
      LblArrVarDecl (Just lbl) ty@(ArrayType {elemType=eType,indxTypes=iTypes}) indxs lit exp -> 
        case exp of
          If _ e1 e2 e3 -> error $ "array initialized with if: the C code will not compile. Better desugar Imp code."
          _ ->
            let dim1 = showCTabbedRet (indxs!!0) (False,"") (cnt+1) in
            let (call,dims) =  case (eType,length iTypes) of {
                    (PrimInt{},1) -> ("_initArr",dim1);
                    (PrimFloat{},1) -> ("_initArrF",dim1);
                    (PrimInt{},2) -> ("_initArr2",dim1++","++showCTabbedRet (indxs!!1) addRet (cnt+1));
                    (PrimFloat{},2) -> ("_initArrF2",dim1++","++showCTabbedRet (indxs!!1) addRet (cnt+1));
                    (PrimVoid{},1) -> ("_initArrV",dim1);
                    (PrimBool{},1) -> ("_initArrB",dim1)} in
              showC ty ++ " " ++ lit ++ "; " ++ call ++ "(&" ++ 
              showCTabbedRet (ExpVar lit) addRet (cnt+1) ++ "," ++ 
              showCTabbedRet exp addRet (cnt+1) ++ "," ++ 
              dims ++ ");\n" ++ tabs cnt --only one or two dimensions!!


--showImpp - with type annotations, labels, post and pres - should be Imp+
--invariant is not shown
class ShowImpp a where
  showImpp:: a -> String
  showImpp a = showImppTabbed a 0
  showImppPre:: a -> String
  showImppPre a = ""
  showImppUpsis:: a -> (String,Int)
  showImppUpsis a = ("",0)
  showImppTabbed:: a -> Int -> String
  showImppTabbed a cnt = showImpp a
  concatSepByCommaImpp:: [a] -> String
  concatSepByCommaImpp []  = ""
  concatSepByCommaImpp [p] = showImpp p
  concatSepByCommaImpp (p:prims) = showImpp p++","++concatSepByCommaImpp prims

--'f' is added in front of size variables in types and in formaule: f_0 -> ff_0
prefixVar = 'f'

instance ShowImpp Prog where
  showImpp (Prog inclFilenames prims meths) = showPreludeImpp inclFilenames ++ concatMap showImpp meths
  showImppPre (Prog inclFilenames prims meths) = concatMap showImppPre meths
  showImppUpsis (Prog inclFilenames prims meths) = 
    let (upsis,nos) = unzip (map showImppUpsis meths) in
      (concat upsis,sum nos)

showPreludeImpp:: [String] -> String
showPreludeImpp [] = ""
showPreludeImpp [inclFilename] = "#include \"" ++ inclFilename ++ "\"\n\n"
showPreludeImpp (i:inclFilenames) = showPreludeImpp [i] ++ showPreludeImpp inclFilenames

instance ShowImpp MethDecl where
  showImpp m = 
    let ((passby,t,fname):args) = methParams m in
    let passbyStr = if passby==PassByRef then "ref " else "" in
    let strArgs = concatArgs args in
      "{-\nOK:="++showSet (fqsv (getOKOutcome (methOut m)),getOKOutcome (methOut m)) ++ "\n" ++
      "individualERRs:={"++showImpp (methErrs m)++"}\n"++
      "ERR:="++showSet (fqsv (getERROutcome (methOut m)),getERROutcome (methOut m)) ++ "\n" ++
--      "NEVER_BUG:="++showSet (fqsv (snd((methOutBugs m)!!0)),snd((methOutBugs m)!!0)) ++ "\n" ++
--      "MUST_BUG:="++showSet (fqsv (snd((methOutBugs m)!!1)),snd((methOutBugs m)!!1)) ++ "\n" ++
--      "MAY_BUG:="++showSet (fqsv (snd((methOutBugs m)!!2)),snd((methOutBugs m)!!2)) ++ "\n-}\n" ++
      passbyStr ++ showImpp t ++ " " ++ fname ++ "(" ++ strArgs ++ ")\n  where\n  (" ++ 
      showImpp (strong $ methPost m) ++ 
--      "),\n  (" ++ showImpp (weak $ methPost m) ++ "),\n  (" ++ showImpp (cond $ methPost m) ++ 
      "),\n  {" ++ showImpp (methPres m) ++ "},\n  {" ++ showUpsisImpp (methUpsis m) ++ 
      "},\n{" ++ showImppTabbed (methBody m) 1 ++ "}\n\n"
  showImppPre m = 
    let pres = methPres m in
      if length pres == 0 then ""
      else "{" ++ showImpp(methPres m) ++ "}"
  showImppUpsis m = 
    let upsis = methUpsis m in
      if length upsis == 0 then ("",0)
      else 
        let upsis = methUpsis m in
        let no = length upsis in
          ("{" ++ (methName m ++ ": " ++ concatSepByComma (map concatLabels upsis)) ++ "}",no)

instance ShowImpp PrimDecl where
  showImpp p = 
    let ((_,t,fname):args) = primParams p in
    let strArgs = concatArgs args in
      showImpp t ++ " " ++ fname ++ "(" ++ strArgs ++ ")\n  where\n  (" ++ 
      showImpp (primPost p) ++ "),\n  {" ++ 
      showImpp (primPres p) ++ "},\n  {" ++ showTestsImpp (primTests p) ++ 
      "},\n  (" ++ show fTrue ++ "),\n\n"

concatArgs:: [(PassBy,AnnoType,Lit)] -> String
concatArgs [] = ""
concatArgs [(passby,ty,arg)] = 
  let passbyStr = if passby==PassByRef then "ref " else "" in
    passbyStr ++ showImpp ty ++ " " ++ arg
concatArgs ((passby,ty,arg):strs) = 
  let passbyStr = if passby==PassByRef then "ref " else "" in
    passbyStr ++ showImpp ty ++ " " ++ arg ++ "," ++ concatArgs strs

instance ShowImpp AnnoType where
  showImpp ty = 
    case ty of
      PrimBool{anno=Just a} -> "Bool" ++ "<" ++ a++[prefixVar] ++ ">"
      PrimBool{anno=Nothing} -> "Bool"
      PrimFloat{anno=Just a} -> "Float" ++ "<" ++ a++[prefixVar] ++ ">"
      PrimFloat{anno=Nothing} -> "Float"
      PrimInt{anno=Just a} -> "Int" ++ "<" ++ a++[prefixVar] ++ ">"
      PrimInt{anno=Nothing} -> "Int"
      PrimVoid{anno=Just a} -> "Void" ++ "<" ++ a++[prefixVar] ++ ">"
      PrimVoid{anno=Nothing} -> "Void"
      ArrayType{} -> 
        showImpp (elemType ty) ++ 
        "[" ++ concatSepByCommaImpp (indxTypes ty) ++ "]"
    
showTy:: AnnoType -> String
showTy ty =
  case ty of
    PrimBool{} -> "Bool"
    PrimFloat{} -> "Float"
    PrimInt{} -> "Int"
    PrimVoid{} -> "Void"
    ArrayType{elemType=eTy,indxTypes=iTys} -> 
--      showTy eTy ++ "[" ++ (concatMap showTy iTys) ++ "]"
      showTy eTy ++ "[" ++ (concatSepByComma (map showTy iTys)) ++ "]"

instance ShowImpp [LabelledFormula] where
  showImpp [] = ""
  showImpp [(lbl,pre)] = concatLabels lbl ++ ":(" ++ showImpp pre ++ ")"
  showImpp (pre:pres) = showImpp [pre] ++ "," ++ showImpp pres

concatLabels:: [Label] -> String
concatLabels [] = ""
concatLabels [l] = l
concatLabels (l:ls) = l ++ "." ++ concatLabels ls

showUpsisImpp:: [QLabel] -> String
showUpsisImpp [] = ""
showUpsisImpp [u] = concatLabels u
showUpsisImpp (u:upsis) = showUpsisImpp [u] ++ "," ++ showUpsisImpp upsis
--showUpsisImpp upsis = error "Upsis should be empty after specialization (before type checking) !!" ++ show upsis

showTestsImpp:: [LabelledExp] -> String
showTestsImpp [] = ""
showTestsImpp ((lbl,exp):rest) = 
  lbl ++ ":" ++ showImppTabbed exp 1 ++ "," ++ showTestsImpp rest

instance ShowImpp Exp where
  showImppTabbed e cnt =
    case e of
      KTrue -> "True"
      KFalse -> "False"
      KIntNum i -> show i
      KFloatNum f -> show f
      KVoid -> "Void"
      ExpError -> "error"
      ExpBogus -> "NO INITIALIZATION"
      ExpVar id -> id
      AssignVar id exp -> id ++ ":=" ++ showImppTabbed exp cnt
      LblMethCall maybeLbl id args -> let lbl = case maybeLbl of {Just lbl->lbl;Nothing->"NO_LBL"} in
        lbl ++ ":" ++
        id ++ "(" ++ concatSepByComma (map (\arg -> showImppTabbed arg cnt) args) ++ ")"
      ExpBlock varDecls eb -> "{\n" ++ tabs cnt ++ concatMap (\vd -> showImppTabbed vd cnt) varDecls ++ 
        showImppTabbed eb (cnt+1) ++ "\n" ++ tabs cnt ++ "}"
      If _ test exp1 exp2 -> 
        "if " ++ showImppTabbed test cnt ++ "\n" ++ tabs cnt ++ "then { " ++ 
          showImppTabbed exp1 (cnt+1) ++ "\n"++tabs cnt++"} else { " ++ showImppTabbed exp2 (cnt+1) ++ " }"
      Seq exp1 exp2 -> showImppTabbed exp1 cnt ++ ";\n" ++ tabs cnt ++ showImppTabbed exp2 cnt
      While exp1 eb -> "while " ++ showImppTabbed exp1 cnt ++ "\n" ++ tabs cnt ++ showImppTabbed eb (cnt+1)
      For exp1 exp2 exp3 eb -> "for (" ++ showImppTabbed exp1 cnt ++ "; " ++ showImppTabbed exp2 cnt ++ "; "
        ++ showImppTabbed exp3 cnt ++ ")\n" ++ tabs cnt ++ showImppTabbed eb (cnt+1)

instance ShowImpp VarDecl where
  showImppTabbed vd cnt = 
    case vd of
      VarDecl ty lit e -> showImpp ty ++ " " ++ lit ++ " := " ++ showImppTabbed e (cnt+1) ++ ";\n" ++ tabs cnt
      LblArrVarDecl maybeLbl ty indxs lit exp -> 
        let lbl = case maybeLbl of {Nothing -> "";Just lbl -> lbl++":"} in
        lbl ++ showImpp ty ++ "[" ++ concatSepByCommaImpp indxs ++ "] " ++ lit ++ " := " ++ showImppTabbed exp (cnt+1) ++ ";\n" ++ tabs cnt

instance ShowImpp [Outcome] where
  showImpp [ok,err] = "{" ++ showImpp ok ++ ", " ++ showImpp err ++ "}"
instance ShowImpp Outcome where
  showImpp (OK f) = "OK: "++showImpp f
  showImpp (ERR f) = "ERR: "++showImpp f

instance ShowImpp Formula where
  showImpp (And c) = 
        let show_vec = (\fs -> 
              case fs of
                [] -> show "And--void--"
                [c] -> showImpp c
                (c:cs) -> showImpp c ++ " && " ++ show_vec cs)
        in "(" ++ show_vec c ++ ")"
  showImpp (Or c) =
        let show_vec = (\fs -> 
              case fs of
                [] -> show "Or--void--"
                [c] -> showImpp c
                (c:cs) -> showImpp c ++ " || " ++ show_vec cs)
        in "(" ++ show_vec c ++ ")"
  showImpp (Not c) = "(! " ++ showImpp c ++ ")"
  showImpp (Exists qsvs f) = "exists (" ++ concatSepByComma (map showImpp qsvs) ++ " : " ++ showImpp f ++ ")"
  showImpp (Forall qsvs f) = error $ "forall should not appear in Impp form" ++ show f
  showImpp (GEq u) = 
        let show_vec = (\fs -> 
              case fs of
     		        [] -> "GEq--void--"
    		        [u] -> showImpp u
    		        (u:us) -> showImpp u ++ " + " ++ show_vec us)
  		   in show_vec u ++ " >= 0"
  showImpp (EqK u) = 
        let show_vec = (\fs -> 
              case fs of
  		          [] -> "EqK--void--"
  		          [u] -> showImpp u
  		          (u:us) -> showImpp u ++ " + " ++ show_vec us)
  		  in show_vec u ++ " = 0" 
  showImpp f@(AppCAbst lit vars resVars) = error $ "AppCAbst should not appear in Impp form" ++ show f
  showImpp f@(AppRecPost lit insouts) = error $ "RecPost should not appear in Impp form" ++ show f
  showImpp (FormulaBogus) = "--bogus--"

instance ShowImpp Update where
  showImpp (Const i) = show i
  showImpp (Coef qsv i) =
      let (bef,aft) = if (i==1) then ("","") else if (i==(-1)) then ("(-",")") else ((show i) ++ "","") in
      bef ++ showImpp qsv ++ aft

instance ShowImpp QSizeVar where
  showImpp (sv,pORu) =
	let pu = if pORu == Primed then "PRM" else if pORu == Recursive then "REC" else "" in
	let str = case sv of
			SizeVar ann -> ann
			ArrSizeVar ann Min -> "DTm" ++ ann
			ArrSizeVar ann Max -> "DTM" ++ ann
	in (pu ++ str ++ [prefixVar])

-------Show Formula----------------
instance Show CAbst where
  show (CAbst fname ins formula) = 
    fname ++ "<" ++ concatSepByComma (map show ins) ++ "> = (" ++ show formula ++ ")"

instance Show RecPost where
  show (RecPost fname args formula (ins,outs,byVal)) = 
    fname ++ ":={[" ++ concatSepByComma (map show ins) ++ "] -> [" ++ concatSepByComma (map show outs) ++ "] -> [" ++ concatSepByComma (map show byVal) ++ "]: (" ++ show formula ++ ")};\n"
    
instance Show Formula where
    show (And c) = 
      let show_vec = (\fs -> 
            case fs of
              [] -> show "And--void--"
              [c] -> show c
              (c:cs) -> show c ++ " && " ++ show_vec cs)
      in "(" ++ show_vec c ++ ")"
    show (Or c) =
      let show_vec = (\fs -> 
            case fs of
              [] -> show "Or--void--"
              [c] -> show c
              (c:cs) -> show c ++ " || " ++ show_vec cs)
      in "(" ++ show_vec c ++ ")"
    show (Not c) = "(! " ++ show c ++ ")"
    show (Exists qsvs f) = "exists (" ++ concatSepByComma (map show qsvs) ++ " : " ++ show f ++ ")"
    show (Forall qsvs f) = "forall (" ++ concatSepByComma (map show qsvs) ++ " : " ++ show f ++ ")"
    show (GEq u) = 
      let show_vec = (\fs -> 
            case fs of
   		        [] -> "GEq--void--"
  		        [u] -> show u
  		        (u:us) -> show u ++ " + " ++ show_vec us)
		   in show_vec u ++ " >= 0"
    show (EqK u) = 
      let show_vec = (\fs -> 
            case fs of
		          [] -> "EqK--void--"
		          [u] -> show u
		          (u:us) -> show u ++ " + " ++ show_vec us)
		  in show_vec u ++ " = 0" 
    show (AppCAbst lit vars resVars) = lit ++ "(" ++ concatSepByComma (map show (vars `union` resVars)) ++ ")"
    show (AppRecPost lit insouts) = lit ++ "(" ++ concatSepByComma (map show insouts) ++ ")"
    show (FormulaBogus) = "--bogus--"
    show (QLabelSubst subst lbls) = "[" ++ concatSepByComma (map show (fst (unzip subst))) ++ "] -> ["
                                   ++ concatSepByComma (map show (snd (unzip subst))) ++ "]" ++  concatLabels lbls

instance Show Update where
    show (Const i) = show i
    show (Coef qsv i) = 
      let (bef,aft) = if (i==1) then ("","") else if (i==(-1)) then ("(-",")") else ((show i) ++ "","") in
      bef ++ show qsv ++ aft

instance Show QSizeVar where
  show (sv,pORu) = 
  	let pu = if pORu == Primed then "PRM" else if pORu == Recursive then "REC" else "" in
  	let str = case sv of
  			SizeVar ann -> ann
  			ArrSizeVar ann Min -> "DTm" ++ ann
  			ArrSizeVar ann Max -> "DTM" ++ ann
  	in (pu ++ str)

---- 2 different textual forms for QSizeVar: one from input file and the other from Omega (previously converted with show:: QSizeVar -> String)
-- from input: s,s',  s^,  s.min,s.max,s.min', s.max', s.min^, s.max^
-- from Omega: s,PRMs,RECs,DTms, DTMs, PRMDTms,PRMDTMs,RECDTms,RECDTMs
stringToQsv:: String -> QSizeVar
stringToQsv s = 
  case (take 3 s) of
    "PRM" -> case (take 3 (drop 3 s)) of
      "DTm" -> if (drop 6 s == "") then error "PRMDTm error" else (ArrSizeVar (drop 6 s) Min,Primed)
      "DTM" -> if (drop 6 s == "") then error "PRMDTM error" else (ArrSizeVar (drop 6 s) Max,Primed)
      _ -> if (drop 3 s == "") then error "PRM error" else (SizeVar (drop 3 s),Primed)
    "DTm" -> if (drop 3 s == "") then error "DTm error" else (ArrSizeVar (drop 3 s) Min,Unprimed)
    "DTM" -> if (drop 3 s == "") then error "DTM error" else (ArrSizeVar (drop 3 s) Max,Unprimed)
-- Added: 25.03.2006
    "REC" -> case (take 3 (drop 3 s)) of
      "DTm" -> if (drop 6 s == "") then error "RECDTm error" else (ArrSizeVar (drop 6 s) Min,Recursive)
      "DTM" -> if (drop 6 s == "") then error "RECDTM error" else (ArrSizeVar (drop 6 s) Max,Recursive)
      _ -> if (drop 3 s == "") then error "REC error" else (SizeVar (drop 3 s),Recursive)
    _ -> (SizeVar s,Unprimed)

-- showSet and showRelation are used in the log (a.omega)
-- mimic the input that Omega accepts
showSet:: ([QSizeVar],Formula) -> String
showSet (qsv,f) = show (map show qsv,f)

showRelation:: Relation -> String
showRelation (from,to,f) = show (map show from,map show to,f)

instance Show ([String],Formula) where
  show (vars,f) = "{[" ++ concatSepByComma vars ++ "]:" ++ show f ++ "};"

instance Show ([String],[String],Formula) where
  show (vars,vars',f) =  "{[" ++ concatSepByComma vars ++ "] -> [" ++ concatSepByComma vars' ++ "]:" ++ show f ++ "};"

concatSepByComma:: [String] -> String
concatSepByComma xs = _concatSepByComma xs ""
  where
  _concatSepByComma:: [String] -> ShowS
  _concatSepByComma [] = showString ""
  _concatSepByComma (x:xs) = showString x . showl xs
  showl [] = showString ""
  showl (x:xs) = showChar ',' . showString x . showl xs

concatSepByLn:: [String] -> String
concatSepByLn xs = _concatSepByComma xs ""
  where
  _concatSepByComma:: [String] -> ShowS
  _concatSepByComma [] = showString ""
  _concatSepByComma (x:xs) = showString x . showl xs
  showl [] = showString ""
  showl (x:xs) = showChar '\n' . showString x . showl xs

printProgImpt:: Prog -> FS ()
printProgImpt prog = 
  getFlags >>= \flags ->
  let outFile = outputFile flags ++ ".impt" in
	(unsafePerformIO $ writeFile outFile (showImpp prog))
		`seq` return ()

printProgImpi:: Prog -> FS ()
printProgImpi prog = 
  getFlags >>= \flags ->
  let outFile = outputFile flags ++ ".impi" in
	let io = 
	      writeFile outFile (showImpp prog) >>
	      let upsis = showImppUpsis prog in
	        putStrLn ("## " ++ show (snd upsis) ++ " runtime tests. " ++ (fst upsis))
--	      writeFile "a.pre" (showImppPre prog) 
	  in
	  unsafePerformIO io `seq` return ()

printProgC:: Prog -> FS()
printProgC prog = 
  getFlags >>= \flags ->
  let outFile = outputFile flags ++ ".c" in
	(unsafePerformIO $ writeFile outFile (showC prog))
		`seq` return ()

printProgCAll:: Prog -> FS()
printProgCAll prog = 
  getFlags >>= \flags ->
  let outFile = outputFile flags ++ ".all.c" in
	(unsafePerformIO $ writeFile outFile (showC prog))
		`seq` return ()
