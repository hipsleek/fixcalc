{
module FixCalcParser where
import ImpAST
import ImpConfig(defaultFlags)
import ImpFixpoint2k(bottomUp2k,Heur(..),subrec,combSelHull,getDisjuncts,undefinedF,widen,widenPPL,fixTestBU)
import ImpFormula(fqsv,simplify,subset)
import Fresh
import FixCalcLexer(runP,P(..),Tk(..),lexer,getLineNum,getInput)
import MyPrelude
------------------------------------------
import Monad(foldM)
}

%monad {P}
%lexer {lexer} {TkEOF}
%tokentype {Tk}
%token
	lit	{TkAlphaNum $$}
	intNum	{TkIntNum $$}
	true	{TkTrue}
	false	{TkFalse}
	'+'		{TkPlus}
	'-'		{TkMinus}
	'('		{TkLBr}
	')'		{TkRBr}
	';'		{TkSemiColon}
	':='	{TkAssign}
	'['		{TkLSqBr}
	']'		{TkRSqBr}
	'{'		{TkLAcc}
	'}'		{TkRAcc}
	','		{TkComma}
	'='   {TkEq}
	'<'   {TkLT}
	'>'   {TkGT}
	'>='  {TkGTE}
	'<='  {TkLTE}	
	'&&'   {TkAnd}
	'||'  {TkOr}
	':'   {TkColon}
	'.'   {TkDot}
	exists{TkExists}
	forall{TkForall}
	prime {TkPrime}
	rec   {TkRec}
  fixtest {TkKwFixtest}
  widen   {TkKwWiden}
  widenppl   {TkKwWidenppl}
  subset  {TkKwSubset}
  bottomup{TkKwBottomup}
  selhull {TkKwSelhull}

%left '||'
%left '&&'
%nonassoc '>' '<' '>=' '<=' '='
%left ','         -- , must be higher than < but lower than + because 1+x<y,z+2
%left '+' '-'
%left NEG

%name parseCalc LInputItem
%%

LInputItem:: {[RelEnv -> FS RelEnv]}
LInputItem: 
  InputItem LInputItem       {$1:$2}      
  | {- empty -}              {[]}

InputItem::{RelEnv -> FS RelEnv}
InputItem:
    lit ':=' Lhs ';'                                    
        {\env -> putStrNoLnFS ("# " ++ $1 ++ ":=") >>
                 $3 env >>= \lhs -> 
                 case lhs of {R (RecPost _ args f triple) -> return (R (RecPost $1 args f triple)); F f -> simplify f >>= \sf -> return (F sf)} >>= \renamedLHS ->
                 return (extendRelEnv env ($1,renamedLHS))}
  | lit subset lit ';'                                
        {\env -> putStrFS("# "++ $1 ++ " subset " ++ $3 ++ ";") >>
                 case (lookupVar $1 env,lookupVar $3 env) of
                   (Just (F f1),Just (F f2)) ->
                      subset f1 f2 >>= \subok -> 
                      putStrFS("\n" ++ show subok ++ "\n") >> 
                      return env
                   (_,_) -> error ("Argument of subset is not a valid formula\n")
         }
  | lit ';'                                           
        {\env -> putStrFS ("# "++ $1 ++";") >>
                 case lookupVar $1 env of
                   Just (F f) -> 
                      simplify f >>= \fsimpl ->
                      putStrFS("\n" ++ showSet (fqsv fsimpl,fsimpl) ++ "\n") >> return env
                   Just (R recpost) -> 
                      putStrFS ("\n" ++ show recpost ++ "\n") >> return env
                   Nothing -> error ("Variable not declared - "++$1++"\n")
        }
  | fixtest '(' lit ',' lit ')' ';'
        {\env -> putStrFS("# fixtest("++ $3 ++ "," ++ $5 ++ ");") >> 
                 case (lookupVar $3 env,lookupVar $5 env) of
                   (Just (R recpost),Just (F f)) ->
                      fixTestBU recpost f >>= \fixok -> 
                      putStrFS("\n" ++ show fixok ++ "\n") >> return env
                   (_,_) -> error ("Arguments of fixtest are incorrect")}
                     

Lhs::{RelEnv -> FS Value}
Lhs:
    '{' '[' LPorUSizeVar ']' ':' Formula '}'      
                  {\env -> putStrFS ("{ ... };") >>
                           if "f_" `elem` (map (\(SizeVar anno,_) -> take 2 anno) (fqsv $6)) then 
                             error ("Free variables of formula should not start with \"f_\" (\"f_\" are fresh variables)")
                           else return (F $6)} 
  | '{' '[' LPorUSizeVar ']' '-' '>' '[' LPorUSizeVar ']' '-' '>' '[' LPorUSizeVar ']' ':' Formula '}'      
                  {\env -> putStrFS ("{ ... };") >> 
                           if "f_" `elem` (map (\(SizeVar anno,_) -> take 2 anno) (fqsv $16)) then 
                             error ("Free variables of formula should not start with \"f_\" (\"f_\" are fresh variables)")
                           else return (R (RecPost "dummy" (reverse $3++reverse $8) $16 (reverse $3,reverse $8,reverse $13)))}
  | lit '(' lit ')'
                {\env -> putStrFS ($1 ++ "(" ++ $3 ++ ");") >>
                         let cabst = case lookupVar $1 env of {Just (R recpost) -> recpost; 
                                                               Just (F f) -> error ("Argument of subrec is not a constraint abstraction\n"); 
                                                               Nothing -> error ("Variable not declared - "++$1++"\n")} in
                         let f = case lookupVar $3 env of {Just (F f) -> f;
                                                           Just (R recpost) -> error ("Argument of subrec is not a formula\n"); 
                                                           Nothing -> error ("Variable not declared - "++$3++"\n")} in
                         subrec cabst f >>= \fn -> simplify fn >>= \fnext -> return (F fnext)}
  | bottomup '(' lit ',' intNum ',' lit ')'
        {\env -> putStrFS ("bottomup(" ++ $3 ++ "," ++ show $5 ++ "," ++ $7 ++ ");") >>
                 case lookupVar $3 env of
                   Just (F f) -> error ("Argument of bottomup is not a constraint abstraction\n")
                   Nothing -> error ("Variable not declared - "++$3++"\n")
                   Just (R recpost) -> 
                     let heur = case $7 of {"SimHeur" -> SimilarityHeur; "DiffHeur" -> DifferenceHeur; lit -> error ("Heuristic not implemented - "++lit)} in
                     bottomUp2k recpost ($5,heur) fFalse >>= \(post,cnt) -> return (F post)}
  | selhull '(' lit ',' intNum ',' lit ')'
        {\env -> putStrFS ("selhull(" ++ $3 ++ "," ++ show $5 ++ "," ++ $7 ++ ");") >>
                 case lookupVar $3 env of
                   Just (R recpost) -> error ("Argument of selhull is not a formula\n")
                   Nothing -> error ("Variable not declared - "++$3++"\n")
                   Just (F f) -> 
                     let heur = case $7 of {"SimHeur" -> SimilarityHeur; "DiffHeur" -> DifferenceHeur; lit -> error ("Heuristic not implemented - "++lit)} in
                     combSelHull ($5,heur) (getDisjuncts f) undefinedF >>= \disj -> return (F (Or disj))}
  | widen '(' lit ',' lit ')' 
        {\env -> putStrFS ("widen(" ++ $3 ++ "," ++ $5 ++ ");") >>
                 case (lookupVar $3 env,lookupVar $5 env) of
                   (Just (F f1),Just (F f2)) -> widen SimilarityHeur (getDisjuncts f1,getDisjuncts f2) >>= \disj ->
                      return (F (Or disj))
                   (Just (R recpost),_) -> error ("Argument of widen is not a formula\n")
                   (_,Just (R recpost)) -> error ("Argument of widen is not a formula\n")
                   (_,_) -> error ("Variable not declared - "++$3++"\n")
        }
  | widenppl '(' lit ',' lit ')' 
        {\env -> putStrFS ("widenppl(" ++ $3 ++ "," ++ $5 ++ ");") >>
                 case (lookupVar $3 env,lookupVar $5 env) of
                   (Just (F f1),Just (F f2)) -> widenPPL (getDisjuncts f1++getDisjuncts f2) (getDisjuncts f1++getDisjuncts f2) >>= \disj ->
                      return (F (Or disj))
                   (Just (R recpost),_) -> error ("Argument of widenppl is not a formula\n")
                   (_,Just (R recpost)) -> error ("Argument of widenppl is not a formula\n")
                   (_,_) -> error ("Variable not declared - "++$3++"\n")
        }

Formula: QFormula  {$1}
  | '(' Formula ')' {$2}
  | Formula '&&' Formula 
    { And [$1,$3] }
  | Formula '||' Formula 
    { Or [$1,$3] }
  | true { fTrue }
  | false { fFalse }


QFormula:: {Formula}
QFormula: LBExpr { let (f,rest)=$1 in f}
  | exists '(' LPorUSizeVar1 ':' Formula ')' 
    { fExists (reverse $3) $5 }
  | forall '(' LPorUSizeVar1 ':' Formula ')' 
    { fForall (reverse $3) $5 }
  
-- from the final result of qs, only Formula is useful
-- [[Update]] is needed only in the intermediate productions
LBExpr:: {(Formula,[[Update]])}
LBExpr:
  BExpr {$1}
  | lit '(' LPorUSizeVar1 ')' {(AppRecPost $1 (reverse $3),[])}
  | LBExpr RelOp LAExpr
  { let (f,rest) = $1 in
    let third = reverse $3 in
    let combi = [(e1,e2) | e1 <- rest, e2 <- third] in
      case $2 of
        TkEq  -> 
          let newfs = map (\(e1,e2) -> EqK (e1 ++ (minus_update e2))) combi in 
            (And (f:newfs),third)
        TkGTE -> 
          let newfs = map (\(e1,e2) -> GEq (e1 ++ (minus_update e2))) combi in 
            (And (f:newfs),third)
        TkGT  ->
          let newfs = map (\(e1,e2) -> GEq ((Const (-1)):(e1 ++ minus_update e2))) combi in
            (And (f:newfs),third)
        TkLTE ->
          let newfs = map (\(e1,e2) -> GEq (e2 ++ (minus_update e1))) combi in
            (And (f:newfs),third)
        TkLT  ->
          let newfs = map (\(e1,e2) -> GEq ((Const (-1)):(e2 ++ minus_update e1))) combi in
            (And (f:newfs),third)
  }


BExpr:: { (Formula,[[Update]]) }
BExpr: 
  LAExpr RelOp LAExpr
  { let (first,third) = (reverse $1,reverse $3) in
    let combi = [(e1,e2) | e1 <- first, e2 <- third] in
    case $2 of
      TkEq -> 
        let newfs = map (\(e1,e2) -> (EqK (e1 ++ (minus_update e2)))) combi in
          if singleton newfs then (head newfs,third) else (And newfs,third)
      TkGTE -> 
        let newfs = map (\(e1,e2) -> (GEq (e1 ++ (minus_update e2)))) combi in 
          if singleton newfs then (head newfs,third) else (And newfs,third)
      TkGT  -> 
        let newfs = map (\(e1,e2) -> (GEq ((Const (- 1)):(e1 ++ (minus_update e2))) )) combi in
          if singleton newfs then (head newfs,third) else (And newfs,third)
      TkLTE -> 
        let newfs = map (\(e1,e2) -> (GEq (e2 ++ (minus_update e1)))) combi in 
          if singleton newfs then (head newfs,third) else (And newfs,third)
      TkLT  -> 
        let newfs = map (\(e1,e2) -> (GEq ((Const (- 1)):(e2 ++ (minus_update e1))) )) combi in
          if singleton newfs then (head newfs,third) else (And newfs,third)
  }
    
RelOp:: {Tk}
RelOp: '='  {$1}
  | '>='  {$1}
  | '>'   {$1}
  | '<='  {$1}
  | '<'   {$1}

-- list of AExpr -- AExpr,AExpr,..
LAExpr:: { [[Update]]}
LAExpr: LAExpr ',' AExpr   { $3:$1 }
  | AExpr  { [$1] }

      
-- AExpr == [Update]
AExpr:: { [Update] }
AExpr : AExpr '+' AExpr { $1 ++ $3 }
     | AExpr '-' AExpr { $1 ++ (minus_update $3) }
     | '(' AExpr ')'  { $2 }
     | intNum PorUSizeVar  { [ Coef $2 $1 ] }
     | '-' intNum PorUSizeVar  { [ Coef $3 (-$2) ] }
     | intNum           { [ Const $1 ] }
     | '-' intNum %prec NEG { [ Const (- $2)] }
     | PorUSizeVar      { [ Coef $1 1 ]} 
     | '-' PorUSizeVar      { [ Coef $2 (-1) ]} 

LPorUSizeVar: {- empty -} {[]}
  | LPorUSizeVar1 {$1}

LPorUSizeVar1: LPorUSizeVar1 ',' PorUSizeVar {$3:$1}
  | PorUSizeVar     {[$1]}

PorUSizeVar:: {QSizeVar}
PorUSizeVar: 
  lit {(stringToQsv $1)}
  | lit prime {(SizeVar $1,Primed)}
  | lit rec {(SizeVar $1,Recursive)}
  | lit '.' lit { 
      if ($3=="min") 
        then ((ArrSizeVar $1 Min),Unprimed)
        else 
          if ($3=="max") 
            then ((ArrSizeVar $1 Max),Unprimed) 
            else error $ "neither min or max after QSizeVar"
      }
  | lit '.' lit prime { 
      if ($3=="min") 
        then ((ArrSizeVar $1 Min),Primed)
        else 
          if ($3=="max") 
            then ((ArrSizeVar $1 Max),Primed) 
            else error $ "neither min or max after QSizeVar"
      }
  | lit '.' lit rec { 
      if ($3=="min") 
        then ((ArrSizeVar $1 Min),Recursive)
        else 
          if ($3=="max") 
            then ((ArrSizeVar $1 Max),Recursive) 
            else error $ "neither min or max after QSizeVar"
      }


{
happyError :: P a
happyError = do l <- getLineNum
		s <- getInput
		error $ "Parse error on line " ++ (show l) ++ " rest of line: " ++ (takeWhile (/= '\n') s)

minus_update :: [Update] -> [Update]
minus_update [] = []
minus_update ((Const i):us) = (Const (- i)):(minus_update us)
minus_update ((Coef v i):us) = (Coef v (- i)):(minus_update us) 

--returning type varies depending on the grammar's start symbol
parse :: String -> IO ()
parse s = 
  let listFunc = runP s parseCalc in
  let parseFuncFS = foldM (\env -> \func -> func env) emptyRelEnv listFunc in 
  runFS (initialState defaultFlags) parseFuncFS >>= \lastenv -> return ()

type RelEnv = [(Lit,Value)]
data Value = F Formula
  | R RecPost

emptyRelEnv :: RelEnv
emptyRelEnv = []

extendRelEnv :: RelEnv -> (Lit,Value) -> RelEnv
extendRelEnv gamma (var,ty) = (var,ty):gamma

lookupVar :: Lit -> RelEnv -> Maybe Value
lookupVar lit [] = Nothing
lookupVar lit env@((v,f):rest) | (lit == v) = Just f
  | otherwise = lookupVar lit rest

}
