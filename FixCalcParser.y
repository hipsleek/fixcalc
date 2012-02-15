{
module FixCalcParser where
import ImpAST
import ImpConfig(defaultFlags,Flags(..),Heur(..))
import ImpFixpoint2k(bottomUp2k,bottomUp2k_gen,bottomUp_mr,topDown2k,subrec,combSelHull,getDisjuncts,widen,fixTestBU,fixTestTD,getOneStep)
import ImpFormula(simplify,subset,pairwiseCheck,hull)
import Fresh
import FixCalcLexer(runP,P(..),Tk(..),lexer,getLineNum,getInput)
import MyPrelude
------------------------------------------
import Data.List(nub,elemIndex)
import Data.Maybe(fromJust)
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
  widen   {TkKwWiden}
  subset  {TkKwSubset}
  bottomup{TkKwBottomup}
  bottomup_mr{TkKwBottomup_mr}
  bottomup_gen{TkKwBottomup_gen}
  topdown {TkKwTopdown}
  selhull {TkKwSelhull}
  manualhull {TkKwManualhull}
  intersection {TkKwIntersection}
  pairwisecheck {TkKwPairwisecheck}
  hull    {TkKwHull}
  fixtestpost {TkKwFixtestpost}
  fixtestinv {TkKwFixtestinv}

%left '||'
%left '&&'
%nonassoc '>' '<' '>=' '<=' '='
%left ','         -- , must be higher than < but lower than + because 1+x<y,z+2
%left '+' '-'
%left NEG

%name parseCalc LCommand
%%


LCommand:: {[RelEnv -> FS RelEnv]}
LCommand: 
  Command LCommand       {$1:$2}      
  | {- empty -}              {[]}

Command::{RelEnv -> FS RelEnv}
Command:
    lit ':=' ParseFormula ';'                                    
    {\env -> --putStrNoLnFS ("# " ++ $1 ++ ":=") >>
             $3 env >>= \rhs ->
             case rhs of {
               R (RecPost _ f triple) -> return (R (RecPost $1 f triple)); 
               F f -> simplify f >>= \sf -> return (F sf)} >>= \renamedRHS ->
	       return (extendRelEnv env ($1,renamedRHS))}
  | ParseFormula1 ';'                                           
    {\env -> $1 env >>= \fl -> 
	mapM (\rhs ->
             case rhs of
	     (F f) -> simplify f >>= \fsimpl -> putStrFS(show fsimpl) >> return (F fsimpl)
	     (R recpost) -> putStrFS(show recpost) >> return rhs) fl >>= \rhs1 -> 
	     foldM (\env1 -> \rhs2 -> return (extendRelEnv env1 (" ",rhs2))) env rhs1
    }
  | ParseFormula ';'                                           
    {\env -> $1 env >>= \rhs -> 
             case rhs of
               (F f) -> 
                  simplify f >>= \fsimpl ->
                  --putStrFS("\n" ++ showSet fsimpl ++ "\n") >> 
                  return env
               (R recpost) -> 
                  --putStrFS ("\n" ++ show recpost ++ "\n") >> 
                  return env
    }
  | fixtestpost '(' lit ',' lit ')' ';'
    {\env -> --putStrFS("# fixtestPost("++ $3 ++ "," ++ $5 ++ ");") >> 
             case (lookupVar $3 env,lookupVar $5 env) of
               (Just (R recpost),Just (F f)) ->
                  fixTestBU recpost f >>= \fixok -> 
                  --putStrFS("\n" ++ show fixok ++ "\n") >> 
                  return env
               (_,_) -> error ("Arguments of fixtest are incorrect")}
  | fixtestinv '(' lit ',' lit ')' ';'
    {\env -> --putStrFS("# fixtestInv("++ $3 ++ "," ++ $5 ++ ");") >> 
             case (lookupVar $3 env,lookupVar $5 env) of
               (Just (R recpost),Just (F f)) ->
                  getOneStep recpost fTrue >>= \oneStep ->
                  fixTestTD oneStep f >>= \fixok -> 
                  --putStrFS("\n" ++ show fixok ++ "\n") >> 
                  return env
               (_,_) -> error ("Arguments of fixtestInv are incorrect")}
  | lit subset lit ';'                                
    {\env -> --putStrFS("# "++ $1 ++ " subset " ++ $3 ++ ";") >>
             case (lookupVar $1 env,lookupVar $3 env) of
               (Just (F f1),Just (F f2)) ->
                  subset f1 f2 >>= \subok -> 
                  --putStrFS("\n" ++ show subok ++ "\n") >> 
                  return env
               (_,_) -> error ("Argument of subset is not a valid formula\n")
     }
  | lit ';'
    {\env -> --putStrFS("# "++ $1 ++ ";") >>
             case lookupVar $1 env of 
               Just (R recpost) -> --putStrFS("\n" ++ show recpost ++ "\n") >> 
                 return env
               Just (F f) -> putStrFS("\n" ++ show f ++ "\n") >> 
                 return env
               Nothing -> error ("Variable not declared - "++$1++"\n")
    }                   


ParseFormula1::{RelEnv -> FS [Value]}
ParseFormula1:
bottomup_gen '(' '[' Llit ']'')' 
     {\env -> let heur = SimilarityHeur in
	  bottomUp2k_gen ($4 env) (map (\x -> (1,heur)) ($4 env)) (map (\x -> fFalse) ($4 env)) 
	 >>= \resl -> return (map (\x -> F x) (fst (unzip resl)))}

ParseFormula::{RelEnv -> FS Value}
ParseFormula:
    '{' '[' LPorUSizeVar ']' ':' Formula '}'      
                  {\env -> --putStrFS ("{ ... };") >>
                           if "f_" `elem` (map (\(SizeVar anno,_) -> take 2 anno) (fqsv $6)) then 
                             error ("Free variables of formula should not start with \"f_\" (\"f_\" are fresh variables)")
                           else return (F $6)} 
  | '{' '[' LPorUSizeVar ']' '-' '>' '[' LPorUSizeVar ']' '-' '>' '[' LPorUSizeVar ']' ':' Formula '}'      
                  {\env -> --putStrFS ("{ ... };") >> 
                           if "f_" `elem` (map (\(SizeVar anno,_) -> take 2 anno) (fqsv $16)) then 
                             error ("Free variables of formula should not start with \"f_\" (\"f_\" are fresh variables)")
                           else return (R (RecPost "dummy" $16 (reverse $3,reverse $8,reverse $13)))}
  | lit '(' lit ')'
                {\env -> --putStrFS ($1 ++ "(" ++ $3 ++ ");") >>
                         let cabst = case lookupVar $1 env of {Just (R recpost) -> recpost; 
                                                               Just (F f) -> error ("Argument of subrec is not a constraint abstraction\n"); 
                                                               Nothing -> error ("Variable not declared - "++$1++"\n")} in
                         let f = case lookupVar $3 env of {Just (F f) -> f;
                                                           Just (R recpost) -> error ("Argument of subrec is not a formula\n"); 
                                                           Nothing -> error ("Variable not declared - "++$3++"\n")} in
                         subrec cabst f >>= \fn -> simplify fn >>= \fnext -> return (F fnext)}
  | bottomup '(' lit ',' intNum ',' lit ')'
        {\env -> --putStrFS ("bottomup(" ++ $3 ++ "," ++ show $5 ++ "," ++ $7 ++ ");") >>
                 case lookupVar $3 env of
                   Just (F f) -> error ("Argument of bottomup is not a constraint abstraction\n")
                   Nothing -> error ("Variable not declared - "++$3++"\n")
                   Just (R recpost) -> 
                     let heur = case $7 of {"SimHeur" -> SimilarityHeur; "DiffHeur" -> DifferenceHeur; "HausHeur" -> HausdorffHeur; lit -> error ("Heuristic not implemented - "++lit)} in
                     bottomUp2k recpost ($5,heur) fFalse >>= \(post,cnt) -> return (F post)}
  | bottomup_mr '(' lit ',' lit ')'
        {\env -> putStrFS ("bottomup_mr(" ++ $3 ++ "," ++ $5 ++ ");") >>
	case lookupVar $3 env of
	    Just (F f) -> error ("First argument of bottomup_mr is not a constraint abstraction\n")
	    Nothing -> error ("Variable not declared - "++$3++"\n")
	    Just (R recpost1) -> 
	      case lookupVar $5 env of 
	    	    Just (F f) -> error ("Second argument of bottomup_mr is not a constraint abstraction\n")
	    	    Nothing -> error ("Variable not declared - "++$5++"\n")
	            Just (R recpost2) -> 
		      bottomUp_mr recpost1 recpost2  >>= \(post,cnt) -> return (F post)}
  | topdown '(' lit ',' intNum ',' lit ')'
        {\env -> --putStrFS ("topdown(" ++ $3 ++ "," ++ show $5 ++ "," ++ $7 ++ ");") >>
                 case lookupVar $3 env of
                   Just (F f) -> error ("Argument of topdown is not a constraint abstraction\n")
                   Nothing -> error ("Variable not declared - "++$3++"\n")
                   Just (R recpost) -> 
                     let heur = case $7 of {"SimHeur" -> SimilarityHeur; "DiffHeur" -> DifferenceHeur; "HausHeur" -> HausdorffHeur; lit -> error ("Heuristic not implemented - "++lit)} in
                     topDown2k recpost ($5,heur) fTrue >>= \(inv,cnt) -> return (F inv)}
  | selhull '(' lit ',' intNum ',' lit ')'
        {\env -> --putStrFS ("selhull(" ++ $3 ++ "," ++ show $5 ++ "," ++ $7 ++ ");") >>
                 case lookupVar $3 env of
                   Just (R recpost) -> error ("Argument of selhull is not a formula\n")
                   Nothing -> error ("Variable not declared - "++$3++"\n")
                   Just (F f) -> 
                     let heur = case $7 of {"SimHeur" -> SimilarityHeur; "DiffHeur" -> DifferenceHeur; "HausHeur" -> HausdorffHeur; lit -> error ("Heuristic not implemented - "++lit)} in
                     combSelHull ($5,heur) (getDisjuncts f) undefined >>= \disj -> return (F (Or disj))}
  | manualhull '(' lit ',' '[' LInt ']' ')'
        {\env -> --putStrFS ("manualhull(" ++ $3 ++ "," ++ show $6 ++ ");") >>
                 case lookupVar $3 env of
                    Just (F f) -> 
                      let disj = getDisjuncts f in
                      if length disj == length $6 then
                        let grouped = groupDisjuncts (zip disj $6) (nub $6) (replicate (length (nub $6)) fFalse) in
                        mapM (\x -> hull x) grouped >>= \hulled ->
                        return (F (fOr hulled))
                      else
                        error ("Length of the list " ++ show $6 ++ " is different than the number of disjuncts in formula.")
                    _ -> error ("First argument of manualhull is not a formula.")
                      
        }
  | widen '(' lit ',' lit ',' lit ')' 
        {\env -> --putStrFS ("widen(" ++ $3 ++ "," ++ $5 ++ "," ++ $7 ++ ");") >>
                 case (lookupVar $3 env,lookupVar $5 env) of
                   (Just (F f1),Just (F f2)) -> 
                     let heur = case $7 of {"SimHeur" -> SimilarityHeur; "DiffHeur" -> DifferenceHeur; "HausHeur" -> HausdorffHeur; lit -> error ("Heuristic not implemented - "++lit)} in
                     widen heur (getDisjuncts f1,getDisjuncts f2) >>= \disj ->
                     return (F (Or disj))
                   (Just (R recpost),_) -> error ("Argument of widen is not a formula\n")
                   (_,Just (R recpost)) -> error ("Argument of widen is not a formula\n")
                   (_,_) -> error ("Variable not declared - "++$3++"\n")
        }
  | lit intersection lit
        {\env -> --putStrFS($1 ++ " intersection " ++ $3 ++ ";") >>
                 case (lookupVar $1 env,lookupVar $3 env) of
                   (Just (F f1),Just (F f2)) ->
                      simplify (And [f1,f2]) >>= \f3 -> 
                      return (F f3)
                   (_,_) -> error ("Argument of intersection is not a valid formula\n")
         }
  | hull lit
        {\env -> --putStrFS("hull " ++ $2 ++ ";") >>
                 case (lookupVar $2 env) of
                   Just (F f1) -> hull f1 >>= \f2 -> 
                      return (F f2)
                   _ -> error ("Argument of hull is not a valid formula\n")
         }
  | pairwisecheck lit
        {\env -> --putStrFS ("PairwiseCheck "++ $2) >>
                 case lookupVar $2 env of
                   Just (F f) -> 
                      pairwiseCheck f >>= \fsimpl ->
                      return (F fsimpl)
                   _ -> error ("Argument of pairwisecheck is not a valid formula "++$2++"\n")
        }

Llit:: {RelEnv -> [RecPost]}
Llit: lit {
     \env -> case lookupVar $1 env of
       Just (F f) -> error ("Argument of bottomup is not a constraint abstraction\n")
       Nothing -> error ("Variable not declared - "++$1++"\n")
       Just (R recpost) -> [recpost]
  }
 | lit ',' Llit {
     \env -> case lookupVar $1 env of
       Just (F f) -> error ("Argument of bottomup is not a constraint abstraction\n")
       Nothing -> error ("Variable not declared - "++$1++"\n")
       Just (R recpost) -> recpost:($3 env)}

LInt::{[Int]}
LInt: intNum {[$1]}
  | intNum ',' LInt {$1:$3}


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
parse :: String -> Flags -> IO ()
parse s flags = 
  let listFunc = runP s parseCalc in
  let parseFuncFS = foldM (\env -> \func -> func env) emptyRelEnv listFunc in 
  runFS (initialState flags) parseFuncFS >>= \lastenv -> return ()

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

groupDisjuncts:: [(Formula,Int)] -> [Int] -> [Formula] -> [Formula]
groupDisjuncts [] uniqueIds partialFormulae = partialFormulae
groupDisjuncts ((d,groupId):disj) uniqueIds partialFormulae =
  let ix = fromJust (elemIndex groupId uniqueIds) in
  let newPartialFormulae = updateList partialFormulae ix (Or [partialFormulae!!ix,d]) in
  groupDisjuncts disj uniqueIds newPartialFormulae
  
--updateList:: [a] -> (Int,a) -> [a]
--updateList xs (i,upd) = updateList1 xs (i,upd) 0
--  where
--  updateList1 xs (i,upd) j = 
--    if (i==j) then upd:(tail xs)
--    else updateList1 (tail xs) (i,upd) (j+1)
}
