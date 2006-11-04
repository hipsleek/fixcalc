module ImpFixpt where

import ImpAST

-- Utilities
-- subrec takes a recursive call and replace it with the second arguement.
subrec :: Formula -> Formula -> Formula
subrec f1 f2 = let f2' = toPrime f2
               in subrec1 f1 f2'
 where subrec1 f g =
	case f of 
 	  (And fs) -> map (\x -> subrec1 x g) fs
	  (Or fs) -> map (\x -> subrec1 x g) fs
	  (Not ff) -> subrec1 ff g
	  (Exists vars ff) -> subrec1 ff g
	  (Forall vars ff) -> subrec1 ff g
	  (CAbstApply id vars) -> g
	  _ -> f
   
-- toPrime primes all the varaibles appear in the formula
toPrime :: Formula -> Formula
toPrime f =
 case f of 
  (And fs) -> map (\x -> toPrime x) fs
  (Or fs) -> map (\x -> toPrime x) fs
  (Not ff) -> toPrime ff
  (Exists vars ff) -> toPrime ff
  (Forall vars ff) -> toPrime ff
  (GEq upds) -> let upds' = map (\x -> toPrimeUpdate x)
	        in (GEq upds')
  (EqK upds) -> let upds' = map (\x -> toPrimeUpdate x)
	        in (GEq upds')
  (CAbstApply id vars) -> f   -- this case shouldn't be reached.
  
toPrimeUpdate :: Update -> Update
toPrimeUpdate upd = 
 case upd of
  (Coef (svar, Unprimed) i) -> (Coef (svar, Primed) i)
  _ -> upd
  
toPrimeSVar :: QSizeVar -> QSizeVar
toPrimeSVar (svar,u) = (svar,Primed)) 

-- widen takes f1 and f2, each of them in conjunction form
-- \forall clause \in f1, if f2 => clause then clause \in f1'
-- f1' is the returned formula
widen :: CAbst -> CAbst -> CAbst
widen f1 f2 = 
  let f1s = buildClauses f1
	    tests =  map (\x -> f2 subset x) f1s		-- omega
		  f1s' = zip f1s tests
	    f1' = rmClauses f1s'
		  f1'' = mergeClauses f1'
	in f1''
 where 
  buildClauses (CAbst fname f) = 
	 -- flat nested And: final formula = c1 & c2 & ... & cn
	 -- return a list of CAbsts with each ci as formula, i=1..n
	 case f of
	   (And fs) -> case fs of
		    [ff] -> case ff of
    			  (And fs') -> buildClauses (CAbst fname ff)
    			  _ -> [(CAbst fname ff)]
		    (fa:fs') -> 
		      let fs'' = buildClauses (CAbst fname (And fs'))
			    in case fa of
			        (And fs') -> 
			          let fa' = buildClauses (CAbst fname fa)
					      in fa'++fs''
			        _ -> (CAbst fname fa):fs''
	   _ -> fFalse -- formula need to be in conjunction form
  rmClauses fs = case fs of
			[] -> []
			(fa:fs') -> if (snd fa == False) then (rmClauses fs')
					else (fst fa):(rmClauses fs')
	mergeClauses fs = let (CAbst fname f) = head fs
			      map (\(CAbst fn ff) -> ff) fs
			  in (CAbst fname (And fs))

-- bottomup takes a constraint abstraction and returns a post-condition
bottomup :: CAbst -> Formula
bottomup (CAbst fn vars formula) =  
 let f1 = subrec formula fFalse
     f1r = simplifyIt f1	-- omega
     f2 = subrec formula f1r  
     f2r = simplifyIt f2	-- omega
     f3 = subrec formula f2r  
     f3r = simplifyIt f3	-- omega
 in 
  if ((CAbst fn f3r) subset (CAbst fn f2r)) then 
    f2r	-- omega
  else 
    let f4 = subrec formula f3
        f4r = simplifyIt f4	-- omega
    in if ((CAbst fn f4r) subset (CAbst fn f3r)) then f3r -- omega
    else let hf3r = selHull f3r -- omega, selective hulling is not done yet
       hf4r = selHull f4r -- omega
         in if ((CAbst fn hf4r) subset (CAbst fn hf3r)) -- omega
         then hf3r
         else let wf3r = multiWiden hf3r hf4r -- xuna 5&6
          wf4r = subrec formula wf3r
        in if ((CAbst fn wf4r) subset (CAbst fn wf3r)) -- omega
          then wf3r
          else iter wf4r (length var -4)
 where iter f n = if n>0 then let f5 = subrec formula f
          hf5 = hull f5 -- omega
              in if ((CAbst fn hf5) subset (CAbst fn f)) then f -- omega
          else iter hf5 (n-1)
      else fTrue
{--- will finish this part tomorrow 
-- topdown takes a constraint abstraction and returns its invariant
topdown :: CAbst -> Formula 
topdown (CAbst fname vars formula) = 
 let f1 = extractRec formula
     vars' = map toPrimeSVar vars
     cf = CAbstR fname vars vars' f1 -- CAbstR is for relation, currently not in ImpAbst.hs
     f2 = hull (cf union (cf compose cf)) -- omega
     f3 = hull (f2 union (f2 compose cf)) -- omega
 in if (f3 subset f2)
	then f2
	else let wf2 = widen f2 f3
	         wf3 = hull (wf2 union (wf2 compose cf))
	     in if (wf3 subset wf2)
			then wf2
			else iter cf wf3 (2*(length vars)-2)
 where iter cf f n = let f4 = hull (f union (f compose cf))
		     in if (f4 subset f)
			   then f 
			   else let wf = widen f f4
				    wf4 =  hull (wf union (wf compose cf))
				in if (wf4 subset wf)
					then wf
					else if (n-1>0) then iter cf wf4
							else fFalse


{-
     abc = map (\x-> case x of	-- fresh is not needed because we will \exists abc.
			(SizeVar a) -> (SizeVar (a++"1"))
			(ArrSizeVar a m) -> (ArrSizeVar (a++"1") m)) vars
     fs = Exists abc (subrec f1 
     f2 = Or [f1,fs] 
 in cf
-}
				     