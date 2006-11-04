module FixCalcLexer where
import Data.Char(isAlpha,isDigit,isAlphaNum)
-------Tokens----------------------
data Tk=
	TkAlphaNum String
	| TkTrue | TkFalse | TkIntNum Int | TkFloatNum Float
	| TkAssign | TkSemiColon | TkLAcc | TkRAcc | TkComma
	| TkLBr | TkRBr | TkLSqBr | TkRSqBr
	| TkColon
  | TkAnd | TkOr 
	| TkPlus | TkMinus | TkMul | TkDiv
	| TkEq | TkGT | TkGTE | TkLT | TkLTE | TkNEq | TkNot
  | TkPrime 
  | TkDblPercent
  | TkExists | TkForall | TkDot
	| TkEOF
	| TkRec
	| TkString String
	| TkKwFixtest | TkKwWiden | TkKwSubset | TkKwBottomup | TkKwSelhull | TkKwWidenppl

lexer :: (Tk -> P a) -> P a
lexer cont = getInput >>= 
	\input -> lexer' input >>= 
		\token -> cont token

lexer' :: String -> P Tk
lexer' [] = return TkEOF
lexer' ('\n':xs) = incLineNum >> lexer' xs
lexer' ('^':xs) = returnPI TkRec xs
lexer' ('.':xs) = returnPI TkDot xs
lexer' ('=':xs) = returnPI TkEq xs
lexer' (';':xs) = returnPI TkSemiColon xs
-- '()' should precede '(', but if so, functions without args cannot be recognized -> I use Void instead of ()
--lexer' ('(':')':xs) = returnPI TkVoid xs 
lexer' ('(':xs) = returnPI TkLBr xs
lexer' (')':xs) = returnPI TkRBr xs
lexer' ('{':xs) = returnPI TkLAcc xs
lexer' ('}':xs) = returnPI TkRAcc xs
lexer' ('[':xs) = returnPI TkLSqBr xs
lexer' (']':xs) = returnPI TkRSqBr xs
lexer' (',':xs) = returnPI TkComma xs
lexer' (':':'=':xs) = returnPI TkAssign xs
lexer' (':':xs) = returnPI TkColon xs
lexer' ('&':'&':xs) = returnPI TkAnd xs
lexer' ('|':'|':xs) = returnPI TkOr xs
lexer' ('+':xs) = returnPI TkPlus xs
lexer' ('#':xs) = lexer' $ dropWhile (/= '\n') xs
lexer' ('-':xs) = returnPI TkMinus xs
lexer' ('>':'=':xs) = returnPI TkGTE xs
lexer' ('>':xs) = returnPI TkGT xs
lexer' ('<':'=':xs) = returnPI TkLTE xs
lexer' ('<':'>':xs) = returnPI TkNEq xs
lexer' ('<':xs) = returnPI TkLT xs
lexer' ('*':xs) = returnPI TkMul xs
lexer' ('/':xs) = returnPI TkDiv xs
lexer' ('!':xs) = returnPI TkNot xs
lexer' ('\'':xs) = returnPI TkPrime xs
lexer' ('%':'%':xs) = 
	resetLineNum >>
	returnPI TkDblPercent xs
lexer' ('T':'r':'u':'e':xs) | not $ isAlphaNum (head xs) = returnPI TkTrue xs
lexer' ('F':'a':'l':'s':'e':xs) | not $ isAlphaNum (head xs) = returnPI TkFalse xs
lexer' ('e':'x':'i':'s':'t':'s':xs) | not $ isAlphaNum (head xs) = returnPI TkExists xs
lexer' ('f':'o':'r':'a':'l':'l':xs) | not $ isAlphaNum (head xs) = returnPI TkForall xs
lexer' ('f':'i':'x':'t':'e':'s':'t':xs) | not $ isAlphaNum (head xs) = returnPI TkKwFixtest xs
lexer' ('w':'i':'d':'e':'n':xs) | not $ isAlphaNum (head xs) = returnPI TkKwWiden xs
lexer' ('w':'i':'d':'e':'n':'p':'p':'l':xs) | not $ isAlphaNum (head xs) = returnPI TkKwWidenppl xs
lexer' ('s':'u':'b':'s':'e':'t':xs) | not $ isAlphaNum (head xs) = returnPI TkKwSubset xs
lexer' ('b':'o':'t':'t':'o':'m':'u':'p':xs) | not $ isAlphaNum (head xs) = returnPI TkKwBottomup xs
lexer' ('s':'e':'l':'h':'u':'l':'l':xs) | not $ isAlphaNum (head xs) = returnPI TkKwSelhull xs
lexer' ('\"':xs) = lexString "" xs

lexer' all@(x:xs)
  | _isSpace x   = lexer' $ dropWhile (_isSpace) xs 
  | isDigit x   = 
    let (int,rst) = span (isDigit) all in
      case rst of
        [] -> setInput rst >> return (TkIntNum (read int))
        _ -> case (head rst) of
          '.' -> case (tail rst) of
            [] -> setInput rst >> return (TkIntNum (read int))
            _ -> case (isDigit (head (tail rst))) of
              True -> let (fnum,frst) = span (isDigit) (tail rst) in
                setInput frst >> return (TkFloatNum (read (int ++"."++ fnum)))
              False -> setInput rst >> return (TkIntNum (read int))
          _ -> setInput rst >> return (TkIntNum (read int))
  | isAlpha x		= let (str,rst) = span (isIdChar) all in 
    setInput rst >> return (TkAlphaNum str)
  | otherwise		= error $ "unrecognised token at `" ++ 
      (takeWhile (/='\n') all) ++ "'"
  where
  -- c == '\n' is removed from original isSpace, so that lines can be counted correctly
  _isSpace:: Char -> Bool
  _isSpace c =
    c == ' '  ||
    c == '\t' ||
    c == '\r' ||
    c == '\f' ||
    c == '\v' ||
    c == '\xa0'
  
isIdChar x = (isAlphaNum x) || x == '_'

lexString:: String -> String -> P Tk
lexString part s = case s of
  '\"':xs -> returnPI (TkString (reverse part)) xs
  c:xs -> lexString (c:part) xs
  
-------State Monad-----------------
data St = MkState {input :: String, linenum :: Int}
newtype P a = P (St -> (St, a))

instance Monad P where
    --return :: a -> P a
    return a = P (\st -> (st, a))

    --(>>=) :: P a -> (a -> P b) -> P b
    (P a) >>= f = P (\st -> let (st', a') = (a st)
	                        (P b)     = (f a')
	                    in b st')

runP :: String -> P a -> a
runP s (P a) = snd $ a initState
    where initState = MkState {input = s, linenum = 1}

getLineNum :: P Int
getLineNum = P (\st -> (st, linenum st))

incLineNum :: P ()
incLineNum = P (\st -> (st{linenum = (linenum st) + 1}, ()))

resetLineNum :: P ()
resetLineNum = P (\st -> (st{linenum = 1}, ())) --after parsing primitives: lineNum is 1 again

getInput :: P String
getInput = P (\st -> (st, input st))

setInput :: String -> P ()
setInput s = P (\st -> (st{input = s}, ()))
{-
printState :: P ()
printState = do l <- getLineNum
		s <- getInput
		(unsafePerformIO $ putStr $ show ("ln: " ++ (show l) ++ " input: " ++ s))
		  `seq` return ()
-}
-- Like return, but update the pending input stream as well.
returnPI :: Tk -> String -> P Tk
returnPI t s = setInput s >> return t


