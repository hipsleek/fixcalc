-- | Simple lexer for C subset
module Lexer (Token(..), tokenize) where

import Data.Char (isAlpha, isAlphaNum, isDigit, isSpace)

-- | Tokens
data Token
  = TkInt | TkVoid                      -- types
  | TkWhile | TkIf | TkElse | TkReturn  -- keywords
  | TkIdent String                      -- identifier
  | TkNum Int                           -- number
  | TkPlus | TkMinus | TkStar | TkSlash | TkPercent  -- arithmetic
  | TkLt | TkLe | TkGt | TkGe | TkEqEq | TkNe       -- comparison
  | TkAnd | TkOr | TkNot                -- logical
  | TkAssign                            -- =
  | TkLParen | TkRParen                 -- ( )
  | TkLBrace | TkRBrace                 -- { }
  | TkSemi | TkComma                    -- ; ,
  | TkEOF
  deriving (Show, Eq)

-- | Tokenize a string
tokenize :: String -> [Token]
tokenize [] = [TkEOF]
tokenize s@(c:cs)
  | isSpace c = tokenize cs
  -- Skip single-line comments
  | take 2 s == "//" = tokenize (dropWhile (/= '\n') s)
  -- Skip multi-line comments
  | take 2 s == "/*" = tokenize (skipBlockComment (drop 2 s))
  -- Two-character operators
  | take 2 s == "<=" = TkLe : tokenize (drop 2 s)
  | take 2 s == ">=" = TkGe : tokenize (drop 2 s)
  | take 2 s == "==" = TkEqEq : tokenize (drop 2 s)
  | take 2 s == "!=" = TkNe : tokenize (drop 2 s)
  | take 2 s == "&&" = TkAnd : tokenize (drop 2 s)
  | take 2 s == "||" = TkOr : tokenize (drop 2 s)
  -- Single-character operators
  | c == '+' = TkPlus : tokenize cs
  | c == '-' = TkMinus : tokenize cs
  | c == '*' = TkStar : tokenize cs
  | c == '/' = TkSlash : tokenize cs
  | c == '%' = TkPercent : tokenize cs
  | c == '<' = TkLt : tokenize cs
  | c == '>' = TkGt : tokenize cs
  | c == '=' = TkAssign : tokenize cs
  | c == '!' = TkNot : tokenize cs
  | c == '(' = TkLParen : tokenize cs
  | c == ')' = TkRParen : tokenize cs
  | c == '{' = TkLBrace : tokenize cs
  | c == '}' = TkRBrace : tokenize cs
  | c == ';' = TkSemi : tokenize cs
  | c == ',' = TkComma : tokenize cs
  -- Numbers
  | isDigit c = let (num, rest) = span isDigit s
                in TkNum (read num) : tokenize rest
  -- Identifiers and keywords
  | isAlpha c || c == '_' = 
      let (ident, rest) = span isIdentChar s
      in keywordOrIdent ident : tokenize rest
  | otherwise = error $ "Unexpected character: " ++ [c]

-- | Check if character can be part of identifier
isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_'

-- | Convert identifier to keyword or keep as identifier
keywordOrIdent :: String -> Token
keywordOrIdent "int"    = TkInt
keywordOrIdent "void"   = TkVoid
keywordOrIdent "while"  = TkWhile
keywordOrIdent "if"     = TkIf
keywordOrIdent "else"   = TkElse
keywordOrIdent "return" = TkReturn
keywordOrIdent s        = TkIdent s

-- | Skip block comment (find closing */)
skipBlockComment :: String -> String
skipBlockComment [] = []
skipBlockComment s
  | take 2 s == "*/" = drop 2 s
  | otherwise = skipBlockComment (tail s)



