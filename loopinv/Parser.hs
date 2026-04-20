-- | Simple recursive descent parser for C subset
module Parser (parse) where

import AST
import Lexer

-- | Parse tokens into a program
parse :: [Token] -> Program
parse toks = Program (parseFuncs toks)

-- | Parse list of functions
parseFuncs :: [Token] -> [Func]
parseFuncs [TkEOF] = []
parseFuncs toks = 
    let (func, rest) = parseFunc toks
    in func : parseFuncs rest

-- | Parse a single function
parseFunc :: [Token] -> (Func, [Token])
parseFunc toks = 
    let (retType, toks1) = parseType toks
        (name, toks2) = parseIdent toks1
        toks3 = expect TkLParen toks2
        (params, toks4) = parseParams toks3
        toks5 = expect TkRParen toks4
        toks6 = expect TkLBrace toks5
        (body, toks7) = parseStmts toks6
        toks8 = expect TkRBrace toks7
    in (Func retType name params body, toks8)

-- | Parse type
parseType :: [Token] -> (Type, [Token])
parseType (TkInt : rest) = (TInt, rest)
parseType (TkVoid : rest) = (TVoid, rest)
parseType toks = error $ "Expected type, got: " ++ show (take 3 toks)

-- | Parse identifier
parseIdent :: [Token] -> (String, [Token])
parseIdent (TkIdent s : rest) = (s, rest)
parseIdent toks = error $ "Expected identifier, got: " ++ show (take 3 toks)

-- | Parse parameters
parseParams :: [Token] -> ([(Type, String)], [Token])
parseParams (TkRParen : _) = ([], TkRParen : drop 0 [])  -- empty params, put back RParen
parseParams toks = parseParams' toks
  where
    parseParams' ts =
        let (typ, ts1) = parseType ts
            (name, ts2) = parseIdent ts1
        in case ts2 of
            (TkComma : ts3) -> 
                let (rest, ts4) = parseParams' ts3
                in ((typ, name) : rest, ts4)
            _ -> ([(typ, name)], ts2)

-- | Parse list of statements until }
parseStmts :: [Token] -> ([Stmt], [Token])
parseStmts (TkRBrace : rest) = ([], TkRBrace : rest)  -- put back RBrace
parseStmts toks =
    let (stmt, rest) = parseStmt toks
        (stmts, rest') = parseStmts rest
    in (stmt : stmts, rest')

-- | Parse a single statement
parseStmt :: [Token] -> (Stmt, [Token])
-- Variable declaration: int x = expr; or int x;
parseStmt (TkInt : TkIdent name : TkAssign : rest) =
    let (expr, rest') = parseExpr rest
        rest'' = expect TkSemi rest'
    in (VarDecl TInt name (Just expr), rest'')
parseStmt (TkInt : TkIdent name : TkSemi : rest) =
    (VarDecl TInt name Nothing, rest)
-- While loop
parseStmt (TkWhile : TkLParen : rest) =
    let (cond, rest') = parseExpr rest
        rest'' = expect TkRParen rest'
        rest''' = expect TkLBrace rest''
        (body, rest4) = parseStmts rest'''
        rest5 = expect TkRBrace rest4
    in (While cond body, rest5)
-- If statement
parseStmt (TkIf : TkLParen : rest) =
    let (cond, rest') = parseExpr rest
        rest'' = expect TkRParen rest'
        rest''' = expect TkLBrace rest''
        (thenBody, rest4) = parseStmts rest'''
        rest5 = expect TkRBrace rest4
    in case rest5 of
        (TkElse : TkLBrace : rest6) ->
            let (elseBody, rest7) = parseStmts rest6
                rest8 = expect TkRBrace rest7
            in (If cond thenBody (Just elseBody), rest8)
        _ -> (If cond thenBody Nothing, rest5)
-- Return statement
parseStmt (TkReturn : TkSemi : rest) =
    (Return Nothing, rest)
parseStmt (TkReturn : rest) =
    let (expr, rest') = parseExpr rest
        rest'' = expect TkSemi rest'
    in (Return (Just expr), rest'')
-- Assignment: x = expr;
parseStmt (TkIdent name : TkAssign : rest) =
    let (expr, rest') = parseExpr rest
        rest'' = expect TkSemi rest'
    in (Assign name expr, rest'')
-- Expression statement
parseStmt toks =
    let (expr, rest) = parseExpr toks
        rest' = expect TkSemi rest
    in (ExprStmt expr, rest')

-- | Parse expression (with precedence)
parseExpr :: [Token] -> (Expr, [Token])
parseExpr = parseOr

-- | Parse || (lowest precedence)
parseOr :: [Token] -> (Expr, [Token])
parseOr toks =
    let (left, rest) = parseAnd toks
    in parseOr' left rest
  where
    parseOr' left (TkOr : rest) =
        let (right, rest') = parseAnd rest
        in parseOr' (BinOp Or left right) rest'
    parseOr' left rest = (left, rest)

-- | Parse &&
parseAnd :: [Token] -> (Expr, [Token])
parseAnd toks =
    let (left, rest) = parseComparison toks
    in parseAnd' left rest
  where
    parseAnd' left (TkAnd : rest) =
        let (right, rest') = parseComparison rest
        in parseAnd' (BinOp And left right) rest'
    parseAnd' left rest = (left, rest)

-- | Parse comparison operators
parseComparison :: [Token] -> (Expr, [Token])
parseComparison toks =
    let (left, rest) = parseAddSub toks
    in case rest of
        (TkLt : rest') -> let (right, rest'') = parseAddSub rest' in (BinOp Lt left right, rest'')
        (TkLe : rest') -> let (right, rest'') = parseAddSub rest' in (BinOp Le left right, rest'')
        (TkGt : rest') -> let (right, rest'') = parseAddSub rest' in (BinOp Gt left right, rest'')
        (TkGe : rest') -> let (right, rest'') = parseAddSub rest' in (BinOp Ge left right, rest'')
        (TkEqEq : rest') -> let (right, rest'') = parseAddSub rest' in (BinOp Eq left right, rest'')
        (TkNe : rest') -> let (right, rest'') = parseAddSub rest' in (BinOp Ne left right, rest'')
        _ -> (left, rest)

-- | Parse + and -
parseAddSub :: [Token] -> (Expr, [Token])
parseAddSub toks =
    let (left, rest) = parseMulDiv toks
    in parseAddSub' left rest
  where
    parseAddSub' left (TkPlus : rest) =
        let (right, rest') = parseMulDiv rest
        in parseAddSub' (BinOp Add left right) rest'
    parseAddSub' left (TkMinus : rest) =
        let (right, rest') = parseMulDiv rest
        in parseAddSub' (BinOp Sub left right) rest'
    parseAddSub' left rest = (left, rest)

-- | Parse * / %
parseMulDiv :: [Token] -> (Expr, [Token])
parseMulDiv toks =
    let (left, rest) = parseUnary toks
    in parseMulDiv' left rest
  where
    parseMulDiv' left (TkStar : rest) =
        let (right, rest') = parseUnary rest
        in parseMulDiv' (BinOp Mul left right) rest'
    parseMulDiv' left (TkSlash : rest) =
        let (right, rest') = parseUnary rest
        in parseMulDiv' (BinOp Div left right) rest'
    parseMulDiv' left (TkPercent : rest) =
        let (right, rest') = parseUnary rest
        in parseMulDiv' (BinOp Mod left right) rest'
    parseMulDiv' left rest = (left, rest)

-- | Parse unary operators
parseUnary :: [Token] -> (Expr, [Token])
parseUnary (TkMinus : rest) =
    let (expr, rest') = parseUnary rest
    in (UnaryOp Neg expr, rest')
parseUnary (TkNot : rest) =
    let (expr, rest') = parseUnary rest
    in (UnaryOp Not expr, rest')
parseUnary toks = parsePrimary toks

-- | Parse primary expressions
parsePrimary :: [Token] -> (Expr, [Token])
parsePrimary (TkNum n : rest) = (Lit n, rest)
parsePrimary (TkIdent name : TkLParen : rest) =
    -- Function call
    let (args, rest') = parseArgs rest
        rest'' = expect TkRParen rest'
    in (Call name args, rest'')
parsePrimary (TkIdent name : rest) = (Var name, rest)
parsePrimary (TkLParen : rest) =
    let (expr, rest') = parseExpr rest
        rest'' = expect TkRParen rest'
    in (expr, rest'')
parsePrimary toks = error $ "Expected expression, got: " ++ show (take 3 toks)

-- | Parse function arguments
parseArgs :: [Token] -> ([Expr], [Token])
parseArgs (TkRParen : rest) = ([], TkRParen : rest)  -- put back RParen
parseArgs toks = parseArgs' toks
  where
    parseArgs' ts =
        let (expr, ts') = parseExpr ts
        in case ts' of
            (TkComma : ts'') ->
                let (rest, ts''') = parseArgs' ts''
                in (expr : rest, ts''')
            _ -> ([expr], ts')

-- | Expect a specific token
expect :: Token -> [Token] -> [Token]
expect expected (tok : rest)
    | tok == expected = rest
    | otherwise = error $ "Expected " ++ show expected ++ ", got " ++ show tok
expect expected [] = error $ "Expected " ++ show expected ++ ", got EOF"



