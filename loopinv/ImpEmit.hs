-- | Emit AST as Imp language syntax
module ImpEmit (emitImp) where

import AST
import Data.List (intercalate)

-- | Convert program to Imp source code
emitImp :: Program -> String
emitImp (Program funcs) = 
    "#include \"Primitives.imp\"\n\n" ++
    intercalate "\n\n" (map emitFunc funcs)

-- | Emit a function
emitFunc :: Func -> String
emitFunc (Func retType name params body) =
    emitType retType ++ " " ++ name ++ "(" ++ emitParams params ++ ") {\n" ++
    emitStmts 1 body ++
    "}"

-- | Emit type
emitType :: Type -> String
emitType TInt = "int"
emitType TVoid = "void"

-- | Emit parameters
emitParams :: [(Type, String)] -> String
emitParams = intercalate ", " . map (\(t, n) -> emitType t ++ " " ++ n)

-- | Emit statements with indentation
emitStmts :: Int -> [Stmt] -> String
emitStmts indent stmts = 
    concatMap (emitStmt indent) (init' stmts) ++
    emitStmtLast indent (last' stmts)
  where
    -- All statements except last get semicolon
    init' [] = []
    init' xs = init xs
    -- Last statement has no trailing semicolon (Imp uses ; as separator)
    last' [] = Nothing
    last' xs = Just (last xs)

-- | Emit a statement (not the last one - includes semicolon separator)
emitStmt :: Int -> Stmt -> String
emitStmt indent stmt = emitStmtCore indent stmt ++ ";\n"

-- | Emit the last statement (no semicolon)
emitStmtLast :: Int -> Maybe Stmt -> String
emitStmtLast _ Nothing = ""
emitStmtLast indent (Just stmt) = emitStmtCore indent stmt ++ "\n"

-- | Emit statement core (without semicolon)
emitStmtCore :: Int -> Stmt -> String
emitStmtCore indent stmt = 
    let ind = replicate (indent * 2) ' '
    in case stmt of
        VarDecl typ name Nothing ->
            ind ++ emitType typ ++ " " ++ name ++ " := 0"  -- Imp needs initialization
        VarDecl typ name (Just expr) ->
            ind ++ emitType typ ++ " " ++ name ++ " := " ++ emitExpr expr
        Assign name expr ->
            ind ++ name ++ " := " ++ emitExpr expr
        While cond body ->
            ind ++ "while (" ++ emitExpr cond ++ ") do {\n" ++
            emitStmts (indent + 1) body ++
            ind ++ "}"
        If cond thenBody Nothing ->
            ind ++ "if " ++ emitExpr cond ++ " then {\n" ++
            emitStmts (indent + 1) thenBody ++
            ind ++ "} else { Void }"
        If cond thenBody (Just elseBody) ->
            ind ++ "if " ++ emitExpr cond ++ " then {\n" ++
            emitStmts (indent + 1) thenBody ++
            ind ++ "} else {\n" ++
            emitStmts (indent + 1) elseBody ++
            ind ++ "}"
        Return Nothing ->
            ind ++ "Void"
        Return (Just expr) ->
            ind ++ emitExpr expr
        ExprStmt expr ->
            ind ++ emitExpr expr

-- | Emit expression
emitExpr :: Expr -> String
emitExpr (Var name) = name
emitExpr (Lit n) = show n
emitExpr (BinOp op e1 e2) = 
    "(" ++ emitExpr e1 ++ " " ++ emitBinOp op ++ " " ++ emitExpr e2 ++ ")"
emitExpr (UnaryOp op e) = emitUnaryOp op ++ emitExpr e
emitExpr (Call name args) = 
    name ++ "(" ++ intercalate ", " (map emitExpr args) ++ ")"

-- | Emit binary operator
emitBinOp :: BinOp -> String
emitBinOp Add = "+"
emitBinOp Sub = "-"
emitBinOp Mul = "*"
emitBinOp Div = "/"
emitBinOp Mod = "%"
emitBinOp Lt  = "<"
emitBinOp Le  = "<="
emitBinOp Gt  = ">"
emitBinOp Ge  = ">="
emitBinOp Eq  = "="      -- Imp uses = for equality in expressions
emitBinOp Ne  = "<>"     -- Imp uses <> for not equal
emitBinOp And = "&&"
emitBinOp Or  = "||"

-- | Emit unary operator
emitUnaryOp :: UnaryOp -> String
emitUnaryOp Neg = "-"
emitUnaryOp Not = "!"



