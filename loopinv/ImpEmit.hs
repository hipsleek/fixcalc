-- | Emit AST as Imp language syntax
module ImpEmit (emitImp) where

import AST
import Data.List (intercalate)

-- | Convert program to Imp source code
emitImp :: Program -> String
emitImp (Program funcs) = 
    "#include \"Primitives.imp\"\n\n" ++
    intercalate "\n\n" (map emitFunc funcs)

-- | Emit a function (with variable hoisting for imp tool compatibility)
emitFunc :: Func -> String
emitFunc (Func retType name params body) =
    let (hoisted, transformedBody) = hoistVarDecls body
    in emitType retType ++ " " ++ name ++ "(" ++ emitParams params ++ ") {\n" ++
       -- Emit hoisted declarations first (without initial value)
       concatMap (emitHoistedDecl 1) hoisted ++
       emitStmts 1 transformedBody ++
       "}"

-- | Emit a hoisted declaration (with default initialization - Imp requires it)
emitHoistedDecl :: Int -> (Type, String) -> String
emitHoistedDecl indent (typ, name) =
    replicate (indent * 2) ' ' ++ emitType typ ++ " " ++ name ++ " := 0;\n"

-- | Hoist variable declarations from inside loops to function level
-- Returns (hoisted declarations, transformed statements)
hoistVarDecls :: [Stmt] -> ([(Type, String)], [Stmt])
hoistVarDecls stmts = 
    let (hoisted, transformed) = unzip $ map hoistFromStmt stmts
    in (concat hoisted, transformed)

-- | Hoist from a single statement
hoistFromStmt :: Stmt -> ([(Type, String)], Stmt)
hoistFromStmt (While cond body) =
    let (hoisted, transformedBody) = hoistFromBody body
    in (hoisted, While cond transformedBody)
hoistFromStmt (If cond thenBody elseBody) =
    let (hoistedThen, transformedThen) = hoistFromBody thenBody
        (hoistedElse, transformedElse) = case elseBody of
            Just eb -> let (h, t) = hoistFromBody eb in (h, Just t)
            Nothing -> ([], Nothing)
    in (hoistedThen ++ hoistedElse, If cond transformedThen transformedElse)
hoistFromStmt stmt = ([], stmt)

-- | Hoist from body (inside a loop or if)
-- This is where we actually hoist - VarDecls become assignments
hoistFromBody :: [Stmt] -> ([(Type, String)], [Stmt])
hoistFromBody stmts = 
    let (hoisted, transformed) = unzip $ map hoistAndTransform stmts
    in (concat hoisted, concat transformed)

-- | Hoist a statement and transform VarDecl to Assign
hoistAndTransform :: Stmt -> ([(Type, String)], [Stmt])
hoistAndTransform (VarDecl typ name maybeExpr) =
    -- Hoist the declaration, keep assignment in place
    case maybeExpr of
        Just expr -> ([(typ, name)], [Assign name expr])
        Nothing -> ([(typ, name)], [Assign name (Lit 0)])
hoistAndTransform (While cond body) =
    let (hoisted, transformedBody) = hoistFromBody body
    in (hoisted, [While cond transformedBody])
hoistAndTransform (If cond thenBody elseBody) =
    let (hoistedThen, transformedThen) = hoistFromBody thenBody
        (hoistedElse, transformedElse) = case elseBody of
            Just eb -> let (h, t) = hoistFromBody eb in (h, Just t)
            Nothing -> ([], Nothing)
    in (hoistedThen ++ hoistedElse, [If cond transformedThen transformedElse])
hoistAndTransform stmt = ([], [stmt])

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



