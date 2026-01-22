-- | Simple AST for C subset (loops, assignments, basic expressions)
module AST where

-- | A program is a list of functions
data Program = Program [Func]
  deriving (Show, Eq)

-- | Function definition
data Func = Func {
    funcRetType :: Type,
    funcName    :: String,
    funcParams  :: [(Type, String)],
    funcBody    :: [Stmt]
  }
  deriving (Show, Eq)

-- | Types we support
data Type = TInt | TVoid
  deriving (Show, Eq)

-- | Statements
data Stmt
  = VarDecl Type String (Maybe Expr)    -- int x = 0;
  | Assign String Expr                   -- x = expr;
  | While Expr [Stmt]                    -- while (cond) { body }
  | If Expr [Stmt] (Maybe [Stmt])        -- if (cond) { } else { }
  | Return (Maybe Expr)                  -- return expr;
  | ExprStmt Expr                        -- expr;
  deriving (Show, Eq)

-- | Expressions
data Expr
  = Var String                           -- variable
  | Lit Int                              -- integer literal
  | BinOp BinOp Expr Expr               -- e1 op e2
  | UnaryOp UnaryOp Expr                -- op e
  | Call String [Expr]                   -- func(args)
  deriving (Show, Eq)

-- | Binary operators
data BinOp
  = Add | Sub | Mul | Div | Mod         -- arithmetic
  | Lt | Le | Gt | Ge | Eq | Ne         -- comparison
  | And | Or                             -- logical
  deriving (Show, Eq)

-- | Unary operators
data UnaryOp = Neg | Not
  deriving (Show, Eq)



