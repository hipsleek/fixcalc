-- | LoopInv: Build constraint abstractions and compute loop invariants via LFP
-- 
-- This tool:
-- 1. Converts C code to Imp syntax (constraint abstraction)
-- 2. Runs the imp tool which uses fixCalc to compute LFP
-- 3. Extracts disjuncts and outputs in prime notation
-- 4. Verifies if the LFP is exact (EX) or over-approximate (OX)
--
module Main where

import System.Environment (getArgs)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import System.FilePath (takeBaseName, takeDirectory, (</>))
import Data.List (isPrefixOf, isInfixOf, stripPrefix, partition)
import Data.Maybe (mapMaybe)
import Data.Char (isSpace)

import Lexer (tokenize)
import Parser (parse)
import AST (Program(..), Func(..), Stmt(..), Expr(..), BinOp(..), UnaryOp(..))
import ImpEmit (emitImp)

main :: IO ()
main = do
    args <- getArgs
    case args of
        [inputFile] -> processFile inputFile
        _ -> showHelp

showHelp :: IO ()
showHelp = do
    putStrLn "LoopInv - Loop Invariant Generator using fixCalc"
    putStrLn ""
    putStrLn "Usage: loopinv <input.c>"
    putStrLn ""
    putStrLn "This tool:"
    putStrLn "  1. Converts C code to Imp (constraint abstraction)"
    putStrLn "  2. Runs imp tool to compute loop invariants via LFP (fixCalc)"
    putStrLn "  3. Displays the computed result"

processFile :: FilePath -> IO ()
processFile inputFile = do
    putStrLn "================================================================"
    putStrLn "  LoopInv - Constraint Abstraction & LFP Computation"
    putStrLn "================================================================"
    putStrLn ""
    
    -- Step 1: Read and parse C code
    putStrLn $ "Input: " ++ inputFile
    putStrLn ""
    cCode <- readFile inputFile
    
    putStrLn "=== Original C Code ==="
    putStrLn cCode
    
    -- Step 2: Convert to Imp (constraint abstraction)
    putStrLn "=== Converting to Imp (Constraint Abstraction) ==="
    let tokens = tokenize cCode
    let ast = parse tokens
    let impCode = emitImp ast
    
    let impFile = takeDirectory inputFile </> takeBaseName inputFile ++ ".imp"
    writeFile impFile impCode
    putStrLn $ "Generated: " ++ impFile
    putStrLn ""
    putStrLn impCode
    
    -- Step 3: Run imp tool (which calls fixCalc for LFP)
    putStrLn "=== Running imp tool (LFP computation via fixCalc) ==="
    putStrLn ""
    
    let impBin = "./imp"
    (exitCode, stdout, stderr) <- readProcessWithExitCode impBin [impFile, "+infer"] ""
    
    case exitCode of
        ExitSuccess -> do
            putStrLn stdout
            
            -- Read and parse the LFP result
            imptContent <- readFile "a.impt"
            
            -- Extract variable mapping and LFP formula
            let varMapping = extractVarMapping imptContent
            let lfpFormula = extractLFP imptContent
            
            putStrLn "=== LFP Analysis ==="
            putStrLn ""
            putStrLn $ "Variable mapping: " ++ show varMapping
            putStrLn ""
            putStrLn $ "Raw LFP: " ++ lfpFormula
            putStrLn ""
            
            -- Convert to prime notation
            let primeFormula = toPrimeNotation varMapping lfpFormula
            putStrLn $ "Prime notation: " ++ primeFormula
            putStrLn ""
            
            -- Split into disjuncts
            let disjuncts = splitDisjuncts primeFormula
            putStrLn $ "=== Disjuncts (" ++ show (length disjuncts) ++ " cases) ==="
            putStrLn ""
            mapM_ (\(i, d) -> putStrLn $ "Case " ++ show i ++ ": " ++ d) (zip [1..] disjuncts)
            putStrLn ""
            
            -- Convert disjuncts to case format
            let cases = map disjunctToCase disjuncts
            putStrLn "=== Case Format (pre ens post) ==="
            putStrLn ""
            putStrLn "case {"
            mapM_ (\c -> putStrLn $ "  " ++ formatCaseClause c) cases
            putStrLn "}"
            putStrLn ""
            
            -- Step 4: Verify EX/OX (exactness check)
            putStrLn "=== Exactness Verification (EX/OX) ==="
            putStrLn ""
            
            -- Find the first while loop in the AST
            case findWhileLoop ast of
                Just (loopCond, loopBody, loopVars) -> do
                    -- Generate fixcalc verification query
                    let fcQuery = generateExactnessQuery loopCond loopBody loopVars primeFormula varMapping
                    let fcFile = "exactness_check.fc"
                    writeFile fcFile fcQuery
                    putStrLn $ "Generated verification query: " ++ fcFile
                    putStrLn ""
                    putStrLn "Query:"
                    putStrLn fcQuery
                    putStrLn ""
                    
                    -- Run fixcalc
                    (fcExit, fcOut, fcErr) <- readProcessWithExitCode "./fixcalc" [fcFile] ""
                    case fcExit of
                        ExitSuccess -> do
                            putStrLn "fixcalc output:"
                            putStrLn fcOut
                            -- Parse result to determine EX/OX
                            let result = parseExactnessResult fcOut
                            putStrLn ""
                            putStrLn $ "=== Result: " ++ result ++ " ==="
                            putStrLn ""
                            case result of
                                "EX" -> putStrLn "The LFP is EXACT - it precisely captures the loop's input-output relation."
                                "OX" -> putStrLn "The LFP is OVER-APPROXIMATE - it may include behaviors that cannot happen."
                                _ -> putStrLn "Could not determine exactness."
                        ExitFailure _ -> do
                            putStrLn $ "fixcalc error: " ++ fcErr
                            putStrLn fcOut
                Nothing -> do
                    putStrLn "No while loop found in AST for exactness verification."
            
        ExitFailure code -> do
            putStrLn $ "Error: imp tool failed with code " ++ show code
            putStrLn "stderr:"
            putStrLn stderr
            putStrLn "stdout:"
            putStrLn stdout

-- | Extract variable mapping from a.impt
-- Find the whilef function whose variables match the LFP formula
extractVarMapping :: String -> [(String, String)]
extractVarMapping content =
    let ls = lines content
        lfp = extractLFP content
        -- Find all whilef function definition lines (have Int<f_ pattern)
        whileLines = filter (\l -> "whilef_" `isInfixOf` l && "Int<f_" `isInfixOf` l && "ref Void" `isInfixOf` l) ls
        -- Get mappings from each and find the one that matches the LFP
        allMappings = map extractMappingsFromWhileLine whileLines
        -- Pick the mapping where variables appear in the LFP
        matchingMappings = filter (mappingMatchesLFP lfp) allMappings
    in case matchingMappings of
        (m:_) -> m
        [] -> case allMappings of
            (m:_) -> m  -- fallback to first mapping
            [] -> []

-- | Check if a variable mapping matches the LFP formula
mappingMatchesLFP :: String -> [(String, String)] -> Bool
mappingMatchesLFP lfp mapping = 
    -- Check if all internal variable names appear in the LFP
    all (\(internal, _) -> internal `isInfixOf` lfp) mapping

extractMappingsFromWhileLine :: String -> [(String, String)]
extractMappingsFromWhileLine line =
    -- Parse: ref Void whilef_0(ref Int<f_6f> x,ref Int<f_7f> n)
    -- Extract pairs like (f_6f, x), (f_7f, n)
    let -- Find content between ( and )
        afterParen = dropWhile (/= '(') line
        params = takeWhile (/= ')') (drop 1 afterParen)
        -- Split by comma
        paramList = splitByComma params
    in mapMaybe parseParam paramList

splitByComma :: String -> [String]
splitByComma s = map trim $ go s ""
  where
    go [] acc = [reverse acc]
    go (',':rest) acc = reverse acc : go rest ""
    go (c:rest) acc = go rest (c:acc)

parseParam :: String -> Maybe (String, String)
parseParam param =
    -- Parse: ref Int<f_6f> x
    let tokens = words param
        -- Find token with <f_...> and the next token is the var name
    in findMapping tokens

findMapping :: [String] -> Maybe (String, String)
findMapping [] = Nothing
findMapping [_] = Nothing
findMapping (t1:t2:rest)
    | "<f_" `isInfixOf` t1 =
        case extractInternalName t1 of
            Just internal -> Just (internal, t2)
            Nothing -> findMapping (t2:rest)
    | otherwise = findMapping (t2:rest)

extractInternalName :: String -> Maybe String
extractInternalName s =
    -- Extract f_Xf from something like "Int<f_6f>"
    case break (== '<') s of
        (_, '<':rest) -> 
            case break (== '>') rest of
                (internal, '>':_) -> Just internal
                _ -> Nothing
        _ -> Nothing

-- | Extract LFP formula from a.impt
-- Look for the where clause line that starts with ((( and contains PRMf_
extractLFP :: String -> String
extractLFP content =
    let ls = lines content
        -- Find lines that start with ((( and contain PRMf_ (the actual LFP formula)
        lfpLines = filter (\l -> "(((" `isPrefixOf` trim l && "PRMf_" `isInfixOf` l) ls
    in case lfpLines of
        (l:_) -> cleanLFP (trim l)
        [] -> ""

cleanLFP :: String -> String
cleanLFP s = 
    -- Remove trailing comma if present
    let s' = if not (null s) && last s == ',' then init s else s
    in s'

-- | Convert internal variable names to prime notation
-- f_Xf -> X (pre-state, unprimed)
-- PRMf_Xf -> X' (post-state, primed)
toPrimeNotation :: [(String, String)] -> String -> String
toPrimeNotation mapping formula =
    -- First replace PRMf_* with primed versions (do this first to avoid substring issues)
    let withPrimed = foldl (\f (internal, orig) -> replaceAll ("PRM" ++ internal) (orig ++ "'") f) formula mapping
    -- Then replace f_* with unprimed versions
    in foldl (\f (internal, orig) -> replaceAll internal orig f) withPrimed mapping

-- | Replace all occurrences of a substring
replaceAll :: String -> String -> String -> String
replaceAll old new str = go str
  where
    go [] = []
    go s@(c:cs)
        | old `isPrefixOf` s = new ++ go (drop (length old) s)
        | otherwise = c : go cs

-- | Split formula into disjuncts by ||
-- Handles nested parentheses correctly
splitDisjuncts :: String -> [String]
splitDisjuncts formula =
    let -- Remove outermost parentheses if present
        stripped = stripOuterParens (trim formula)
    in map trim $ splitByOr stripped 0 ""

stripOuterParens :: String -> String
stripOuterParens s
    | null s = s
    | head s == '(' && last s == ')' && isMatchingOuter s = stripOuterParens (init (tail s))
    | otherwise = s

-- | Check if the outer parens actually match each other (not just any open/close)
isMatchingOuter :: String -> Bool
isMatchingOuter s = 
    let inner = init (tail s)  -- remove first and last char
    in checkBalanced inner 0

checkBalanced :: String -> Int -> Bool
checkBalanced [] depth = depth == 0
checkBalanced ('(':rest) depth = checkBalanced rest (depth + 1)
checkBalanced (')':rest) depth 
    | depth > 0 = checkBalanced rest (depth - 1)
    | otherwise = False  -- unmatched close paren means outer parens don't match
checkBalanced (_:rest) depth = checkBalanced rest depth

-- | Split by || at depth 0 (respecting parentheses)
splitByOr :: String -> Int -> String -> [String]
splitByOr [] _ acc = [reverse acc]
splitByOr ('(':rest) depth acc = splitByOr rest (depth + 1) ('(':acc)
splitByOr (')':rest) depth acc = splitByOr rest (depth - 1) (')':acc)
splitByOr ('|':'|':rest) 0 acc = reverse acc : splitByOr rest 0 ""
splitByOr (c:rest) depth acc = splitByOr rest depth (c:acc)

-- | Trim whitespace from both ends
trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

-- ============================================================================
-- Case Format Conversion (disjunct -> pre ens post)
-- ============================================================================

-- | A case clause with preconditions and postconditions
data CaseClause = CaseClause
    { preConds :: [String]              -- Preconditions (unprimed constraints)
    , postAssigns :: [(String, String)] -- Post-assignments (var', value)
    , invariants :: [(String, String)]  -- Invariants (var', var) meaning unchanged
    , postConstraints :: [String]       -- Constraints on primed vars (not assignments)
    } deriving (Show)

-- | Convert a disjunct to a case clause
disjunctToCase :: String -> CaseClause
disjunctToCase disjunct =
    let conjuncts = splitConjuncts (stripOuterParens disjunct)
        -- First pass: find all equalities
        equalities = mapMaybe parseEquality conjuncts
        -- Find post-assignments: primed = unprimed (e.g., x' = n, x' = 0)
        postAssigns' = findPostAssignments equalities
        -- Find invariants: var' = var (unchanged) or derived
        invariants' = findInvariants equalities postAssigns'
        -- Find constraints (non-equalities)
        constraints = filter (not . isEquality) conjuncts
        -- Also get equalities that are constraints (primed on both sides, etc.)
        constraintEqualities = filter (isConstraintEquality postAssigns') equalities
        -- Substitute post-values into constraints
        allConstraints = constraints ++ map equalityToString constraintEqualities
        substituted = map (substituteAll postAssigns') allConstraints
        -- Separate into preconditions (unprimed) and post-constraints (still have primed)
        (preConds', postConstraints) = partition (not . containsPrimed) substituted
        -- Filter out trivial preconditions (like "true" or empty)
        validPreConds = filter isValidPrecond preConds'
        -- Post-constraints remain as constraints on primed variables (use different filter)
        validPostConstraints = filter isValidPostConstraint postConstraints
    in CaseClause validPreConds postAssigns' invariants' validPostConstraints

-- | Split a disjunct into conjuncts by && (recursively flattens)
splitConjuncts :: String -> [String]
splitConjuncts s = flattenConjuncts [stripOuterParens s]

-- | Recursively flatten conjuncts until no more && at top level
flattenConjuncts :: [String] -> [String]
flattenConjuncts parts =
    let split1 = concatMap splitOneLevel parts
        cleaned = map (trim . stripOuterParens) split1
    in if cleaned == parts then parts else flattenConjuncts cleaned

-- | Split by && at depth 0 (one level only)
splitOneLevel :: String -> [String]
splitOneLevel s = splitByAnd (stripOuterParens s) 0 ""

splitByAnd :: String -> Int -> String -> [String]
splitByAnd [] _ acc = [reverse acc]
splitByAnd ('(':rest) depth acc = splitByAnd rest (depth + 1) ('(':acc)
splitByAnd (')':rest) depth acc = splitByAnd rest (depth - 1) (')':acc)
splitByAnd ('&':'&':rest) 0 acc = reverse acc : splitByAnd rest 0 ""
splitByAnd (c:rest) depth acc = splitByAnd rest depth (c:acc)

-- | Parse an equality like "x' = n" or "0 = x'"
parseEquality :: String -> Maybe (String, String)
parseEquality s =
    let s' = trim s
    in case splitByEquals s' of
        [lhs, rhs] -> Just (trim lhs, trim rhs)
        _ -> Nothing

-- | Split by = (but not >= or <=)
splitByEquals :: String -> [String]
splitByEquals s = go s "" False
  where
    go [] acc _ = [reverse acc]
    go ('>':'=':rest) acc _ = go rest ('=':'>':acc) True
    go ('<':'=':rest) acc _ = go rest ('=':'<':acc) True
    go ('=':rest) acc False = reverse acc : go rest "" False
    go ('=':rest) acc True = go rest ('=':acc) False  -- reset flag after consuming
    go (c:rest) acc _ = go rest (c:acc) False

-- | Check if a string is an equality (contains = but not >= or <=)
isEquality :: String -> Bool
isEquality s = 
    let s' = removeComparisonOps s
    in '=' `elem` s' && not (">=" `isInfixOf` s) && not ("<=" `isInfixOf` s)

removeComparisonOps :: String -> String
removeComparisonOps [] = []
removeComparisonOps ('>':'=':rest) = removeComparisonOps rest
removeComparisonOps ('<':'=':rest) = removeComparisonOps rest
removeComparisonOps (c:rest) = c : removeComparisonOps rest

-- | Check if a variable is primed (ends with ')
isPrimed :: String -> Bool
isPrimed s = not (null s) && last s == '\''

-- | Get the unprimed version of a variable
unprime :: String -> String
unprime s = if isPrimed s then init s else s

-- | Check if an expression contains any primed variables
containsPrimed :: String -> Bool
containsPrimed s = '\'' `elem` s

-- | Find post-assignments: equalities where primed var = unprimed expr
findPostAssignments :: [(String, String)] -> [(String, String)]
findPostAssignments eqs = concatMap checkEquality eqs
  where
    checkEquality (lhs, rhs)
        -- x' = expr (expr is unprimed)
        | isPrimedVar lhs && not (containsPrimed rhs) = [(lhs, rhs)]
        -- expr = x' (expr is unprimed)  
        | isPrimedVar rhs && not (containsPrimed lhs) = [(rhs, lhs)]
        | otherwise = []
    
    isPrimedVar s = isPrimed s && isSimpleVar (unprime s)
    isSimpleVar s = all (\c -> c `elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ "_")) s

-- | Find invariants: var' = var (unchanged variables)
-- Also derive from chains like x' = n' and x' = n -> n' = n
-- Excludes variables already in post-assignments
findInvariants :: [(String, String)] -> [(String, String)] -> [(String, String)]
findInvariants eqs postAssigns' = 
    let -- Direct invariants: x' = x or x = x'
        direct = concatMap checkDirect eqs
        -- Derived: if x' = n' and x' = n, then n' = n
        derived = deriveInvariants eqs postAssigns'
        -- Normalize all to (primed, unprimed) form
        normalized = map normalizeInv (direct ++ derived)
        allInvs = nubBy sameInvariant normalized
        -- Filter out invariants for variables already in post-assignments
        postVars = map (unprime . fst) postAssigns'
    in filter (\(v, _) -> unprime v `notElem` postVars) allInvs
  where
    checkDirect (lhs, rhs)
        | isPrimed lhs && unprime lhs == rhs = [(lhs, rhs)]
        | isPrimed rhs && unprime rhs == lhs = [(rhs, lhs)]
        | otherwise = []
    
    -- Normalize invariant to (primed, unprimed) form
    normalizeInv (a, b)
        | isPrimed a && not (isPrimed b) = (a, b)
        | isPrimed b && not (isPrimed a) = (b, a)
        | otherwise = (a, b)  -- both primed or both unprimed, keep as is
    
    sameInvariant (a, _) (b, _) = unprime a == unprime b

-- | Derive invariants from equality chains
deriveInvariants :: [(String, String)] -> [(String, String)] -> [(String, String)]
deriveInvariants eqs postAssigns' =
    -- For each primed = primed equality, check if we can derive an invariant
    concatMap derive eqs
  where
    derive (lhs, rhs)
        | isPrimed lhs && isPrimed rhs =
            -- x' = n', check if x' = someVal in postAssigns
            case lookup lhs postAssigns' of
                Just val -> [(rhs, val)]  -- n' = val
                Nothing -> case lookup rhs postAssigns' of
                    Just val -> [(lhs, val)]
                    Nothing -> []
        | otherwise = []

-- | Check if an equality is a constraint (not a post-assignment or invariant or derived)
isConstraintEquality :: [(String, String)] -> (String, String) -> Bool
isConstraintEquality postAssigns' (lhs, rhs) =
    -- It's a constraint if it involves primed vars but isn't a post-assignment or invariant
    (containsPrimed lhs || containsPrimed rhs) &&
    not (isPostAssignment lhs rhs) &&
    not (isInvariant lhs rhs) &&
    not (isDerivedInvariant lhs rhs)
  where
    isPostAssignment l r = 
        (isPrimed l && not (containsPrimed r)) ||
        (isPrimed r && not (containsPrimed l))
    isInvariant l r =
        (isPrimed l && unprime l == r) ||
        (isPrimed r && unprime r == l)
    -- Check if this equality will be derived as an invariant (both sides have same base)
    isDerivedInvariant l r =
        isPrimed l && isPrimed r && 
        (any (\(pv, _) -> pv == l || pv == r) postAssigns')

equalityToString :: (String, String) -> String
equalityToString (lhs, rhs) = lhs ++ " = " ++ rhs

-- | Substitute all post-assignments into an expression
substituteAll :: [(String, String)] -> String -> String
substituteAll postAssigns' expr =
    foldl (\e (var, val) -> replaceAll var val e) expr postAssigns'

-- | Check if a precondition is valid (not trivial)
isValidPrecond :: String -> Bool
isValidPrecond s = 
    let s' = trim s
    in not (null s') && 
       s' /= "true" && 
       s' /= "0 = 0" &&
       not (containsPrimed s')  -- should not have primed vars after substitution

-- | Check if a post-constraint is valid (not trivial, must have primed vars, not an invariant)
isValidPostConstraint :: String -> Bool
isValidPostConstraint s =
    let s' = trim s
    in not (null s') && 
       s' /= "true" && 
       s' /= "0 = 0" &&
       containsPrimed s' &&  -- must have primed vars
       not (isInvariantString s')  -- not just "x = x'" or "x' = x"

-- | Check if a string represents an invariant (var = var' or var' = var)
isInvariantString :: String -> Bool
isInvariantString s =
    case splitByEquals s of
        [lhs, rhs] -> 
            let l = trim lhs
                r = trim rhs
            in (isPrimed l && unprime l == r) || (isPrimed r && unprime r == l)
        _ -> False

-- | Format a case clause as "pre ens post"
formatCaseClause :: CaseClause -> String
formatCaseClause (CaseClause pres posts invs postConstrs) =
    let preStr = if null pres then "true" else intercalate " && " pres
        -- Combine post-assignments and invariants, removing duplicates
        allAssigns = nubBy sameAssign (posts ++ invs)
        assignStrs = map formatAssign allAssigns
        -- Add post-constraints (inequalities on primed vars)
        allPostStrs = assignStrs ++ postConstrs
        postStr = if null allPostStrs 
                  then "true"
                  else intercalate " && " allPostStrs
    in preStr ++ " ens " ++ postStr
  where
    formatAssign (var, val) = var ++ " = " ++ val
    sameAssign (a, _) (b, _) = unprime a == unprime b

-- | Remove duplicates by a predicate
nubBy :: (a -> a -> Bool) -> [a] -> [a]
nubBy _ [] = []
nubBy eq (x:xs) = x : nubBy eq (filter (not . eq x) xs)

-- | Intercalate (join with separator)
intercalate :: String -> [String] -> String
intercalate _ [] = ""
intercalate _ [x] = x
intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs

-- ============================================================================
-- Exactness Verification (EX/OX)
-- ============================================================================

-- | Find the first while loop in the AST
-- Returns (condition, body, variables used)
findWhileLoop :: Program -> Maybe (Expr, [Stmt], [String])
findWhileLoop (Program funcs) = 
    case concatMap findInFunc funcs of
        (w:_) -> Just w
        [] -> Nothing
  where
    findInFunc (Func _ _ params body) = 
        let paramVars = map snd params
        in findInStmts paramVars body
    
    findInStmts vars stmts = concatMap (findInStmt vars) stmts
    
    findInStmt vars (While cond body) = 
        let bodyVars = collectVarsFromStmts body
            allVars = vars ++ bodyVars
        in [(cond, body, allVars)]
    findInStmt vars (If _ thenB maybeElse) = 
        findInStmts vars thenB ++ maybe [] (findInStmts vars) maybeElse
    findInStmt _ _ = []
    
    collectVarsFromStmts stmts = concatMap collectVarsFromStmt stmts
    collectVarsFromStmt (VarDecl _ name _) = [name]
    collectVarsFromStmt (Assign name _) = [name]
    collectVarsFromStmt (While _ body) = collectVarsFromStmts body
    collectVarsFromStmt (If _ thenB maybeElse) = 
        collectVarsFromStmts thenB ++ maybe [] collectVarsFromStmts maybeElse
    collectVarsFromStmt _ = []

-- | Generate fixcalc query to verify exactness
-- F = base ∪ (F ∘ step) => EX
-- F ⊃ base ∪ (F ∘ step) => OX
generateExactnessQuery :: Expr -> [Stmt] -> [String] -> String -> [(String, String)] -> String
generateExactnessQuery loopCond loopBody allVars lfpFormula varMapping =
    let -- Get the variables from the mapping (these are the actual loop variables)
        vars = map snd varMapping
        -- fixcalc uses P prefix for primed vars, _t suffix for temp vars
        primedVars = map ("P" ++) vars
        tempVars = map (++ "_t") vars
        
        -- Format variable lists for fixcalc
        varList = intercalate "," vars
        primedList = intercalate "," primedVars
        tempList = intercalate "," tempVars
        
        -- Convert LFP to fixcalc format (replace ' with P prefix)
        lfpFixcalc = convertToFixcalcFormat lfpFormula vars
        
        -- Generate condition expression
        condExpr = exprToFixcalc loopCond
        negCondExpr = "!(" ++ condExpr ++ ")"
        
        -- Generate step relation from loop body
        stepExpr = generateStepExpr loopBody vars tempVars
        
        -- Build the identity assignments for base case (Px = x)
        identityAssigns = intercalate " && " [("P" ++ v) ++ " = " ++ v | v <- vars]
        
        -- Build combined condition inline (since fixcalc doesn't have union)
        baseCondition = "(" ++ negCondExpr ++ " && " ++ identityAssigns ++ ")"
        stepCondition = "(" ++ condExpr ++ " && " ++ stepExpr ++ ")"
        -- Composition: exists temp vars such that step and F hold
        compositionCondition = "exists(" ++ tempList ++ ": " ++ stepCondition ++ " && " ++ lfpFixcalc ++ ")"
        -- Replace vars with temp vars in LFP for composition
        lfpWithTemp = convertVarsToTemp lfpFormula vars tempVars
        compositionCondition2 = "exists(" ++ tempList ++ ": " ++ stepCondition ++ " && " ++ lfpWithTemp ++ ")"
        
        -- Build the query
    in unlines
        [ "# Exactness verification for loop LFP"
        , "# Variables: " ++ varList
        , ""
        , "# Computed LFP from imp tool"
        , "F := {[" ++ varList ++ "," ++ primedList ++ "]: " ++ lfpFixcalc ++ "};"
        , ""
        , "# Combined: base || (exists temp. step && F(temp, post))"
        , "# Base: condition false, vars unchanged"  
        , "# Step+Compose: condition true, one iteration, then F"
        , "combined := {[" ++ varList ++ "," ++ primedList ++ "]: "
        , "  " ++ baseCondition
        , "  || " ++ compositionCondition2
        , "};"
        , ""
        , "# Exactness check: F = combined iff both subset checks pass"
        , "F subset combined;"
        , "combined subset F;"
        ]

-- | Convert prime notation to fixcalc format
-- x' -> Px, n' -> Pn, etc.
convertToFixcalcFormat :: String -> [String] -> String
convertToFixcalcFormat formula vars =
    let -- Replace x' with Px for each variable
        withPrimed = foldl (\f v -> replaceAll (v ++ "'") ("P" ++ v) f) formula vars
        -- Replace == with =
        cleaned = replaceAll "==" "=" withPrimed
    in cleaned

-- | Convert vars to temp vars for composition
-- In F(temp, post), the unprimed vars become temp vars
-- x -> x_t, but Px stays as Px
convertVarsToTemp :: String -> [String] -> [String] -> String
convertVarsToTemp formula vars tempVars =
    let -- First convert to fixcalc format (x' -> Px)
        fixcalc = convertToFixcalcFormat formula vars
        -- Then replace unprimed vars with temp vars
        -- Need to be careful not to replace inside "Px"
        -- Do this by first marking primed, then replacing, then unmarking
        marked = foldl (\f v -> replaceAll ("P" ++ v) ("__PRIMED_" ++ v ++ "__") f) fixcalc vars
        withTemp = foldl (\f (v, tv) -> replaceWholeWord v tv f) marked (zip vars tempVars)
        unmarked = foldl (\f v -> replaceAll ("__PRIMED_" ++ v ++ "__") ("P" ++ v) f) withTemp vars
    in unmarked

-- | Replace whole word only (not as part of another word)
replaceWholeWord :: String -> String -> String -> String
replaceWholeWord old new str = go str
  where
    go [] = []
    go s@(c:cs)
        | old `isPrefixOf` s && not (isVarChar (safeLast (take (length str - length s) str))) && not (isVarChar (safeHead (drop (length old) s))) = 
            new ++ go (drop (length old) s)
        | otherwise = c : go cs
    
    isVarChar c = c `elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ "_")
    safeLast [] = ' '
    safeLast xs = last xs
    safeHead [] = ' '
    safeHead (x:_) = x

-- | Convert AST expression to fixcalc format
exprToFixcalc :: Expr -> String
exprToFixcalc (Var v) = v
exprToFixcalc (Lit n) = show n
exprToFixcalc (BinOp op e1 e2) = 
    let s1 = exprToFixcalc e1
        s2 = exprToFixcalc e2
    in case op of
        Add -> "(" ++ s1 ++ " + " ++ s2 ++ ")"
        Sub -> "(" ++ s1 ++ " - " ++ s2 ++ ")"
        Mul -> "(" ++ s1 ++ " * " ++ s2 ++ ")"
        Div -> "(" ++ s1 ++ " / " ++ s2 ++ ")"
        Mod -> "(" ++ s1 ++ " % " ++ s2 ++ ")"
        Lt  -> "(" ++ s1 ++ " < " ++ s2 ++ ")"
        Le  -> "(" ++ s1 ++ " <= " ++ s2 ++ ")"
        Gt  -> "(" ++ s1 ++ " > " ++ s2 ++ ")"
        Ge  -> "(" ++ s1 ++ " >= " ++ s2 ++ ")"
        Eq  -> "(" ++ s1 ++ " = " ++ s2 ++ ")"
        Ne  -> "(" ++ s1 ++ " != " ++ s2 ++ ")"
        And -> "(" ++ s1 ++ " && " ++ s2 ++ ")"
        Or  -> "(" ++ s1 ++ " || " ++ s2 ++ ")"
exprToFixcalc (UnaryOp op e) =
    let s = exprToFixcalc e
    in case op of
        Neg -> "(-" ++ s ++ ")"
        Not -> "(!(" ++ s ++ "))"
exprToFixcalc (Call _ _) = "true"  -- Function calls not supported, assume true

-- | Generate step expression from loop body (one iteration)
-- vars: original variable names (x, n)
-- tempVars: temp variable names (x_t, n_t)
generateStepExpr :: [Stmt] -> [String] -> [String] -> String
generateStepExpr stmts vars tempVars =
    let -- Find all assignments in the body
        assigns = collectAssigns stmts
        -- Create var -> tempVar mapping
        varToTemp = zip vars tempVars
        -- For each variable, determine its new value
        -- Variables not assigned keep their value
        stepParts = map (varStep assigns varToTemp) (zip vars tempVars)
    in intercalate " && " stepParts
  where
    varStep assigns varToTemp (v, tv) =
        case lookup v assigns of
            Just expr -> tv ++ " = " ++ exprToFixcalc expr
            Nothing -> tv ++ " = " ++ v  -- unchanged
    
    collectAssigns :: [Stmt] -> [(String, Expr)]
    collectAssigns = concatMap collectFromStmt
    
    collectFromStmt (Assign v e) = [(v, e)]
    collectFromStmt (VarDecl _ v (Just e)) = [(v, e)]
    collectFromStmt (While _ body) = collectAssigns body  -- nested loops
    collectFromStmt (If _ thenB maybeElse) = 
        collectAssigns thenB ++ maybe [] collectAssigns maybeElse
    collectFromStmt _ = []

-- | Parse fixcalc output to determine EX or OX
parseExactnessResult :: String -> String
parseExactnessResult output =
    let ls = lines output
        -- Look for the two subset check results
        -- fixcalc outputs "True" or "False" for subset checks
        results = filter isResultLine ls
        -- We need both "True" for EX
    in if length results >= 2
       then let r1 = "true" `isInfixOf` (map toLower (results !! 0))
                r2 = "true" `isInfixOf` (map toLower (results !! 1))
            in if r1 && r2 then "EX" else "OX"
       else "UNKNOWN"
  where
    isResultLine l = "true" `isInfixOf` map toLower l || "false" `isInfixOf` map toLower l
    toLower c = if c >= 'A' && c <= 'Z' then toEnum (fromEnum c + 32) else c
