module ImpConfig where

data Hull = Hull | ConvexHull deriving Show
data Prederivation = WeakPD | StrongPD | SelectivePD | PostPD deriving (Show,Eq)
data Postcondition = StrongPost | WeakPost deriving (Show,Eq)

data Heur = SimilarityHeur | DifferenceHeur | SyntacticHeur | HausdorffHeur deriving (Show,Eq)
type FixFlags = (Int,Heur)

data Flags = Flags {
  isIndirectionIntArray:: Bool,
  checkingAfterInference:: Bool,
  noInference:: Bool,
  separateFstFromRec:: Bool,
  useAnnotatedFixpoint:: Bool,
  useSelectiveHull:: Bool,
  widenEarly:: Bool,
  fixFlags:: (Int,Heur),
  prederivation:: Prederivation,
  postcondition:: Postcondition,
  outputFile:: String
} deriving Show

defaultFlags = Flags { 
---- True: collect constraints regarding Min and Max values of the array elements.
---- False: do not collect. As a consequence, functions are allowed to return values of array type.
  isIndirectionIntArray = False,
  checkingAfterInference = False,
  noInference = False,
---- derive 2 stronger preconditions that need specialization for recursive functions
---- otherwise the resulting program may not type-check
  separateFstFromRec = False,
  useAnnotatedFixpoint = True, --use the annotated fixpoint where it is provided.
  useSelectiveHull = False,-- Old fixpoint: Quicksort (Hanoi and Mergesort) require selectiveHull for precise result
  widenEarly = True, -- Old fixpoint: Quicksort requires widenEarly (and selHull) for precise result
  fixFlags = (5,SimilarityHeur),
  prederivation = PostPD,
  postcondition = StrongPost, -- StrongPost: accumulate preconditions of the callee in the postcondition of the caller
  outputFile = "a"
}
---- Fresh.hs
enableLog = True

---- ImpTypeInfer.hs
---- propagate False with no effort as recursive checks
noRecPreDerivation = False
whatHull = Hull

---- ImpFixpoint.hs
useTrueFixpoint = False -- replace the result of fixpoint: (Post,Inv) = (True,True)
pairwiseDuringFix = False


useFixpoint2k = True
--testSafetyChecks = True
noExistentialsInDisjuncts = True


