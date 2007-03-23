{- | 
  Lists all the configuration flags.
-}

module ImpConfig(
  Flags(..),
  Hull(..), 
  Prederivation(..),
  Postcondition(..),
  Heur(..),
  FixFlags,
  defaultFlags,
  whatHull,
  noExistentialsInDisjuncts,
  useFixpoint2k
) where

data Hull = Hull | ConvexHull deriving Show
data Prederivation = WeakPD | StrongPD | SelectivePD | PostPD deriving (Show,Eq)
data Postcondition = StrongPost | WeakPost deriving (Show,Eq)
type FixFlags = (Int,Heur)
data Heur = SimilarityHeur | DifferenceHeur | HausdorffHeur deriving (Show,Eq)

data Flags = Flags {
  isIndirectionIntArray:: Bool, -- ^Collect constraints regarding Min and Max values of the array elements. Default is False.
  checkingAfterInference:: Bool,
  noInference:: Bool,
---- derive 2 stronger preconditions that need specialization for recursive functions
---- otherwise the resulting program may not type-check
  separateFstFromRec:: Bool,
  useAnnotatedFixpoint:: Bool, -- ^Use the annotated fixpoint where it is provided. Default is False.
  useSelectiveHull:: Bool, -- Old by the old fixpoint. Quicksort (Hanoi and Mergesort) require selectiveHull for precise result.
  widenEarly:: Bool, -- ^Used by the old fixpoint. Quicksort requires widenEarly for precise result.
  fixFlags:: FixFlags, -- ^Number of disjuncts (m) and heuristic function to compute disjunct affinity. Default is (5, Similarity).
  prederivation:: Prederivation, -- ^Kind of prederivation. Default is PostPD.
  postcondition:: Postcondition, -- ^Whether to accumulate preconditions in the computed postcondition. Default is True.
  outputFile:: String
} deriving Show

defaultFlags = Flags { 
  isIndirectionIntArray = False,
  checkingAfterInference = False,
  noInference = False,
  separateFstFromRec = False,
  useAnnotatedFixpoint = True, 
  useSelectiveHull = False,
  widenEarly = True, 
  fixFlags = (5,SimilarityHeur),
  prederivation = PostPD,
  postcondition = StrongPost, 
  outputFile = "a"
}


whatHull = Hull 
useFixpoint2k = True
noExistentialsInDisjuncts = True


