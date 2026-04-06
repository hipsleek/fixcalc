{-# OPTIONS_GHC -w #-}
{-# OPTIONS -XMagicHash -XBangPatterns -XTypeSynonymInstances -XFlexibleInstances -cpp #-}
#if __GLASGOW_HASKELL__ >= 710
{-# OPTIONS_GHC -XPartialTypeSignatures #-}
#endif
module FixCalcParser where
import ImpAST
import ImpConfig(defaultFlags,Flags(..),Heur(..))
import ImpFixpoint2k(bottomUp2k,bottomUp2k_gen,bottomUp_mr,topDown2k,gfp2k,subrec_z)
import ImpFixpoint2k(subrec_z_mut,subrec_gen,combSelHull,getDisjuncts,widen)
import ImpHullWiden(narrow)
import ImpFixpoint2k(fixTestBU,fixTestTD,getOneStep,getEq,pickEqFromEq)
import ImpFixpoint2k(pickGEQfromEQ,fixTestBU_Lgen,satEQfromEQ,satGEQfromEQ)
import ImpFormula(simplify,subset,difference,complement,pairwiseCheck,hull,apply,debugApply)
import Fresh
import FixCalcLexer(runP,P(..),Tk(..),lexer,getLineNum,getInput)
import MyPrelude
------------------------------------------
import Data.List(nub,elemIndex,transpose)
import Data.Maybe(fromJust)
import Control.Monad(foldM)
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import qualified GHC.Exts as Happy_GHC_Exts
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.1.1

newtype HappyAbsSyn t12 t19 t20 = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
newtype HappyWrap4 = HappyWrap4 ([RelEnv -> FS RelEnv])
happyIn4 :: ([RelEnv -> FS RelEnv]) -> (HappyAbsSyn t12 t19 t20)
happyIn4 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap4 x)
{-# INLINE happyIn4 #-}
happyOut4 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap4
happyOut4 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut4 #-}
newtype HappyWrap5 = HappyWrap5 (RelEnv -> FS RelEnv)
happyIn5 :: (RelEnv -> FS RelEnv) -> (HappyAbsSyn t12 t19 t20)
happyIn5 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap5 x)
{-# INLINE happyIn5 #-}
happyOut5 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap5
happyOut5 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut5 #-}
newtype HappyWrap6 = HappyWrap6 (RelEnv -> FS [Value])
happyIn6 :: (RelEnv -> FS [Value]) -> (HappyAbsSyn t12 t19 t20)
happyIn6 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap6 x)
{-# INLINE happyIn6 #-}
happyOut6 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap6
happyOut6 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut6 #-}
newtype HappyWrap7 = HappyWrap7 (RelEnv -> FS RelEnv)
happyIn7 :: (RelEnv -> FS RelEnv) -> (HappyAbsSyn t12 t19 t20)
happyIn7 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap7 x)
{-# INLINE happyIn7 #-}
happyOut7 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap7
happyOut7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut7 #-}
newtype HappyWrap8 = HappyWrap8 (RelEnv -> FS Value)
happyIn8 :: (RelEnv -> FS Value) -> (HappyAbsSyn t12 t19 t20)
happyIn8 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap8 x)
{-# INLINE happyIn8 #-}
happyOut8 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap8
happyOut8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut8 #-}
newtype HappyWrap9 = HappyWrap9 (RelEnv -> [RecPost])
happyIn9 :: (RelEnv -> [RecPost]) -> (HappyAbsSyn t12 t19 t20)
happyIn9 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap9 x)
{-# INLINE happyIn9 #-}
happyOut9 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap9
happyOut9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut9 #-}
newtype HappyWrap10 = HappyWrap10 ([Lit])
happyIn10 :: ([Lit]) -> (HappyAbsSyn t12 t19 t20)
happyIn10 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap10 x)
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap10
happyOut10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut10 #-}
newtype HappyWrap11 = HappyWrap11 ([Int])
happyIn11 :: ([Int]) -> (HappyAbsSyn t12 t19 t20)
happyIn11 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap11 x)
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap11
happyOut11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut11 #-}
happyIn12 :: t12 -> (HappyAbsSyn t12 t19 t20)
happyIn12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn12 #-}
happyOut12 :: (HappyAbsSyn t12 t19 t20) -> t12
happyOut12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut12 #-}
newtype HappyWrap13 = HappyWrap13 (Formula)
happyIn13 :: (Formula) -> (HappyAbsSyn t12 t19 t20)
happyIn13 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap13 x)
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap13
happyOut13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut13 #-}
newtype HappyWrap14 = HappyWrap14 ((Formula,[[Update]]))
happyIn14 :: ((Formula,[[Update]])) -> (HappyAbsSyn t12 t19 t20)
happyIn14 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap14 x)
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap14
happyOut14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut14 #-}
newtype HappyWrap15 = HappyWrap15 ((Formula,[[Update]]))
happyIn15 :: ((Formula,[[Update]])) -> (HappyAbsSyn t12 t19 t20)
happyIn15 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap15 x)
{-# INLINE happyIn15 #-}
happyOut15 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap15
happyOut15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut15 #-}
newtype HappyWrap16 = HappyWrap16 (Tk)
happyIn16 :: (Tk) -> (HappyAbsSyn t12 t19 t20)
happyIn16 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap16 x)
{-# INLINE happyIn16 #-}
happyOut16 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap16
happyOut16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut16 #-}
newtype HappyWrap17 = HappyWrap17 ([[Update]])
happyIn17 :: ([[Update]]) -> (HappyAbsSyn t12 t19 t20)
happyIn17 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap17 x)
{-# INLINE happyIn17 #-}
happyOut17 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap17
happyOut17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut17 #-}
newtype HappyWrap18 = HappyWrap18 ([Update])
happyIn18 :: ([Update]) -> (HappyAbsSyn t12 t19 t20)
happyIn18 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap18 x)
{-# INLINE happyIn18 #-}
happyOut18 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap18
happyOut18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut18 #-}
happyIn19 :: t19 -> (HappyAbsSyn t12 t19 t20)
happyIn19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn19 #-}
happyOut19 :: (HappyAbsSyn t12 t19 t20) -> t19
happyOut19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut19 #-}
happyIn20 :: t20 -> (HappyAbsSyn t12 t19 t20)
happyIn20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn20 #-}
happyOut20 :: (HappyAbsSyn t12 t19 t20) -> t20
happyOut20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut20 #-}
newtype HappyWrap21 = HappyWrap21 (QSizeVar)
happyIn21 :: (QSizeVar) -> (HappyAbsSyn t12 t19 t20)
happyIn21 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap21 x)
{-# INLINE happyIn21 #-}
happyOut21 :: (HappyAbsSyn t12 t19 t20) -> HappyWrap21
happyOut21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut21 #-}
happyInTok :: (Tk) -> (HappyAbsSyn t12 t19 t20)
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn t12 t19 t20) -> (Tk)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyExpList :: HappyAddr
happyExpList = HappyA# "\x00\x00\x20\x80\x02\x00\xdc\xbf\x7f\x00\x00\x20\x80\x02\x00\xdc\xbf\x7f\x00\x00\x20\x80\x02\x00\xdc\xbf\x7f\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x68\x00\x00\x60\x40\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\xe0\x8d\x00\xe0\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x80\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x80\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x06\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf0\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf8\x01\x00\x00\x00\x00\x00\x00\x06\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x10\x03\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x60\x00\x00\x00\x00\x00\x00\x00\x00\xe0\x0d\x00\xe0\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x20\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x02\x00\xd8\xbd\x79\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x40\x40\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\xe0\x0d\x00\xe0\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x03\x00\x00\x00\x00\x00\x10\x00\x06\x00\x00\x00\x00\x00\x00\x16\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x60\x0c\x00\x00\x00\x00\x00\x00\x00\x60\x0c\x00\x00\x00\x00\x00\x00\x00\x60\x0c\x00\x00\x00\x00\x00\x00\x00\x60\x0c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x60\x0c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe0\x0d\x00\xe0\x00\x00\x00\x00\x00\xe0\x0d\x00\xe0\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x60\x0c\x00\x00\x00\x00\x00\x00\x00\x00\x06\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x03\x00\x00\x00\x00\x00\x10\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x08\x00\x00\x00\x00\x00\x00\x10\x00\x06\x00\x00\x00\x00\x00\x00\x00\x08\x08\x00\x00\x00\x00\x00\x00\x00\x08\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0c\x12\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\xe0\x0d\x00\xe0\x00\x00\x00\x00\x00\xe0\x0d\x00\xe0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\xe0\x0d\x00\xe0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x16\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x06\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x06\x00\x00\x00\x00\x00\x00\x10\x00\x06\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\xe0\x0d\x00\xe0\x00\x00\x00\x00\x00\x00\x00\x04\x06\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_parseCalc","LCommand","Command","ParseFormula1","ParseFormula2","ParseFormula","Llit","Llit2","LInt","Formula","QFormula","LBExpr","BExpr","RelOp","LAExpr","AExpr","LPorUSizeVar","LPorUSizeVar1","PorUSizeVar","lit","intNum","true","false","'+'","'-'","'('","')'","';'","':='","'['","']'","'{'","'}'","','","'='","'<'","'>'","'>='","'<='","'&&'","'||'","':'","'.'","'!'","exists","forall","prime","rec","apply","widen","narrow","subset","complement","bottomup","bottomup_mr","bottomup_gen","topdown","gfp","selhull","manualhull","intersection","pairwisecheck","hull","fixtestpost","fixtestinv","pickEqFromEq","pickGEqFromEq","SatEQfromEQ","SatGEQfromEQ","%eof"]
        bit_start = st Prelude.* 72
        bit_end = (st Prelude.+ 1) Prelude.* 72
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..71]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\x01\x00\x01\x00\x01\x00\x06\x00\x0a\x00\x22\x00\x41\x00\x09\x00\x02\x00\x17\x00\x38\x00\x3c\x00\x57\x00\x4d\x00\x71\x00\x85\x00\x8f\x00\x99\x00\xa3\x00\xa9\x00\x6e\x00\xc7\x00\xb3\x00\xc6\x00\xf0\x00\x07\x01\x08\x01\x09\x01\xca\x00\xc9\x00\xdf\x00\xff\x00\x10\x01\x11\x01\x0a\x01\x00\x00\x00\x00\x12\x01\x4b\x00\x0b\x01\x13\x01\x0c\x01\x17\x01\x18\x01\x00\x00\x19\x01\x56\x00\x14\x01\x47\x00\x00\x00\xd3\x00\x00\x00\xc8\x00\xd9\x00\x00\x00\x42\x00\x1a\x01\x00\x00\x00\x00\x80\x00\x4c\x00\x1a\x01\x15\x01\x16\x01\x1b\x01\x1c\x01\x0f\x01\x69\x00\x00\x00\x15\x00\x1f\x01\x20\x01\x22\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1d\x01\x1e\x01\x2f\x00\x23\x01\x24\x01\x25\x01\x26\x01\x27\x01\x28\x01\x21\x01\x2f\x01\x2f\x01\x29\x01\x30\x01\x30\x01\x4c\x00\x2a\x01\x2b\x01\x00\x00\xc5\x00\xff\xff\xf9\x00\x00\x00\x31\x01\x00\x00\x31\x01\x33\x01\x00\x00\x00\x00\xcf\x00\xcf\x00\xcf\x00\xcf\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xcf\x00\x00\x00\x4c\x00\x4c\x00\x34\x01\x2c\x01\x36\x01\x2d\x01\x2e\x01\x32\x01\x37\x01\x35\x01\x38\x01\x39\x01\x3d\x01\x3a\x01\x3e\x01\x3b\x01\x3f\x01\x43\x01\x44\x01\x45\x01\x00\x00\x00\x00\x00\x00\x00\x00\x41\x01\x42\x01\x46\x01\x47\x01\x4d\x01\x48\x01\x49\x01\x4e\x01\x4a\x01\x51\x01\x53\x01\x56\x01\x4f\x01\x58\x01\x50\x01\x4b\x01\x00\x00\x52\x01\xcf\x00\x03\x01\x52\x01\x00\x00\x00\x00\x97\x00\x6f\x00\x00\x00\x00\x00\x00\x00\x59\x01\xfb\xff\x03\x00\x2b\x00\x55\x00\xf2\xff\x00\x00\x57\x01\x00\x00\x5c\x01\x5d\x01\x5e\x01\x61\x01\x63\x01\x64\x01\x00\x00\x00\x00\x5f\x01\x60\x01\x62\x01\x65\x01\x5a\x01\x3c\x01\x67\x01\x68\x01\x4c\x00\x4c\x00\x00\x00\x54\x01\x4c\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf9\x00\x66\x01\x69\x01\x6a\x01\x6b\x01\x6c\x01\x6e\x01\x6d\x01\x6f\x01\x70\x01\x71\x01\x72\x01\x73\x01\x75\x01\x74\x01\x77\x01\x7b\x01\x7a\x01\x7c\x01\x78\x01\x7e\x01\x85\x01\x7f\x01\x00\x00\x8a\x01\x81\x01\x00\x00\x8c\x01\x8d\x01\x84\x01\x8f\x01\x86\x01\xb6\x00\x87\x01\x53\x00\x58\x00\x88\x01\x89\x01\x00\x00\x8b\x01\x00\x00\x00\x00\x00\x00\x00\x00\x94\x01\x00\x00\x00\x00\x96\x01\x00\x00\x97\x01\x91\x01\x99\x01\x93\x01\x95\x01\x9a\x01\x98\x01\x9c\x01\x9b\x01\x9d\x01\x9d\x01\x9e\x01\xa0\x01\x00\x00\x9f\x01\x00\x00\x00\x00\xa1\x01\x00\x00\xa2\x01\x00\x00\xa3\x01\x00\x00\x00\x00\xa4\x01\x00\x00\xa5\x01\xa6\x01\xa7\x01\xac\x01\x40\x01\xad\x01\xa8\x01\xa9\x01\xaa\x01\xab\x01\xae\x01\xb2\x01\xb1\x01\xbc\x01\xbd\x01\xb4\x01\x00\x00\x90\x01\x00\x00\xb5\x01\xc0\x01\xba\x01\xbb\x01\xc3\x01\x00\x00\xb9\x01\x00\x00\x00\x00\xbe\x01\xc5\x01\xbf\x01\xc1\x01\xc4\x01\x00\x00\x00\x00\x0d\x01\x4c\x00\xb9\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\xe8\x00\xf8\x00\xed\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc2\x01\x68\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc6\x01\x00\x00\xc7\x01\x00\x00\x00\x00\x00\x00\x5b\x01\x00\x00\x00\x00\xb6\x01\x72\x00\xc3\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x79\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc8\x01\xc9\x01\x00\x00\xad\x00\xfa\x00\x7c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xca\x01\x00\x00\xfc\x00\x00\x00\x00\x00\x00\x00\x7a\x00\x84\x00\xe5\x00\x8e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe7\x00\x00\x00\x86\x00\x90\x00\xcb\x01\x00\x00\xce\x01\x00\x00\x00\x00\x00\x00\xd0\x01\x00\x00\xd1\x01\x00\x00\xd2\x01\x00\x00\xd3\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x98\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xcc\x01\x00\x00\x00\x00\x00\x00\x00\x00\xd5\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x9a\x00\xa4\x00\x00\x00\x00\x00\xae\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd7\x01\x00\x00\x00\x00\x00\x00\xd8\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd4\x01\x00\x00\x00\x00\xf3\x00\x00\x00\xda\x01\x00\x00\xdb\x01\x00\x00\x00\x00\xdc\x01\x00\x00\xdd\x01\x00\x00\xde\x01\xdf\x01\x00\x00\xe1\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe2\x01\x00\x00\x00\x00\xe3\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf6\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb8\x00\x00\x00\x00\x00\x00\x00"#

happyAdjustOffset :: Happy_GHC_Exts.Int# -> Happy_GHC_Exts.Int#
happyAdjustOffset off = off

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\xfd\xff\x00\x00\xfd\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd7\xff\xd6\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xdd\xff\x00\x00\x00\x00\x00\x00\x00\x00\xcf\xff\xc9\xff\xc5\xff\x00\x00\xbb\xff\xb3\xff\xad\xff\xb5\xff\xcb\xff\xca\xff\x00\x00\x00\x00\xb1\xff\x00\x00\x00\x00\x00\x00\x00\x00\xd3\xff\x00\x00\xf4\xff\x00\x00\x00\x00\x00\x00\x00\x00\xf8\xff\xfb\xff\xf9\xff\xfe\xff\xd8\xff\xde\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb0\xff\xae\xff\xad\xff\x00\x00\xbb\xff\xb2\xff\xb4\xff\xb7\xff\x00\x00\x00\x00\xac\xff\xab\xff\x00\x00\x00\x00\x00\x00\x00\x00\xc1\xff\xbd\xff\xbf\xff\xc0\xff\xbe\xff\x00\x00\xe7\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe8\xff\xea\xff\xec\xff\xee\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd5\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xcc\xff\xcd\xff\xc3\xff\x00\x00\xbc\xff\xc2\xff\xb9\xff\xba\xff\xaa\xff\x00\x00\xb6\xff\xb8\xff\xce\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd2\xff\x00\x00\xe4\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xfc\xff\xf5\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc6\xff\x00\x00\x00\x00\xaf\xff\xc4\xff\xa9\xff\xa8\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd1\xff\x00\x00\x00\x00\x00\x00\xd4\xff\x00\x00\x00\x00\xe1\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xfa\xff\x00\x00\xe9\xff\xeb\xff\xed\xff\xef\xff\x00\x00\xc7\xff\xc8\xff\xb1\xff\xe6\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf6\xff\x00\x00\xdb\xff\xd0\xff\x00\x00\xdc\xff\x00\x00\xe0\xff\x00\x00\xe2\xff\xda\xff\x00\x00\xd9\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf2\xff\x00\x00\xe3\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf7\xff\x00\x00\xdf\xff\xf3\xff\x00\x00\xb1\xff\x00\x00\x00\x00\x00\x00\xf1\xff\xf0\xff\x00\x00\x00\x00\x00\x00\xe5\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x06\x00\x01\x00\x01\x00\x02\x00\x03\x00\x04\x00\x08\x00\x06\x00\x07\x00\x01\x00\x08\x00\x0b\x00\x0b\x00\x0d\x00\x09\x00\x1e\x00\x1f\x00\x17\x00\x09\x00\x15\x00\x16\x00\x01\x00\x25\x00\x15\x00\x16\x00\x28\x00\x19\x00\x1a\x00\x1b\x00\x07\x00\x1e\x00\x1f\x00\x20\x00\x0d\x00\x22\x00\x23\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x09\x00\x2b\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x1f\x00\x20\x00\x07\x00\x22\x00\x23\x00\x24\x00\x0f\x00\x26\x00\x27\x00\x28\x00\x29\x00\x07\x00\x2b\x00\x2c\x00\x17\x00\x07\x00\x2f\x00\x30\x00\x31\x00\x32\x00\x07\x00\x07\x00\x09\x00\x0a\x00\x01\x00\x01\x00\x02\x00\x03\x00\x04\x00\x22\x00\x06\x00\x07\x00\x07\x00\x0e\x00\x0b\x00\x01\x00\x01\x00\x2a\x00\x18\x00\x08\x00\x15\x00\x16\x00\x1c\x00\x1d\x00\x08\x00\x0b\x00\x21\x00\x22\x00\x0f\x00\x19\x00\x1a\x00\x1b\x00\x15\x00\x16\x00\x01\x00\x2a\x00\x17\x00\x15\x00\x16\x00\x01\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0b\x00\x0d\x00\x0e\x00\x08\x00\x07\x00\x11\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0f\x00\x0d\x00\x0e\x00\x01\x00\x02\x00\x11\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0e\x00\x0d\x00\x0e\x00\x11\x00\x07\x00\x11\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0e\x00\x0d\x00\x0e\x00\x11\x00\x07\x00\x11\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0e\x00\x0d\x00\x0e\x00\x11\x00\x07\x00\x11\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0e\x00\x0d\x00\x0e\x00\x11\x00\x07\x00\x11\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x07\x00\x0d\x00\x0e\x00\x1c\x00\x1d\x00\x11\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x07\x00\x0d\x00\x0e\x00\x10\x00\x11\x00\x11\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0e\x00\x0d\x00\x0e\x00\x0e\x00\x01\x00\x11\x00\x01\x00\x15\x00\x16\x00\x07\x00\x15\x00\x16\x00\x01\x00\x02\x00\x0f\x00\x10\x00\x11\x00\x06\x00\x07\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x18\x00\x05\x00\x06\x00\x01\x00\x1c\x00\x1d\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x0d\x00\x0e\x00\x0d\x00\x0e\x00\x11\x00\x07\x00\x11\x00\x01\x00\x02\x00\x03\x00\x04\x00\x33\x00\x05\x00\x06\x00\x01\x00\x08\x00\x0f\x00\x10\x00\x11\x00\x0f\x00\x10\x00\x11\x00\x05\x00\x06\x00\x10\x00\x11\x00\x10\x00\x11\x00\x07\x00\x07\x00\x07\x00\x01\x00\x01\x00\x01\x00\x01\x00\x0b\x00\x0b\x00\x0b\x00\x01\x00\x01\x00\x01\x00\x01\x00\x07\x00\x07\x00\x0f\x00\x0b\x00\x01\x00\x01\x00\x07\x00\x01\x00\x17\x00\xff\xff\x09\x00\x09\x00\x0c\x00\x08\x00\x07\x00\x07\x00\x07\x00\x07\x00\x07\x00\x07\x00\x01\x00\x01\x00\x01\x00\x0a\x00\x01\x00\x01\x00\x0c\x00\x01\x00\x01\x00\x01\x00\x0f\x00\x0f\x00\x0f\x00\x0f\x00\x01\x00\x01\x00\xff\xff\x0f\x00\x01\x00\xff\xff\x0f\x00\x09\x00\x06\x00\x08\x00\x0f\x00\x0f\x00\x0f\x00\x08\x00\x08\x00\x08\x00\x0c\x00\x02\x00\x02\x00\x0b\x00\x01\x00\x0c\x00\x0c\x00\x02\x00\x0c\x00\x01\x00\x0f\x00\x01\x00\x01\x00\x0c\x00\x0c\x00\x01\x00\x01\x00\x01\x00\x15\x00\x0f\x00\x01\x00\x0c\x00\x01\x00\x01\x00\x12\x00\x08\x00\x08\x00\x0f\x00\x08\x00\xff\xff\x11\x00\x08\x00\x07\x00\x07\x00\xff\xff\x01\x00\xff\xff\xff\xff\xff\xff\x0f\x00\x08\x00\x02\x00\x0f\x00\x0f\x00\x0f\x00\x0f\x00\x0f\x00\x04\x00\x0f\x00\x08\x00\x0f\x00\x0f\x00\x0f\x00\x0f\x00\x09\x00\x0b\x00\x01\x00\x0f\x00\x0c\x00\x0b\x00\x0b\x00\x01\x00\x0b\x00\x01\x00\x01\x00\x0b\x00\x01\x00\x0b\x00\x0b\x00\x0b\x00\x0b\x00\x01\x00\x0b\x00\x01\x00\x01\x00\x08\x00\x01\x00\x08\x00\x02\x00\x08\x00\x02\x00\x02\x00\x08\x00\x01\x00\x12\x00\x08\x00\xff\xff\xff\xff\x08\x00\xff\xff\xff\xff\xff\xff\xff\xff\x0c\x00\xff\xff\x0c\x00\x0c\x00\x0c\x00\x0c\x00\x0c\x00\x0c\x00\x0c\x00\x08\x00\x08\x00\x08\x00\x0f\x00\x0f\x00\x0f\x00\x0f\x00\x09\x00\x0b\x00\x01\x00\x01\x00\x0b\x00\x0b\x00\x01\x00\x08\x00\x08\x00\x01\x00\x0c\x00\x01\x00\x11\x00\x06\x00\x08\x00\x0c\x00\x0c\x00\x08\x00\xff\xff\x06\x00\x06\x00\xff\xff\x06\x00\x0c\x00\x0c\x00\x06\x00\x05\x00\x05\x00\x02\x00\x06\x00\x06\x00\x06\x00\x11\x00\x05\x00\x11\x00\xff\xff\x07\x00\x06\x00\x06\x00\xff\xff\x07\x00\x07\x00\x07\x00\x07\x00\x06\x00\x06\x00\x06\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\xc8\x00\x07\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\xab\x00\x3c\x00\x3d\x00\x43\x00\xc7\x00\x08\x00\x3e\x00\x09\x00\x4c\x00\x0a\x00\xc3\x00\xc9\x00\x4b\x00\x78\x00\x79\x00\x52\x00\x10\x00\x78\x00\x79\x00\xc4\x00\x3f\x00\x40\x00\x41\x00\x30\x00\x0a\x00\x0b\x00\x0c\x00\x09\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x13\x00\x14\x00\x4a\x00\x15\x00\x16\x00\x17\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x53\x00\x0c\x00\x44\x00\x0d\x00\x0e\x00\x0f\x00\xac\x00\x11\x00\x12\x00\x54\x00\x14\x00\x2f\x00\x15\x00\x16\x00\xc6\x00\x2e\x00\x55\x00\x56\x00\x57\x00\x58\x00\x44\x00\x69\x00\x45\x00\x46\x00\x83\x00\x38\x00\x39\x00\x3a\x00\x3b\x00\x48\x00\x3c\x00\x3d\x00\x2c\x00\x77\x00\x84\x00\x7b\x00\x2d\x00\x49\x00\x6a\x00\xfc\x00\x78\x00\x79\x00\x6b\x00\x6c\x00\xfb\x00\x7c\x00\x47\x00\x48\x00\xac\x00\x3f\x00\x40\x00\x41\x00\x78\x00\x79\x00\x59\x00\x49\x00\xc5\x00\x78\x00\x79\x00\x25\x00\x30\x00\x31\x00\x32\x00\x33\x00\x5a\x00\x34\x00\x35\x00\xcb\x00\x2b\x00\x36\x00\x63\x00\x31\x00\x32\x00\x33\x00\xac\x00\x34\x00\x64\x00\x63\x00\x67\x00\x36\x00\xad\x00\x31\x00\x32\x00\x33\x00\xa5\x00\x34\x00\x35\x00\x36\x00\x2a\x00\x36\x00\x9f\x00\x31\x00\x32\x00\x33\x00\xa4\x00\x34\x00\x35\x00\x36\x00\x29\x00\x36\x00\x9e\x00\x31\x00\x32\x00\x33\x00\xa2\x00\x34\x00\x35\x00\x36\x00\x28\x00\x36\x00\xf0\x00\x31\x00\x32\x00\x33\x00\xcd\x00\x34\x00\x35\x00\x36\x00\x27\x00\x36\x00\xef\x00\x31\x00\x32\x00\x33\x00\x26\x00\x34\x00\x35\x00\xcc\x00\xcd\x00\x36\x00\xed\x00\x31\x00\x32\x00\x33\x00\x23\x00\x34\x00\x35\x00\xaf\x00\x61\x00\x36\x00\x3d\x01\x31\x00\x32\x00\x33\x00\xfe\x00\x34\x00\x35\x00\x3f\x01\x24\x00\x36\x00\x8b\x00\x78\x00\x79\x00\x22\x00\x78\x00\x79\x00\x63\x00\x39\x00\x5f\x00\x60\x00\x61\x00\x3c\x00\xa2\x00\x70\x00\x71\x00\x72\x00\x73\x00\x74\x00\x75\x00\x6a\x00\x6d\x00\x6e\x00\x8a\x00\x6b\x00\x6c\x00\x71\x00\x72\x00\x73\x00\x74\x00\x75\x00\x1c\x00\x02\x00\x03\x00\x04\x00\x05\x00\x4c\x00\x02\x00\x03\x00\x04\x00\x05\x00\xa3\x00\x35\x00\xa0\x00\x35\x00\x36\x00\x21\x00\x36\x00\x02\x00\x03\x00\x04\x00\x05\x00\xff\xff\x6d\x00\x6e\x00\x89\x00\xaa\x00\x19\x01\x60\x00\x61\x00\x36\x01\x60\x00\x61\x00\x6d\x00\x6e\x00\xae\x00\x61\x00\xa7\x00\x61\x00\x20\x00\x1f\x00\x1e\x00\x88\x00\x87\x00\x85\x00\x81\x00\x86\x00\x82\x00\x80\x00\x7f\x00\x7e\x00\x7d\x00\x63\x00\x5f\x00\x5e\x00\x5b\x00\x7a\x00\x50\x00\x4f\x00\x5d\x00\x4e\x00\x3d\x01\x00\x00\xbc\x00\xbb\x00\x5c\x00\xb4\x00\xba\x00\xb9\x00\xb8\x00\xb7\x00\xb6\x00\xb5\x00\x43\x00\x63\x00\x63\x00\xb1\x00\xa7\x00\x43\x00\xad\x00\x43\x00\x96\x00\x96\x00\xac\x00\x9d\x00\x9b\x00\x9a\x00\x43\x00\x43\x00\x00\x00\x99\x00\xdd\x00\x00\x00\x97\x00\xf4\x00\x2a\x01\x8f\x00\x94\x00\x92\x00\x90\x00\x8e\x00\x8d\x00\x8c\x00\xdc\x00\xd9\x00\xd6\x00\xdb\x00\xd4\x00\xda\x00\xd8\x00\xd3\x00\xd5\x00\xd2\x00\xd7\x00\xd0\x00\x63\x00\xd1\x00\xcf\x00\xc0\x00\xbf\x00\xbe\x00\x78\x00\x70\x00\xbd\x00\xc1\x00\x83\x00\x7b\x00\xef\x00\xf9\x00\xf8\x00\xf5\x00\xf7\x00\x00\x00\x67\x00\xf6\x00\xf3\x00\xf2\x00\x00\x00\x96\x00\x00\x00\x00\x00\x00\x00\xed\x00\xe8\x00\xe1\x00\xec\x00\xeb\x00\xea\x00\xe9\x00\xe7\x00\x50\x00\xe6\x00\xde\x00\xe4\x00\xe3\x00\xe2\x00\xdf\x00\x0c\x01\x0b\x01\x07\x01\x09\x01\x0a\x01\x08\x01\x06\x01\x05\x01\x04\x01\x03\x01\x02\x01\x01\x01\x00\x01\xff\x00\xfd\x00\x84\x00\x7c\x00\x43\x00\xfa\x00\x63\x00\x43\x00\x18\x01\x43\x00\x16\x01\xe1\x00\x15\x01\xe1\x00\xe1\x00\x13\x01\x43\x00\x2c\x01\x11\x01\x00\x00\x00\x00\x0e\x01\x00\x00\x00\x00\x00\x00\x00\x00\x23\x01\x00\x00\x22\x01\x21\x01\x20\x01\x1f\x01\x1e\x01\x1d\x01\x1c\x01\x2b\x01\x29\x01\x24\x01\x28\x01\x27\x01\x26\x01\x25\x01\x31\x01\x30\x01\x2f\x01\x2e\x01\x2d\x01\x36\x01\x43\x00\x34\x01\x33\x01\x43\x00\x39\x01\x63\x00\x65\x00\x41\x00\x3b\x01\x38\x01\x3c\x01\x3a\x01\x00\x00\xb2\x00\xb1\x00\x00\x00\x9d\x00\x75\x00\x6e\x00\x9b\x00\x97\x00\x94\x00\xc1\x00\x92\x00\x90\x00\x1a\x01\xa8\x00\xe4\x00\xc9\x00\x00\x00\xdf\x00\x18\x01\x16\x01\x00\x00\x13\x01\x11\x01\x0f\x01\x0e\x01\x0c\x01\x34\x01\x31\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (1, 87) [
	(1 , happyReduce_1),
	(2 , happyReduce_2),
	(3 , happyReduce_3),
	(4 , happyReduce_4),
	(5 , happyReduce_5),
	(6 , happyReduce_6),
	(7 , happyReduce_7),
	(8 , happyReduce_8),
	(9 , happyReduce_9),
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14),
	(15 , happyReduce_15),
	(16 , happyReduce_16),
	(17 , happyReduce_17),
	(18 , happyReduce_18),
	(19 , happyReduce_19),
	(20 , happyReduce_20),
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27),
	(28 , happyReduce_28),
	(29 , happyReduce_29),
	(30 , happyReduce_30),
	(31 , happyReduce_31),
	(32 , happyReduce_32),
	(33 , happyReduce_33),
	(34 , happyReduce_34),
	(35 , happyReduce_35),
	(36 , happyReduce_36),
	(37 , happyReduce_37),
	(38 , happyReduce_38),
	(39 , happyReduce_39),
	(40 , happyReduce_40),
	(41 , happyReduce_41),
	(42 , happyReduce_42),
	(43 , happyReduce_43),
	(44 , happyReduce_44),
	(45 , happyReduce_45),
	(46 , happyReduce_46),
	(47 , happyReduce_47),
	(48 , happyReduce_48),
	(49 , happyReduce_49),
	(50 , happyReduce_50),
	(51 , happyReduce_51),
	(52 , happyReduce_52),
	(53 , happyReduce_53),
	(54 , happyReduce_54),
	(55 , happyReduce_55),
	(56 , happyReduce_56),
	(57 , happyReduce_57),
	(58 , happyReduce_58),
	(59 , happyReduce_59),
	(60 , happyReduce_60),
	(61 , happyReduce_61),
	(62 , happyReduce_62),
	(63 , happyReduce_63),
	(64 , happyReduce_64),
	(65 , happyReduce_65),
	(66 , happyReduce_66),
	(67 , happyReduce_67),
	(68 , happyReduce_68),
	(69 , happyReduce_69),
	(70 , happyReduce_70),
	(71 , happyReduce_71),
	(72 , happyReduce_72),
	(73 , happyReduce_73),
	(74 , happyReduce_74),
	(75 , happyReduce_75),
	(76 , happyReduce_76),
	(77 , happyReduce_77),
	(78 , happyReduce_78),
	(79 , happyReduce_79),
	(80 , happyReduce_80),
	(81 , happyReduce_81),
	(82 , happyReduce_82),
	(83 , happyReduce_83),
	(84 , happyReduce_84),
	(85 , happyReduce_85),
	(86 , happyReduce_86),
	(87 , happyReduce_87)
	]

happy_n_terms = 52 :: Prelude.Int
happy_n_nonterms = 18 :: Prelude.Int

#if __GLASGOW_HASKELL__ >= 710
happyReduce_1 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_1 = happySpecReduce_2  0# happyReduction_1
happyReduction_1 happy_x_2
	happy_x_1
	 =  case happyOut5 happy_x_1 of { (HappyWrap5 happy_var_1) -> 
	case happyOut4 happy_x_2 of { (HappyWrap4 happy_var_2) -> 
	happyIn4
		 (happy_var_1:happy_var_2
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_2 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_2 = happySpecReduce_0  0# happyReduction_2
happyReduction_2  =  happyIn4
		 ([]
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_3 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_3 = happyReduce 4# 1# happyReduction_3
happyReduction_3 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOut8 happy_x_3 of { (HappyWrap8 happy_var_3) -> 
	happyIn5
		 (\env -> putStrNoLnFSOpt ("# " ++ happy_var_1 ++ ":=") >>
             happy_var_3 env >>= \rhs ->
             putStrFS_debug ("# " ++ happy_var_1 ++ ":=" )>>
             case rhs of {
               R (RecPost _ f triple) -> 
                 return (R (RecPost happy_var_1 f triple)); 
               F f -> 
                 simplify f >>= \sf -> 
                 return (F sf);
               QF (qv,f) ->
                 simplify f >>= \sf ->
                 return (QF (qv,sf))
             } >>= \renamedRHS ->
                 putStrFS_debug ("#bottomup " ++ happy_var_1 ++ ":=") >>
                 return (extendRelEnv env (happy_var_1,renamedRHS))
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_4 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_4 = happySpecReduce_2  1# happyReduction_4
happyReduction_4 happy_x_2
	happy_x_1
	 =  case happyOut7 happy_x_1 of { (HappyWrap7 happy_var_1) -> 
	happyIn5
		 (\env -> happy_var_1 env >>= \res ->
               return res
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_5 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_5 = happyReduce 6# 1# happyReduction_5
happyReduction_5 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut10 happy_x_2 of { (HappyWrap10 happy_var_2) -> 
	case happyOut6 happy_x_5 of { (HappyWrap6 happy_var_5) -> 
	happyIn5
		 (\env -> 
        happy_var_5 env >>= \fl ->
        if (length fl /= length happy_var_2)
        then 
            error "Mismatch in number of LHS and RHS"
        else 
           let new_fl = zip happy_var_2 fl in
             mapM (\(id,rhs) ->
               case rhs of {
                 R (RecPost _ f triple) ->
                   --putStrFS_debug("bach_f_rec="++ show f) >>  
                   return (R (RecPost id f triple)); 
                 (F f) -> 
                   --putStrFS_debug("bach_f="++ show f) >>  
                   simplify f >>= \fsimpl -> 
                   --putStrFS(show fsimpl) >>  
                   return (F fsimpl);
                 (QF (qv,f)) -> 
                   --putStrFS_debug("bach_f="++ show f) >>  
                   simplify f >>= \fsimpl -> 
                   --putStrFS(show fsimpl) >>  
                   return (QF (qv,fsimpl))}
             ) new_fl >>= \rhs1 -> 
           let rhs_new = zip happy_var_2 rhs1 in
           foldM (\env1 -> \(id,rhs2) ->
              case rhs2 of
                 F f -> 
                  --putStrFS_debug ("#bach_gen " ++ id ++ ":="++(show f)++"\n") >>
                  putStrNoLnFSOpt ("# " ++ id ++ ":="++(show f)++"\n") >>
                  return (extendRelEnv env1 (id,rhs2))
                 _ -> error "impossible : should be a formula"
                ) env rhs_new
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_6 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_6 = happySpecReduce_2  1# happyReduction_6
happyReduction_6 happy_x_2
	happy_x_1
	 =  case happyOut6 happy_x_1 of { (HappyWrap6 happy_var_1) -> 
	happyIn5
		 (\env -> happy_var_1 env >>= \fl -> 
         mapM (\rhs ->
             case rhs of
               (F f) -> 
                 simplify f >>= \fsimpl -> 
                 putStrFS(show fsimpl) >> 
                 return (F fsimpl)
               (QF (qv,f)) -> 
                 simplify f >>= \fsimpl -> 
                 putStrFS(show (qv,fsimpl)) >> 
                 return (QF (qv,fsimpl))
               (R recpost) -> 
                 putStrFS(show recpost) >> 
                 return rhs
             ) fl >>= \rhs1 -> 
         foldM (\env1 -> \rhs2 -> 
       return (extendRelEnv env1 (" ",rhs2))) env rhs1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_7 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_7 = happySpecReduce_2  1# happyReduction_7
happyReduction_7 happy_x_2
	happy_x_1
	 =  case happyOut8 happy_x_1 of { (HappyWrap8 happy_var_1) -> 
	happyIn5
		 (\env -> happy_var_1 env >>= \rhs -> 
             case rhs of
               (F f) -> 
                  simplify f >>= \fsimpl ->
                  putStrFSOpt("\n" ++ showSet fsimpl ++ "\n") >> 
                  return env
               (QF (qv,f)) -> 
                  simplify f >>= \fsimpl ->
                  putStrFSOpt("\n{[" ++ show qv ++ "] : " ++  showSet fsimpl ++ "}\n") >> 
                  return env
               (R recpost) -> 
                  putStrFS ("\n" ++ show recpost ++ "\n") >> 
                  return env
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_8 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_8 = happyReduce 11# 1# happyReduction_8
happyReduction_8 (happy_x_11 `HappyStk`
	happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut10 happy_x_4 of { (HappyWrap10 happy_var_4) -> 
	case happyOut10 happy_x_8 of { (HappyWrap10 happy_var_8) -> 
	happyIn5
		 (\env -> --putStrFS("# fixtestPost("++ (show happy_var_4) ++ "," ++ (show happy_var_8) ++ ");") >> 
        if(length happy_var_4 ==length happy_var_8) 
        then
          let (qvr,rcp) = unzip (map (\x -> case lookupVar x env of
                            Just (R recpost@(RecPost _ _ (sv1,sv2,_)))-> ((sv1++sv2),recpost)
                            _ ->  error ("Arguments of fixtest are incorrect")) happy_var_4)
          in
          let mf = map (\(x,qv1) -> case lookupVar x env of
                    Just (F f) -> f;
                    Just (QF (qv2,f)) ->
                      let subs = zip qv2 qv1 in
                      apply subs f
                    _->  error ("Arguments of fixtest are incorrect")) $ (zip happy_var_8 qvr) 
          in
          fixTestBU_Lgen rcp mf >>= \fixok ->
          putStrFSOpt("\n# " ++ show fixok ++ "\n") >>
          return env
        else 
          error ("Mismatch numbers of [] and [] in RHS!")
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_9 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_9 = happyReduce 7# 1# happyReduction_9
happyReduction_9 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	case happyOutTok happy_x_5 of { (TkAlphaNum happy_var_5) -> 
	happyIn5
		 (\env -> putStrFS("# fixtestInv("++ happy_var_3 ++ "," ++ happy_var_5 ++ ");") >> 
             case (lookupVar happy_var_3 env,lookupVar happy_var_5 env) of
               (Just (R recpost),Just (F f)) ->
                  getOneStep recpost fTrue >>= \oneStep ->
                  fixTestTD oneStep f >>= \fixok -> 
                  putStrFSOpt("\n# " ++ show fixok ++ "\n") >> 
                  return env
               (Just (R recpost@(RecPost _ _ (sv1,sv2,_))),Just (QF (qv2,f))) ->
                  getOneStep recpost fTrue >>= \oneStep ->
                  let qv1 = sv1++sv2 in
                  let subs = zip qv2 qv1 in
                  let sf = apply subs f in
                  fixTestTD oneStep sf >>= \fixok -> 
                  putStrFSOpt("\n# " ++ show fixok ++ "\n") >> 
                  return env
               (_,_) -> error ("Arguments of fixtestInv are incorrect")
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_10 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_10 = happyReduce 4# 1# happyReduction_10
happyReduction_10 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn5
		 (\env -> putStrFSOpt("# "++ happy_var_1 ++ " subset " ++ happy_var_3 ++ ";") >>
             case (lookupVar happy_var_1 env,lookupVar happy_var_3 env) of
               (Just (F f1),Just (F f2)) ->
                 subset f1 f2 >>= \subok -> 
                 putStrFSOpt("\n# " ++ show subok ++ "\n") >> 
                 return env
               (Just (QF (qv1,f1)),Just (QF (qv2,f2))) ->
                 if (length qv1) == (length qv2) then
                   let subs = zip qv2 qv1 in
                   let sf2 = apply subs f2 in
                   subset f1 sf2 >>= \subok -> 
                   putStrFSOpt("\n# " ++ show subok ++ "\n") >> 
                   return env
                 else error ("Arguments of subset are not valid QFormulas\n")
               (_,_) -> error ("Arguments of subset are not valid\n")
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_11 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_11 = happySpecReduce_2  1# happyReduction_11
happyReduction_11 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	happyIn5
		 (\env -> putStrFSOpt("\n# "++ happy_var_1 ++ ";") >>
             case lookupVar happy_var_1 env of 
               Just (R recpost) -> putStrFS("\n" ++ show recpost ++ "\n") >> 
                 return env
               Just (F f) -> putStrFS("\n" ++ show f ++ "\n") >> 
                 return env
               Just (QF qf) -> putStrFS("\n" ++ show qf ++ "\n") >> 
                 return env
               Nothing -> error ("# Variable not declared - "++happy_var_1++"\n")
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_12 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_12 = happyReduce 12# 2# happyReduction_12
happyReduction_12 (happy_x_12 `HappyStk`
	happy_x_11 `HappyStk`
	happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut9 happy_x_4 of { (HappyWrap9 happy_var_4) -> 
	case happyOut11 happy_x_8 of { (HappyWrap11 happy_var_8) -> 
	case happyOutTok happy_x_11 of { (TkAlphaNum happy_var_11) -> 
	happyIn6
		 (\env -> 
      let heur = case happy_var_11 of {"SimHeur" -> SimilarityHeur; 
                             "DiffHeur" -> DifferenceHeur; 
                             "HausHeur" -> HausdorffHeur; 
                             "InterHeur" -> SimInteractiveHeur; 
                             lit -> error ("Heuristic not implemented parser.y - "++lit)} 
      in
      bottomUp2k_gen (happy_var_4 env) (map (\x -> (x,heur)) (happy_var_8)) (map (\x -> fFalse) (happy_var_4 env)) 
      >>= \resl -> return (map (\x -> F x) (fst (unzip resl)))
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_13 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_13 = happyReduce 10# 2# happyReduction_13
happyReduction_13 (happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut10 happy_x_4 of { (HappyWrap10 happy_var_4) -> 
	case happyOut10 happy_x_8 of { (HappyWrap10 happy_var_8) -> 
	happyIn6
		 (\env ->
        putStrFSOpt ("apply(" ++ show happy_var_4 ++ "," ++ show happy_var_8 ++ ");") >>
        if(length happy_var_4 ==length happy_var_8) then
            let qv_rp = map (\x -> case lookupVar x env of {
                Just (R recpost@(RecPost _ _ (sv1,sv2,_)))-> ((sv1++sv2),recpost);
                _ ->  error ("apply: mismatched argume")}) happy_var_4 in
            let (mqv,mrp) = unzip qv_rp in
            let mf = map (\(x,qv1) -> case lookupVar x env of {
                Just (F f) -> f;
                Just (QF (qv2,f)) ->
                    let subs = zip qv2 qv1 in
                    apply subs f;
                 _->  error ("apply: mismatched arguments of relation")
                }) $ (zip happy_var_8 mqv) in
            subrec_gen mrp mf  >>= \fn ->
            mapM (\x -> simplify x >>= \f -> return (F f)) fn >>= \fs ->
            return fs
        else error ("apply: mismatched arguments of relations!")
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_14 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_14 = happyReduce 14# 2# happyReduction_14
happyReduction_14 (happy_x_14 `HappyStk`
	happy_x_13 `HappyStk`
	happy_x_12 `HappyStk`
	happy_x_11 `HappyStk`
	happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut10 happy_x_4 of { (HappyWrap10 happy_var_4) -> 
	case happyOut11 happy_x_8 of { (HappyWrap11 happy_var_8) -> 
	case happyOut10 happy_x_12 of { (HappyWrap10 happy_var_12) -> 
	happyIn6
		 (\env ->
        putStrFSOpt ("selhull(" ++ show happy_var_4 ++ "," ++ show happy_var_8 ++ "," ++ show happy_var_12 ++ ");") >>
        if ((length happy_var_4) == (length happy_var_8)) && ((length happy_var_4) == (length happy_var_8)) then
            let params = zip3 happy_var_4 happy_var_8 happy_var_12 in
            mapM (\ (id,val,hr) -> case lookupVar id env of {
                Just (R recpost) -> error ("Argument of selhull is not a formula\n");
                Nothing -> error ("Variable not declared - "++ show id ++"\n");
                Just (QF qf) -> error ("Argument of selhull is not a formula\n");
                Just (F f) ->
                    let heur = case hr of {
                        "SimHeur" -> SimilarityHeur;
                        "DiffHeur" -> DifferenceHeur;
                        "HausHeur" -> HausdorffHeur;
                        lit -> error ("Heuristic not implemented parser.y4 - "++lit)
                    } in
                    combSelHull (val,heur) (getDisjuncts f) [] >>= \disj -> return (F (Or disj))
                }) params
        else error ("selhull: invalid arguments")
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_15 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_15 = happyReduce 14# 2# happyReduction_15
happyReduction_15 (happy_x_14 `HappyStk`
	happy_x_13 `HappyStk`
	happy_x_12 `HappyStk`
	happy_x_11 `HappyStk`
	happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut10 happy_x_4 of { (HappyWrap10 happy_var_4) -> 
	case happyOut10 happy_x_8 of { (HappyWrap10 happy_var_8) -> 
	case happyOut10 happy_x_12 of { (HappyWrap10 happy_var_12) -> 
	happyIn6
		 (\env ->
        putStrFSOpt ("widen(" ++ show happy_var_4 ++ "," ++ show happy_var_8 ++ "," ++ show happy_var_12 ++ ");") >>
        if ((length happy_var_4) == (length happy_var_8)) && ((length happy_var_4) == (length happy_var_8)) then
            let params = zip3 happy_var_4 happy_var_8 happy_var_12 in
            mapM (\ (val1,val2,hr) ->
                case (lookupVar val1 env, lookupVar val2 env) of {
                    (Just (F f1), Just (F f2)) ->
                        let heur = case hr of {
                            "SimHeur" -> SimilarityHeur;
                            "DiffHeur" -> DifferenceHeur;
                            "HausHeur" -> HausdorffHeur;
                            lit -> error ("Heuristic not implemented parser.y4 - "++lit)
                        } in
                        widen heur [] (getDisjuncts f1,getDisjuncts f2) >>= \disj ->
                       return (F (Or disj));
                    (_,_) -> error "widen: invalid arguments"
               }) params
        else error ("widen: invalid arguments")
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_16 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_16 = happyReduce 6# 3# happyReduction_16
happyReduction_16 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_5 of { (TkAlphaNum happy_var_5) -> 
	happyIn7
		 (\env ->
      case (lookupVar happy_var_5 env) of 
        Just (F f) -> 
          simplify f >>= \f1 ->
          return f1
        _ -> error ("PickEqFromEq sorely supports Formula")
      >>= \fl -> 
      putStrFS_debug("#After parse Formula: "++show (fl)) >>
      let rs1=getEq fl in
      putStrFS_debug("#getEq: "++show (rs1)) >>
      let eq_udt_list =pickEqFromEq rs1 in
      putStrFS_debug("#list eq after pick="++show (eq_udt_list)) >>
      let rhs=concat (map (\x -> return (EqK x)) eq_udt_list) in
      putStrFS_debug("#concat="++show (rhs)) >>
      --foldM (\env1 -> \rhs1 -> return (extendRelEnv env1 (happy_var_1,(F rhs1)))) env rhs  --formula in which are disj or conj => needs to be modified here?     
      return (extendRelEnv env (happy_var_1,(F (And rhs))))
      --return env
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_17 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_17 = happyReduce 4# 3# happyReduction_17
happyReduction_17 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn7
		 (\env ->
      case (lookupVar happy_var_3 env) of 
        Just (F f) -> 
          simplify f >>= \f1 ->
          return f1
        _ -> error ("PickEqFromEq solely supports Formula")
      >>= \fl -> 
      putStrFS_debug("#After parse Formula: "++show (fl)) >>
      let rs1=getEq fl in
      putStrFS_debug("#getEq: "++show (rs1)) >>
      let eq_udt_list =pickEqFromEq rs1 in
      putStrFS_debug("#list eq after pick="++show (eq_udt_list)) >>
      let rhs=concat (map (\x -> return (EqK x)) eq_udt_list) in
      putStrFS_debug("#concat="++show (rhs)) >>   
      putStrFS_DD 0 ("# pickEqFromEq("++happy_var_3++")") >>
      putStrFS(show (And rhs)) >>
      return (extendRelEnv env (" ",(F (And rhs))))
      --return env
	) `HappyStk` happyRest}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_18 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_18 = happyReduce 6# 3# happyReduction_18
happyReduction_18 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_5 of { (TkAlphaNum happy_var_5) -> 
	happyIn7
		 (\env ->
      case (lookupVar happy_var_5 env) of 
        Just (F f) -> 
          simplify f >>= \f1 ->
          return f1
        _ -> error ("PickGEqFromEq sorely supports Formula")
      >>= \fl -> 
      putStrFS_debug("#After parse Formula GEq: "++show (fl)) >>
      pickGEQfromEQ fl >>= \gEq ->
      --mapM (\g1 ->putStrFS_debug("#list GEq after pick="++show (g1))) gEq >>
      let rhs=concat ((mapM (\x -> return x) gEq) :: [[Formula]]) in
      putStrFS_debug("#concat="++show (rhs)) >>    
      return (extendRelEnv env (happy_var_1,(F (And rhs))))
      --return env
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_19 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_19 = happyReduce 4# 3# happyReduction_19
happyReduction_19 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn7
		 (\env ->
      case (lookupVar happy_var_3 env) of 
        Just (F f) -> 
          simplify f >>= \f1 ->
          return f1
        _ -> error ("PickGEqFromEq sorely supports Formula")
      >>= \fl -> 
      putStrFS_debug("#After parse Formula GEq: "++show (fl)) >>
      pickGEQfromEQ fl >>= \gEq ->
      --mapM (\g1 ->putStrFS_debug("#list GEq after pick="++show (g1))) gEq >>
      let rhs=concat ((mapM (\x -> return x) gEq) :: [[Formula]]) in
      putStrFS_debug("#concat="++show (rhs)) >>
      putStrFS("#pickGEqFromEq of "++happy_var_3++" : "++show (And rhs)) >>     
      return (extendRelEnv env (" ",(F (And rhs))))
      --return env
	) `HappyStk` happyRest}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_20 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_20 = happyReduce 6# 3# happyReduction_20
happyReduction_20 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_5 of { (TkAlphaNum happy_var_5) -> 
	happyIn7
		 (\env -> 
       case (lookupVar happy_var_5 env) of 
        Just (F f) -> 
          simplify f >>= \f1 ->
          return f1
        _ -> error ("satEQfromEQ sorely supports Formula")
      >>= \fl -> 
      --putStrFS_debug("#satEQEQ After parse Formula: "++show (fl)) >>
      satEQfromEQ fl >>= \fsatEQ -> return (extendRelEnv env (happy_var_1,(F (And fsatEQ))))
      --return env
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_21 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_21 = happyReduce 4# 3# happyReduction_21
happyReduction_21 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn7
		 (\env -> 
       case (lookupVar happy_var_3 env) of 
        Just (F f) -> 
          simplify f >>= \f1 ->
          return f1
        _ -> error ("satEQfromEQ sorely supports Formula")
      >>= \fl -> 
      --putStrFS_debug("#satEQEQ After parse Formula: "++show (fl)) >>
      satEQfromEQ fl >>= \fsatEQ -> return (extendRelEnv env (" ",(F (And fsatEQ))))
      --return env
	) `HappyStk` happyRest}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_22 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_22 = happyReduce 6# 3# happyReduction_22
happyReduction_22 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_5 of { (TkAlphaNum happy_var_5) -> 
	happyIn7
		 (\env ->
      case (lookupVar happy_var_5 env) of 
        Just (F f) -> 
          putStrFS("EQEQ org:"++ show f)>>
          simplify f >>= \f1 ->
          putStrFS("EQEQ sim:"++ show f1)>>
          return f1
        _ -> error ("satGEQFromEQ sorely supports Formula")
      >>= \fl -> 
      --putStrFS_debug("#saeGEQEQ After parse Formula GEq: "++show (fl)) >>
      satGEQfromEQ fl >>= \rhs -> return (extendRelEnv env (happy_var_1,(F (And rhs))))
      --return env
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_23 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_23 = happyReduce 4# 3# happyReduction_23
happyReduction_23 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn7
		 (\env ->
      case (lookupVar happy_var_3 env) of 
        Just (F f) -> 
          simplify f >>= \f1 ->
          return f1
        _ -> error ("satGEQFromEQ sorely supports Formula")
      >>= \fl -> 
      --putStrFS_debug("#saeGEQEQ After parse Formula GEq: "++show (fl)) >>
      satGEQfromEQ fl >>= \rhs -> return (extendRelEnv env (" ",(F (And rhs))))
      --return env
	) `HappyStk` happyRest}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_24 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_24 = happySpecReduce_3  4# happyReduction_24
happyReduction_24 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn8
		 (\env -> putStrFSOpt ("{ ... };") >>
                           if "f_" `elem` (map (\(SizeVar anno,_) -> take 2 anno) (fqsv happy_var_2)) then 
                             error ("Free variables of formula should not start with \"f_\" (\"f_\" are fresh variables)")
                           else return (F happy_var_2)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_25 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_25 = happyReduce 7# 4# happyReduction_25
happyReduction_25 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut19 happy_x_3 of { happy_var_3 -> 
	case happyOut12 happy_x_6 of { happy_var_6 -> 
	happyIn8
		 (\env -> putStrFSOpt ("{ ... };") >>
                           if "f_" `elem` (map (\(SizeVar anno,_) -> take 2 anno) (fqsv happy_var_6)) then 
                             error ("Free variables of formula should not start with \"f_\" (\"f_\" are fresh variables)")
                           else if (length happy_var_3 == 0) then return (F happy_var_6)
                           else return (QF (reverse happy_var_3,happy_var_6))
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_26 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_26 = happyReduce 17# 4# happyReduction_26
happyReduction_26 (happy_x_17 `HappyStk`
	happy_x_16 `HappyStk`
	happy_x_15 `HappyStk`
	happy_x_14 `HappyStk`
	happy_x_13 `HappyStk`
	happy_x_12 `HappyStk`
	happy_x_11 `HappyStk`
	happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut19 happy_x_3 of { happy_var_3 -> 
	case happyOut19 happy_x_8 of { happy_var_8 -> 
	case happyOut19 happy_x_13 of { happy_var_13 -> 
	case happyOut12 happy_x_16 of { happy_var_16 -> 
	happyIn8
		 (\env -> putStrFSOpt ("{ ... };") >> 
                           if "f_" `elem` (map (\(SizeVar anno,_) -> take 2 anno) (fqsv happy_var_16)) then 
                             error ("Free variables of formula should not start with \"f_\" (\"f_\" are fresh variables)")
                           else return (R (RecPost "dummy" happy_var_16 (reverse happy_var_3,reverse happy_var_8,reverse happy_var_13)))
	) `HappyStk` happyRest}}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_27 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_27 = happyReduce 4# 4# happyReduction_27
happyReduction_27 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn8
		 (\env -> putStrFSOpt (happy_var_1 ++ "(" ++ happy_var_3 ++ ");") >>
                 let (cabst,qv1) = case lookupVar happy_var_1 env of {
                     Just (R recpost@(RecPost _ _ (sv1,sv2,_))) -> (recpost, sv1++sv2); 
                     Just (F f) -> error ("Argument of subrec is not a constraint abstraction\n"); 
                     Just (QF qf) -> error ("Argument of subrec is not a constraint abstraction\n"); 
                     Nothing -> error ("Variable not declared - "++happy_var_1++"\n")} in
                 case lookupVar happy_var_3 env of {
                     Just (F f) -> 
                         subrec_z cabst f >>= \fn -> simplify fn >>= \fnext -> return (F fnext);
                     Just (QF (qv2,f)) ->
                         let subs = zip qv2 qv1 in
                         let sf = apply subs f in
                         {-- print_DD True 2 [("== QF qv1 = ", show qv1)] >>
                         print_DD True 2 [("== QF qv2 = ", show qv2)] >>
                         print_DD True 2 [("== QF subs = ", show subs)] >>
                         print_DD True 2 [("== QF f   = ", show f)] >>
                         print_DD True 2 [("== QF sf  = ", show sf)] >> --}
                         subrec_z cabst sf >>= \fn -> simplify fn >>= \fnext -> return (F fnext);
                     Just (R recpost) -> error ("Argument of subrec is not a formula\n"); 
                     Nothing -> error ("Variable not declared - "++happy_var_3++"\n")
                 }
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_28 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_28 = happyReduce 10# 4# happyReduction_28
happyReduction_28 (happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOut10 happy_x_4 of { (HappyWrap10 happy_var_4) -> 
	case happyOut10 happy_x_8 of { (HappyWrap10 happy_var_8) -> 
	happyIn8
		 (\env -> putStrFSOpt (happy_var_1 ++ "([" ++ show happy_var_4 ++ "],[" ++ show happy_var_8 ++ "]);") >>
                 let (cabst,qv1) = case lookupVar happy_var_1 env of {
                     Just (R recpost@(RecPost _ _ (sv1,sv2,_))) -> (recpost, sv1++sv2); 
                     Just (F f) -> error ("Argument of subrec is not a constraint abstraction\n"); 
                     Just (QF qf) -> error ("Argument of subrec is not a constraint abstraction\n"); 
                     Nothing -> error ("Variable not declared - "++happy_var_1++"\n")} in
                 if(length happy_var_4 ==length happy_var_8) then
                     let (mqv,mrp) = unzip (map (\x -> case lookupVar x env of
                                       Just (R recpost@(RecPost _ _ (sv1,sv2,_)))-> ((sv1++sv2),recpost)
                                       _ ->  error ("Relation arguments of subrec are incorrect")) happy_var_4 )
                     in
                     let mf = map (\(x,qv1) -> case lookupVar x env of
                                Just (F f) -> f;
                                Just (QF (qv2,f)) ->
                                    let subs = zip qv2 qv1 in
                                    apply subs f
                                _->  error ("Formula arguments of subrec are incorrect")) $ (zip happy_var_8 mqv) 
                     in
                     let r_input = zip mrp mf in
                     subrec_z_mut cabst r_input >>= \fn -> simplify fn >>= \fnext -> return (F fnext);
                 else 
                     error ("Mismatch numbers of [] and [] in RHS!")
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_29 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_29 = happyReduce 8# 4# happyReduction_29
happyReduction_29 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	case happyOutTok happy_x_5 of { (TkIntNum happy_var_5) -> 
	case happyOutTok happy_x_7 of { (TkAlphaNum happy_var_7) -> 
	happyIn8
		 (\env -> putStrFSOpt ("bottomup(" ++ happy_var_3 ++ "," ++ show happy_var_5 ++ "," ++ happy_var_7 ++ ");") >>
                 case lookupVar happy_var_3 env of
                   Just (F f) -> error ("Argument of bottomup is not a constraint abstraction\n")
                   Just (QF qf) -> error ("Argument of bottomup is not a constraint abstraction\n")
                   Nothing -> error ("Variable not declared - "++happy_var_3++"\n")
                   Just (R recpost) -> 
                       let heur = case happy_var_7 of {"SimHeur" -> SimilarityHeur; "DiffHeur" -> DifferenceHeur; "HausHeur" -> HausdorffHeur; lit -> error ("Heuristic not implemented parser.y2 - "++lit)} in
                       bottomUp2k recpost (happy_var_5,heur) fFalse >>= \(post,cnt) -> return (F post)
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_30 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_30 = happyReduce 6# 4# happyReduction_30
happyReduction_30 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	case happyOutTok happy_x_5 of { (TkAlphaNum happy_var_5) -> 
	happyIn8
		 (\env -> putStrFS ("bottomup_mr(" ++ happy_var_3 ++ "," ++ happy_var_5 ++ ");") >>
                 case lookupVar happy_var_3 env of
                   Just (F f) -> error ("First argument of bottomup_mr is not a constraint abstraction\n")
                   Just (QF qf) -> error ("First argument of bottomup_mr is not a constraint abstraction\n")
                   Nothing -> error ("Variable not declared - "++happy_var_3++"\n")
                   Just (R recpost1) -> 
                       case lookupVar happy_var_5 env of 
                         Just (F f) -> error ("Second argument of bottomup_mr is not a constraint abstraction\n")
                         Just (QF qf) -> error ("Second argument of bottomup_mr is not a constraint abstraction\n")
                         Nothing -> error ("Variable not declared - "++happy_var_5++"\n")
                         Just (R recpost2) -> bottomUp_mr recpost1 recpost2  >>= \(post,cnt) -> return (F post)
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_31 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_31 = happyReduce 8# 4# happyReduction_31
happyReduction_31 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	case happyOutTok happy_x_5 of { (TkIntNum happy_var_5) -> 
	case happyOutTok happy_x_7 of { (TkAlphaNum happy_var_7) -> 
	happyIn8
		 (\env -> putStrFSOpt ("topdown(" ++ happy_var_3 ++ "," ++ show happy_var_5 ++ "," ++ happy_var_7 ++ ");") >>
                 case lookupVar happy_var_3 env of
                   Just (F f) -> error ("Argument of topdown is not a constraint abstraction\n")
                   Just (QF qf) -> error ("Argument of topdown is not a constraint abstraction\n")
                   Nothing -> error ("Variable not declared - "++happy_var_3++"\n")
                   Just (R recpost) -> 
                     let heur = case happy_var_7 of {"SimHeur" -> SimilarityHeur; "DiffHeur" -> DifferenceHeur; "HausHeur" -> HausdorffHeur; lit -> error ("Heuristic not implemented parser.y3 - "++lit)} in
                     topDown2k recpost (happy_var_5,heur) fTrue >>= \(inv,cnt) -> return (F inv)
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_32 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_32 = happyReduce 12# 4# happyReduction_32
happyReduction_32 (happy_x_12 `HappyStk`
	happy_x_11 `HappyStk`
	happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut9 happy_x_4 of { (HappyWrap9 happy_var_4) -> 
	case happyOut11 happy_x_8 of { (HappyWrap11 happy_var_8) -> 
	case happyOutTok happy_x_11 of { (TkAlphaNum happy_var_11) -> 
	happyIn8
		 (\env -> 
      let heur = case happy_var_11 of {"SimHeur" -> SimilarityHeur; 
                             "DiffHeur" -> DifferenceHeur; 
                             "HausHeur" -> HausdorffHeur; 
                             "InterHeur" -> SimInteractiveHeur; 
                             lit -> error ("Heuristic not implemented parser.y - "++lit)} 
      in
      gfp2k (happy_var_4 env) (map (\x -> (x,heur)) (happy_var_8)) (map (\x -> fTrue) (happy_var_4 env)) 
        >>= \resl -> return (F (fOr (fst (unzip resl))))
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_33 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_33 = happySpecReduce_3  4# happyReduction_33
happyReduction_33 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn8
		 (\env -> putStrFSOpt("# "++ happy_var_1 ++ " complement " ++ happy_var_3 ++ ";") >>
             case (lookupVar happy_var_1 env,lookupVar happy_var_3 env) of
               (Just (F f1),Just (F f2)) ->
                 difference f1 f2 >>= \result -> 
                 return (F result)
               (_,_) -> error ("Arguments of complement are not valid\n")
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_34 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_34 = happySpecReduce_2  4# happyReduction_34
happyReduction_34 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_2 of { (TkAlphaNum happy_var_2) -> 
	happyIn8
		 (\env -> putStrFSOpt("complement " ++ happy_var_2 ++ ";") >>
             case (lookupVar happy_var_2 env) of
               Just (F f1) ->
                 complement f1 >>= \result -> 
                 return (F result)
               _ -> error ("Arguments of complement are not valid\n")
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_35 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_35 = happyReduce 8# 4# happyReduction_35
happyReduction_35 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	case happyOutTok happy_x_5 of { (TkIntNum happy_var_5) -> 
	case happyOutTok happy_x_7 of { (TkAlphaNum happy_var_7) -> 
	happyIn8
		 (\env -> putStrFSOpt ("selhull(" ++ happy_var_3 ++ "," ++ show happy_var_5 ++ "," ++ happy_var_7 ++ ");") >>
                 case lookupVar happy_var_3 env of
                   Just (R recpost) -> error ("Argument of selhull is not a formula\n")
                   Nothing -> error ("Variable not declared - "++happy_var_3++"\n")
                   Just (QF qf) -> error ("Argument of selhull is not a formula\n")
                   Just (F f) -> 
                     let heur = case happy_var_7 of {"SimHeur" -> SimilarityHeur; "DiffHeur" -> DifferenceHeur; "HausHeur" -> HausdorffHeur; lit -> error ("Heuristic not implemented parser.y4 - "++lit)} in
                     combSelHull (happy_var_5,heur) (getDisjuncts f) [] >>= \disj -> return (F (Or disj))
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_36 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_36 = happyReduce 8# 4# happyReduction_36
happyReduction_36 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	case happyOut11 happy_x_6 of { (HappyWrap11 happy_var_6) -> 
	happyIn8
		 (\env -> putStrFSOpt ("manualhull(" ++ happy_var_3 ++ "," ++ show happy_var_6 ++ ");") >>
                 case lookupVar happy_var_3 env of
                    Just (F f) -> 
                      let disj = getDisjuncts f in
                      if length disj == length happy_var_6 then
                        let grouped = groupDisjuncts (zip disj happy_var_6) (nub happy_var_6) (replicate (length (nub happy_var_6)) fFalse) in
                        mapM (\x -> hull x) grouped >>= \hulled ->
                        return (F (fOr hulled))
                      else
                        error ("Length of the list " ++ show happy_var_6 ++ " is different than the number of disjuncts in formula.")
                    _ -> error ("First argument of manualhull is not a formula.")
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_37 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_37 = happyReduce 8# 4# happyReduction_37
happyReduction_37 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	case happyOutTok happy_x_5 of { (TkAlphaNum happy_var_5) -> 
	case happyOutTok happy_x_7 of { (TkAlphaNum happy_var_7) -> 
	happyIn8
		 (\env -> putStrFSOpt ("narrow(" ++ happy_var_3 ++ "," ++ happy_var_5 ++ "," ++ happy_var_7 ++ ");") >>
                 case (lookupVar happy_var_3 env,lookupVar happy_var_5 env) of
                   (Just (F f1),Just (F f2)) -> 
                     let heur = case happy_var_7 of {"SimHeur" -> SimilarityHeur; "DiffHeur" -> DifferenceHeur; "HausHeur" -> HausdorffHeur; lit -> error ("Heuristic not implemented parser.y5 - "++lit)} in
                     narrow heur [] (getDisjuncts f1,getDisjuncts f2) >>= \disj ->
                     return (F (Or disj))
                   (Just (R recpost),_) -> error ("Argument of narrow is not a formula\n")
                   (_,Just (R recpost)) -> error ("Argument of narrow is not a formula\n")
                   (Just (QF qf),_) -> error ("Argument of narrow is not a formula\n")
                   (_,Just (QF qf)) -> error ("Argument of narrow is not a formula\n")
                   (_,_) -> error ("Variable not declared - "++happy_var_3++"\n")
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_38 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_38 = happyReduce 8# 4# happyReduction_38
happyReduction_38 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	case happyOutTok happy_x_5 of { (TkAlphaNum happy_var_5) -> 
	case happyOutTok happy_x_7 of { (TkAlphaNum happy_var_7) -> 
	happyIn8
		 (\env -> putStrFSOpt ("widen(" ++ happy_var_3 ++ "," ++ happy_var_5 ++ "," ++ happy_var_7 ++ ");") >>
                 case (lookupVar happy_var_3 env,lookupVar happy_var_5 env) of
                   (Just (F f1),Just (F f2)) -> 
                     let heur = case happy_var_7 of {"SimHeur" -> SimilarityHeur; "DiffHeur" -> DifferenceHeur; "HausHeur" -> HausdorffHeur; lit -> error ("Heuristic not implemented parser.y5 - "++lit)} in
                     widen heur [] (getDisjuncts f1,getDisjuncts f2) >>= \disj ->
                     return (F (Or disj))
                   (Just (R recpost),_) -> error ("Argument of widen is not a formula\n")
                   (_,Just (R recpost)) -> error ("Argument of widen is not a formula\n")
                   (Just (QF qf),_) -> error ("Argument of widen is not a formula\n")
                   (_,Just (QF qf)) -> error ("Argument of widen is not a formula\n")
                   (_,_) -> error ("Variable not declared - "++happy_var_3++"\n")
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_39 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_39 = happySpecReduce_3  4# happyReduction_39
happyReduction_39 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn8
		 (\env -> putStrFSOpt(happy_var_1 ++ " intersection " ++ happy_var_3 ++ ";") >>
                 case (lookupVar happy_var_1 env,lookupVar happy_var_3 env) of
                   (Just (F f1),Just (F f2)) ->
                      simplify (And [f1,f2]) >>= \f3 -> 
                      return (F f3)
                   (_,_) -> error ("Argument of intersection is not a valid formula\n")
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_40 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_40 = happySpecReduce_2  4# happyReduction_40
happyReduction_40 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_2 of { (TkAlphaNum happy_var_2) -> 
	happyIn8
		 (\env -> putStrFSOpt("hull " ++ happy_var_2 ++ ";") >>
                 case (lookupVar happy_var_2 env) of
                   Just (F f1) -> hull f1 >>= \f2 -> 
                      return (F f2)
                   _ -> error ("Argument of hull is not a valid formula\n")
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_41 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_41 = happySpecReduce_2  4# happyReduction_41
happyReduction_41 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_2 of { (TkAlphaNum happy_var_2) -> 
	happyIn8
		 (\env -> putStrFSOpt ("PairwiseCheck "++ happy_var_2) >>
                 case lookupVar happy_var_2 env of
                   Just (F f) -> 
                      pairwiseCheck f >>= \fsimpl ->
                      return (F fsimpl)
                   _ -> error ("Argument of pairwisecheck is not a valid formula "++happy_var_2++"\n")
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_42 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_42 = happySpecReduce_1  5# happyReduction_42
happyReduction_42 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	happyIn9
		 (\env -> case lookupVar happy_var_1 env of
       Just (F f) -> error ("Argument of bottomup is not a constraint abstraction\n")
       Just (QF qf) -> error ("Argument of bottomup is not a constraint abstraction\n")
       Nothing -> error ("Variable not declared - "++happy_var_1++"\n")
       Just (R recpost) -> [recpost]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_43 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_43 = happySpecReduce_3  5# happyReduction_43
happyReduction_43 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOut9 happy_x_3 of { (HappyWrap9 happy_var_3) -> 
	happyIn9
		 (\env -> case lookupVar happy_var_1 env of
       Just (F f) -> error ("Argument of bottomup is not a constraint abstraction\n")
       Just (QF qf) -> error ("Argument of bottomup is not a constraint abstraction\n")
       Nothing -> error ("Variable not declared - "++happy_var_1++"\n")
       Just (R recpost) -> recpost:(happy_var_3 env)
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_44 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_44 = happySpecReduce_1  6# happyReduction_44
happyReduction_44 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	happyIn10
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_45 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_45 = happySpecReduce_3  6# happyReduction_45
happyReduction_45 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOut10 happy_x_3 of { (HappyWrap10 happy_var_3) -> 
	happyIn10
		 (happy_var_1:happy_var_3
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_46 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_46 = happySpecReduce_1  7# happyReduction_46
happyReduction_46 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkIntNum happy_var_1) -> 
	happyIn11
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_47 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_47 = happySpecReduce_3  7# happyReduction_47
happyReduction_47 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkIntNum happy_var_1) -> 
	case happyOut11 happy_x_3 of { (HappyWrap11 happy_var_3) -> 
	happyIn11
		 (happy_var_1:happy_var_3
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_48 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_48 = happySpecReduce_1  8# happyReduction_48
happyReduction_48 happy_x_1
	 =  case happyOut13 happy_x_1 of { (HappyWrap13 happy_var_1) -> 
	happyIn12
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_49 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_49 = happySpecReduce_3  8# happyReduction_49
happyReduction_49 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn12
		 (happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_50 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_50 = happySpecReduce_3  8# happyReduction_50
happyReduction_50 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn12
		 (And [happy_var_1,happy_var_3]
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_51 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_51 = happySpecReduce_3  8# happyReduction_51
happyReduction_51 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn12
		 (Or [happy_var_1,happy_var_3]
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_52 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_52 = happySpecReduce_1  8# happyReduction_52
happyReduction_52 happy_x_1
	 =  happyIn12
		 (fTrue
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_53 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_53 = happySpecReduce_1  8# happyReduction_53
happyReduction_53 happy_x_1
	 =  happyIn12
		 (fFalse
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_54 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_54 = happySpecReduce_1  9# happyReduction_54
happyReduction_54 happy_x_1
	 =  case happyOut14 happy_x_1 of { (HappyWrap14 happy_var_1) -> 
	happyIn13
		 (let (f,rest)=happy_var_1 in f
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_55 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_55 = happyReduce 6# 9# happyReduction_55
happyReduction_55 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut20 happy_x_3 of { happy_var_3 -> 
	case happyOut12 happy_x_5 of { happy_var_5 -> 
	happyIn13
		 (fExists (reverse happy_var_3) happy_var_5
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_56 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_56 = happyReduce 6# 9# happyReduction_56
happyReduction_56 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut20 happy_x_3 of { happy_var_3 -> 
	case happyOut12 happy_x_5 of { happy_var_5 -> 
	happyIn13
		 (fForall (reverse happy_var_3) happy_var_5
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_57 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_57 = happyReduce 4# 9# happyReduction_57
happyReduction_57 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn13
		 (fNot happy_var_3
	) `HappyStk` happyRest}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_58 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_58 = happySpecReduce_1  10# happyReduction_58
happyReduction_58 happy_x_1
	 =  case happyOut15 happy_x_1 of { (HappyWrap15 happy_var_1) -> 
	happyIn14
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_59 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_59 = happyReduce 4# 10# happyReduction_59
happyReduction_59 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOut20 happy_x_3 of { happy_var_3 -> 
	happyIn14
		 ((AppRecPost happy_var_1 (reverse happy_var_3),[])
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_60 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_60 = happySpecReduce_3  10# happyReduction_60
happyReduction_60 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut14 happy_x_1 of { (HappyWrap14 happy_var_1) -> 
	case happyOut16 happy_x_2 of { (HappyWrap16 happy_var_2) -> 
	case happyOut17 happy_x_3 of { (HappyWrap17 happy_var_3) -> 
	happyIn14
		 (let (f,rest) = happy_var_1 in
    let third = reverse happy_var_3 in
    let combi = [(e1,e2) | e1 <- rest, e2 <- third] in
      case happy_var_2 of
        TkEq  -> 
          let newfs = map (\(e1,e2) -> EqK (e1 ++ (minus_update e2))) combi in 
            (And (f:newfs),third)
        TkGTE -> 
          let newfs = map (\(e1,e2) -> GEq (e1 ++ (minus_update e2))) combi in 
            (And (f:newfs),third)
        TkGT  ->
          let newfs = map (\(e1,e2) -> GEq ((Const (-1)):(e1 ++ minus_update e2))) combi in
            (And (f:newfs),third)
        TkLTE ->
          let newfs = map (\(e1,e2) -> GEq (e2 ++ (minus_update e1))) combi in
            (And (f:newfs),third)
        TkLT  ->
          let newfs = map (\(e1,e2) -> GEq ((Const (-1)):(e2 ++ minus_update e1))) combi in
            (And (f:newfs),third)
	)}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_61 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_61 = happySpecReduce_3  11# happyReduction_61
happyReduction_61 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut17 happy_x_1 of { (HappyWrap17 happy_var_1) -> 
	case happyOut16 happy_x_2 of { (HappyWrap16 happy_var_2) -> 
	case happyOut17 happy_x_3 of { (HappyWrap17 happy_var_3) -> 
	happyIn15
		 (let (first,third) = (reverse happy_var_1,reverse happy_var_3) in
    let combi = [(e1,e2) | e1 <- first, e2 <- third] in
    case happy_var_2 of
      TkEq -> 
        let newfs = map (\(e1,e2) -> (EqK (e1 ++ (minus_update e2)))) combi in
          if singleton newfs then (head newfs,third) else (And newfs,third)
      TkGTE -> 
        let newfs = map (\(e1,e2) -> (GEq (e1 ++ (minus_update e2)))) combi in 
          if singleton newfs then (head newfs,third) else (And newfs,third)
      TkGT  -> 
        let newfs = map (\(e1,e2) -> (GEq ((Const (- 1)):(e1 ++ (minus_update e2))) )) combi in
          if singleton newfs then (head newfs,third) else (And newfs,third)
      TkLTE -> 
        let newfs = map (\(e1,e2) -> (GEq (e2 ++ (minus_update e1)))) combi in 
          if singleton newfs then (head newfs,third) else (And newfs,third)
      TkLT  -> 
        let newfs = map (\(e1,e2) -> (GEq ((Const (- 1)):(e2 ++ (minus_update e1))) )) combi in
          if singleton newfs then (head newfs,third) else (And newfs,third)
	)}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_62 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_62 = happySpecReduce_1  12# happyReduction_62
happyReduction_62 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn16
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_63 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_63 = happySpecReduce_1  12# happyReduction_63
happyReduction_63 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn16
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_64 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_64 = happySpecReduce_1  12# happyReduction_64
happyReduction_64 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn16
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_65 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_65 = happySpecReduce_1  12# happyReduction_65
happyReduction_65 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn16
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_66 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_66 = happySpecReduce_1  12# happyReduction_66
happyReduction_66 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn16
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_67 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_67 = happySpecReduce_3  13# happyReduction_67
happyReduction_67 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut17 happy_x_1 of { (HappyWrap17 happy_var_1) -> 
	case happyOut18 happy_x_3 of { (HappyWrap18 happy_var_3) -> 
	happyIn17
		 (happy_var_3:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_68 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_68 = happySpecReduce_1  13# happyReduction_68
happyReduction_68 happy_x_1
	 =  case happyOut18 happy_x_1 of { (HappyWrap18 happy_var_1) -> 
	happyIn17
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_69 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_69 = happySpecReduce_3  14# happyReduction_69
happyReduction_69 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_1 of { (HappyWrap18 happy_var_1) -> 
	case happyOut18 happy_x_3 of { (HappyWrap18 happy_var_3) -> 
	happyIn18
		 (happy_var_1 ++ happy_var_3
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_70 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_70 = happySpecReduce_3  14# happyReduction_70
happyReduction_70 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_1 of { (HappyWrap18 happy_var_1) -> 
	case happyOut18 happy_x_3 of { (HappyWrap18 happy_var_3) -> 
	happyIn18
		 (happy_var_1 ++ (minus_update happy_var_3)
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_71 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_71 = happySpecReduce_3  14# happyReduction_71
happyReduction_71 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_2 of { (HappyWrap18 happy_var_2) -> 
	happyIn18
		 (happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_72 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_72 = happySpecReduce_2  14# happyReduction_72
happyReduction_72 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkIntNum happy_var_1) -> 
	case happyOut21 happy_x_2 of { (HappyWrap21 happy_var_2) -> 
	happyIn18
		 ([ Coef happy_var_2 happy_var_1 ]
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_73 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_73 = happySpecReduce_3  14# happyReduction_73
happyReduction_73 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_2 of { (TkIntNum happy_var_2) -> 
	case happyOut21 happy_x_3 of { (HappyWrap21 happy_var_3) -> 
	happyIn18
		 ([ Coef happy_var_3 (-happy_var_2) ]
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_74 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_74 = happySpecReduce_1  14# happyReduction_74
happyReduction_74 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkIntNum happy_var_1) -> 
	happyIn18
		 ([ Const happy_var_1 ]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_75 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_75 = happySpecReduce_2  14# happyReduction_75
happyReduction_75 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_2 of { (TkIntNum happy_var_2) -> 
	happyIn18
		 ([ Const (- happy_var_2)]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_76 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_76 = happySpecReduce_1  14# happyReduction_76
happyReduction_76 happy_x_1
	 =  case happyOut21 happy_x_1 of { (HappyWrap21 happy_var_1) -> 
	happyIn18
		 ([ Coef happy_var_1 1 ]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_77 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_77 = happySpecReduce_2  14# happyReduction_77
happyReduction_77 happy_x_2
	happy_x_1
	 =  case happyOut21 happy_x_2 of { (HappyWrap21 happy_var_2) -> 
	happyIn18
		 ([ Coef happy_var_2 (-1) ]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_78 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_78 = happySpecReduce_0  15# happyReduction_78
happyReduction_78  =  happyIn19
		 ([]
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_79 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_79 = happySpecReduce_1  15# happyReduction_79
happyReduction_79 happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	happyIn19
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_80 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_80 = happySpecReduce_3  16# happyReduction_80
happyReduction_80 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	case happyOut21 happy_x_3 of { (HappyWrap21 happy_var_3) -> 
	happyIn20
		 (happy_var_3:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_81 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_81 = happySpecReduce_1  16# happyReduction_81
happyReduction_81 happy_x_1
	 =  case happyOut21 happy_x_1 of { (HappyWrap21 happy_var_1) -> 
	happyIn20
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_82 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_82 = happySpecReduce_1  17# happyReduction_82
happyReduction_82 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	happyIn21
		 ((stringToQsv happy_var_1)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_83 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_83 = happySpecReduce_2  17# happyReduction_83
happyReduction_83 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	happyIn21
		 ((SizeVar happy_var_1,Primed)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_84 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_84 = happySpecReduce_2  17# happyReduction_84
happyReduction_84 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	happyIn21
		 ((SizeVar happy_var_1,Recursive)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_85 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_85 = happySpecReduce_3  17# happyReduction_85
happyReduction_85 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn21
		 (if (happy_var_3=="min") 
        then ((ArrSizeVar happy_var_1 Min),Unprimed)
        else 
          if (happy_var_3=="max") 
            then ((ArrSizeVar happy_var_1 Max),Unprimed) 
            else error $ "neither min or max after QSizeVar"
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_86 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_86 = happyReduce 4# 17# happyReduction_86
happyReduction_86 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn21
		 (if (happy_var_3=="min") 
        then ((ArrSizeVar happy_var_1 Min),Primed)
        else 
          if (happy_var_3=="max") 
            then ((ArrSizeVar happy_var_1 Max),Primed) 
            else error $ "neither min or max after QSizeVar"
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_87 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)
#endif
happyReduce_87 = happyReduce 4# 17# happyReduction_87
happyReduction_87 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn21
		 (if (happy_var_3=="min") 
        then ((ArrSizeVar happy_var_1 Min),Recursive)
        else 
          if (happy_var_3=="max") 
            then ((ArrSizeVar happy_var_1 Max),Recursive) 
            else error $ "neither min or max after QSizeVar"
	) `HappyStk` happyRest}}

happyNewToken action sts stk
	= lexer(\tk -> 
	let cont i = happyDoAction i tk action sts stk in
	case tk of {
	TkEOF -> happyDoAction 51# tk action sts stk;
	TkAlphaNum happy_dollar_dollar -> cont 1#;
	TkIntNum happy_dollar_dollar -> cont 2#;
	TkTrue -> cont 3#;
	TkFalse -> cont 4#;
	TkPlus -> cont 5#;
	TkMinus -> cont 6#;
	TkLBr -> cont 7#;
	TkRBr -> cont 8#;
	TkSemiColon -> cont 9#;
	TkAssign -> cont 10#;
	TkLSqBr -> cont 11#;
	TkRSqBr -> cont 12#;
	TkLAcc -> cont 13#;
	TkRAcc -> cont 14#;
	TkComma -> cont 15#;
	TkEq -> cont 16#;
	TkLT -> cont 17#;
	TkGT -> cont 18#;
	TkGTE -> cont 19#;
	TkLTE -> cont 20#;
	TkAnd -> cont 21#;
	TkOr -> cont 22#;
	TkColon -> cont 23#;
	TkDot -> cont 24#;
	TkNot -> cont 25#;
	TkExists -> cont 26#;
	TkForall -> cont 27#;
	TkPrime -> cont 28#;
	TkRec -> cont 29#;
	TkKwApply -> cont 30#;
	TkKwWiden -> cont 31#;
	TkKwNarrow -> cont 32#;
	TkKwSubset -> cont 33#;
	TkKwComplement -> cont 34#;
	TkKwBottomup -> cont 35#;
	TkKwBottomup_mr -> cont 36#;
	TkKwBottomup_gen -> cont 37#;
	TkKwTopdown -> cont 38#;
	TkKwGFP -> cont 39#;
	TkKwSelhull -> cont 40#;
	TkKwManualhull -> cont 41#;
	TkKwIntersection -> cont 42#;
	TkKwPairwisecheck -> cont 43#;
	TkKwHull -> cont 44#;
	TkKwFixtestpost -> cont 45#;
	TkKwFixtestinv -> cont 46#;
	TkKwPickEqFromEq -> cont 47#;
	TkKwPickGEqFromEq -> cont 48#;
	TkKwSatEQfromEQ -> cont 49#;
	TkKwSatGEQfromEQ -> cont 50#;
	_ -> happyError' (tk, [])
	})

happyError_ explist 51# tk = happyError' (tk, explist)
happyError_ explist _ tk = happyError' (tk, explist)

happyThen :: () => P a -> (a -> P b) -> P b
happyThen = (Prelude.>>=)
happyReturn :: () => a -> P a
happyReturn = (Prelude.return)
#if __GLASGOW_HASKELL__ >= 710
happyParse :: () => Happy_GHC_Exts.Int# -> P (HappyAbsSyn _ _ _)

happyNewToken :: () => Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)

happyDoAction :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _)

happyReduceArr :: () => Happy_Data_Array.Array Prelude.Int (Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _) -> P (HappyAbsSyn _ _ _))

#endif
happyThen1 :: () => P a -> (a -> P b) -> P b
happyThen1 = happyThen
happyReturn1 :: () => a -> P a
happyReturn1 = happyReturn
happyError' :: () => ((Tk), [Prelude.String]) -> P a
happyError' tk = (\(tokens, explist) -> happyError) tk
parseCalc = happySomeParser where
 happySomeParser = happyThen (happyParse 0#) (\x -> happyReturn (let {(HappyWrap4 x') = happyOut4 x} in x'))

happySeq = happyDontSeq


happyError :: P a
happyError = do l <- getLineNum
		s <- getInput
		error $ "Parse error on line " ++ (show l) ++ " rest of line: " ++ (takeWhile (/= '\n') s)

minus_update :: [Update] -> [Update]
minus_update [] = []
minus_update ((Const i):us) = (Const (- i)):(minus_update us)
minus_update ((Coef v i):us) = (Coef v (- i)):(minus_update us) 

--returning type varies depending on the grammar's start symbol
parse :: String -> Flags -> IO ()
parse s flags = 
  let listFunc = runP s parseCalc in
  let parseFuncFS = foldM (\env -> \func -> func env) emptyRelEnv listFunc in 
  runFS (initialState flags) parseFuncFS >>= \lastenv -> return ()

type RelEnv = [(Lit,Value)]

data Value = QF QFormula
  | F Formula
  | R RecPost

emptyRelEnv :: RelEnv
emptyRelEnv = []

extendRelEnv :: RelEnv -> (Lit,Value) -> RelEnv
extendRelEnv gamma (var,ty) = (var,ty):gamma

lookupVar :: Lit -> RelEnv -> Maybe Value
lookupVar lit [] = Nothing
lookupVar lit env@((v,f):rest) | (lit == v) = Just f
  | otherwise = lookupVar lit rest

groupDisjuncts:: [(Formula,Int)] -> [Int] -> [Formula] -> [Formula]
groupDisjuncts [] uniqueIds partialFormulae = partialFormulae
groupDisjuncts ((d,groupId):disj) uniqueIds partialFormulae =
  let ix = fromJust (elemIndex groupId uniqueIds) in
  let newPartialFormulae = updateList partialFormulae ix (Or [partialFormulae!!ix,d]) in
  groupDisjuncts disj uniqueIds newPartialFormulae
  
--updateList:: [a] -> (Int,a) -> [a]
--updateList xs (i,upd) = updateList1 xs (i,upd) 0
--  where
--  updateList1 xs (i,upd) j = 
--    if (i==j) then upd:(tail xs)
--    else updateList1 (tail xs) (i,upd) (j+1)
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $













-- Do not remove this comment. Required to fix CPP parsing when using GCC and a clang-compiled alex.
#if __GLASGOW_HASKELL__ > 706
#define LT(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.<# m)) :: Prelude.Bool)
#define GTE(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.>=# m)) :: Prelude.Bool)
#define EQ(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.==# m)) :: Prelude.Bool)
#else
#define LT(n,m) (n Happy_GHC_Exts.<# m)
#define GTE(n,m) (n Happy_GHC_Exts.>=# m)
#define EQ(n,m) (n Happy_GHC_Exts.==# m)
#endif



















data Happy_IntList = HappyCons Happy_GHC_Exts.Int# Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept 0# tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
        (happyTcHack j (happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
        = {- nothing -}
          case action of
                0#           -> {- nothing -}
                                     happyFail (happyExpListPerState ((Happy_GHC_Exts.I# (st)) :: Prelude.Int)) i tk st
                -1#          -> {- nothing -}
                                     happyAccept i tk st
                n | LT(n,(0# :: Happy_GHC_Exts.Int#)) -> {- nothing -}
                                                   (happyReduceArr Happy_Data_Array.! rule) i tk st
                                                   where rule = (Happy_GHC_Exts.I# ((Happy_GHC_Exts.negateInt# ((n Happy_GHC_Exts.+# (1# :: Happy_GHC_Exts.Int#))))))
                n                 -> {- nothing -}
                                     happyShift new_state i tk st
                                     where new_state = (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#))
   where off    = happyAdjustOffset (indexShortOffAddr happyActOffsets st)
         off_i  = (off Happy_GHC_Exts.+# i)
         check  = if GTE(off_i,(0# :: Happy_GHC_Exts.Int#))
                  then EQ(indexShortOffAddr happyCheck off_i, i)
                  else Prelude.False
         action
          | check     = indexShortOffAddr happyTable off_i
          | Prelude.otherwise = indexShortOffAddr happyDefActions st




indexShortOffAddr (HappyA# arr) off =
        Happy_GHC_Exts.narrow16Int# i
  where
        i = Happy_GHC_Exts.word2Int# (Happy_GHC_Exts.or# (Happy_GHC_Exts.uncheckedShiftL# high 8#) low)
        high = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr (off' Happy_GHC_Exts.+# 1#)))
        low  = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr off'))
        off' = off Happy_GHC_Exts.*# 2#




{-# INLINE happyLt #-}
happyLt x y = LT(x,y)


readArrayBit arr bit =
    Bits.testBit (Happy_GHC_Exts.I# (indexShortOffAddr arr ((unbox_int bit) `Happy_GHC_Exts.iShiftRA#` 4#))) (bit `Prelude.mod` 16)
  where unbox_int (Happy_GHC_Exts.I# x) = x






data HappyAddr = HappyA# Happy_GHC_Exts.Addr#


-----------------------------------------------------------------------------
-- HappyState data type (not arrays)













-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((happyInTok (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) sts of
         sts1@((HappyCons (st1@(action)) (_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
         let drop_stk = happyDropStk k stk

             off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st1)
             off_i = (off Happy_GHC_Exts.+# nt)
             new_state = indexShortOffAddr happyTable off_i




          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Happy_GHC_Exts.-# (1#::Happy_GHC_Exts.Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st)
         off_i = (off Happy_GHC_Exts.+# nt)
         new_state = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist 0# tk old_st _ stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (action) sts stk =
--      trace "entering error recovery" $
        happyDoAction 0# tk action sts ((Happy_GHC_Exts.unsafeCoerce# (Happy_GHC_Exts.I# (i))) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = Prelude.error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions


happyTcHack :: Happy_GHC_Exts.Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}


-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `Prelude.seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
