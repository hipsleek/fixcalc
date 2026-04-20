{-# OPTIONS_GHC -w #-}
{-# OPTIONS -XMagicHash -XBangPatterns -XTypeSynonymInstances -XFlexibleInstances -cpp #-}
#if __GLASGOW_HASKELL__ >= 710
{-# OPTIONS_GHC -XPartialTypeSignatures #-}
#endif
module ImpParser where
import ImpAST
import ImpLexer(runP,P(..),Tk(..),lexer,getLineNum,getInput)
import MyPrelude
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import qualified GHC.Exts as Happy_GHC_Exts
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.1.1

newtype HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56 = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
newtype HappyWrap5 = HappyWrap5 (IO Prog)
happyIn5 :: (IO Prog) -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn5 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap5 x)
{-# INLINE happyIn5 #-}
happyOut5 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> HappyWrap5
happyOut5 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut5 #-}
newtype HappyWrap6 = HappyWrap6 ([IO (String,String)])
happyIn6 :: ([IO (String,String)]) -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn6 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap6 x)
{-# INLINE happyIn6 #-}
happyOut6 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> HappyWrap6
happyOut6 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut6 #-}
happyIn7 :: t7 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn7 #-}
happyOut7 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t7
happyOut7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut7 #-}
happyIn8 :: t8 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn8 #-}
happyOut8 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t8
happyOut8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut8 #-}
happyIn9 :: t9 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn9 #-}
happyOut9 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t9
happyOut9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut9 #-}
happyIn10 :: t10 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t10
happyOut10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut10 #-}
happyIn11 :: t11 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t11
happyOut11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut11 #-}
happyIn12 :: t12 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn12 #-}
happyOut12 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t12
happyOut12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut12 #-}
happyIn13 :: t13 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t13
happyOut13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut13 #-}
happyIn14 :: t14 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t14
happyOut14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut14 #-}
happyIn15 :: t15 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn15 #-}
happyOut15 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t15
happyOut15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut15 #-}
happyIn16 :: t16 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn16 #-}
happyOut16 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t16
happyOut16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut16 #-}
happyIn17 :: t17 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn17 #-}
happyOut17 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t17
happyOut17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut17 #-}
happyIn18 :: t18 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn18 #-}
happyOut18 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t18
happyOut18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut18 #-}
happyIn19 :: t19 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn19 #-}
happyOut19 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t19
happyOut19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut19 #-}
happyIn20 :: t20 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn20 #-}
happyOut20 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t20
happyOut20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut20 #-}
happyIn21 :: t21 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn21 #-}
happyOut21 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t21
happyOut21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut21 #-}
happyIn22 :: t22 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn22 #-}
happyOut22 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t22
happyOut22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut22 #-}
happyIn23 :: t23 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn23 #-}
happyOut23 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t23
happyOut23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut23 #-}
happyIn24 :: t24 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn24 #-}
happyOut24 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t24
happyOut24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut24 #-}
happyIn25 :: t25 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn25 #-}
happyOut25 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t25
happyOut25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut25 #-}
happyIn26 :: t26 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn26 #-}
happyOut26 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t26
happyOut26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut26 #-}
happyIn27 :: t27 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn27 #-}
happyOut27 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t27
happyOut27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut27 #-}
happyIn28 :: t28 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn28 #-}
happyOut28 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t28
happyOut28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut28 #-}
happyIn29 :: t29 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn29 #-}
happyOut29 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t29
happyOut29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut29 #-}
happyIn30 :: t30 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn30 #-}
happyOut30 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t30
happyOut30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut30 #-}
happyIn31 :: t31 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn31 #-}
happyOut31 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t31
happyOut31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut31 #-}
happyIn32 :: t32 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn32 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn32 #-}
happyOut32 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t32
happyOut32 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut32 #-}
happyIn33 :: t33 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn33 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn33 #-}
happyOut33 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t33
happyOut33 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut33 #-}
happyIn34 :: t34 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn34 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn34 #-}
happyOut34 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t34
happyOut34 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut34 #-}
happyIn35 :: t35 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn35 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn35 #-}
happyOut35 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t35
happyOut35 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut35 #-}
happyIn36 :: t36 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn36 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn36 #-}
happyOut36 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t36
happyOut36 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut36 #-}
happyIn37 :: t37 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn37 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn37 #-}
happyOut37 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t37
happyOut37 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut37 #-}
happyIn38 :: t38 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn38 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn38 #-}
happyOut38 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t38
happyOut38 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut38 #-}
happyIn39 :: t39 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn39 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn39 #-}
happyOut39 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t39
happyOut39 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut39 #-}
happyIn40 :: t40 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn40 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn40 #-}
happyOut40 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t40
happyOut40 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut40 #-}
happyIn41 :: t41 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn41 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn41 #-}
happyOut41 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t41
happyOut41 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut41 #-}
happyIn42 :: t42 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn42 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn42 #-}
happyOut42 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t42
happyOut42 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut42 #-}
happyIn43 :: t43 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn43 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn43 #-}
happyOut43 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t43
happyOut43 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut43 #-}
happyIn44 :: t44 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn44 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn44 #-}
happyOut44 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t44
happyOut44 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut44 #-}
happyIn45 :: t45 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn45 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn45 #-}
happyOut45 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t45
happyOut45 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut45 #-}
happyIn46 :: t46 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn46 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn46 #-}
happyOut46 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t46
happyOut46 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut46 #-}
happyIn47 :: t47 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn47 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn47 #-}
happyOut47 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t47
happyOut47 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut47 #-}
happyIn48 :: t48 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn48 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn48 #-}
happyOut48 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t48
happyOut48 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut48 #-}
happyIn49 :: t49 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn49 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn49 #-}
happyOut49 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t49
happyOut49 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut49 #-}
newtype HappyWrap50 = HappyWrap50 (Formula)
happyIn50 :: (Formula) -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn50 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap50 x)
{-# INLINE happyIn50 #-}
happyOut50 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> HappyWrap50
happyOut50 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut50 #-}
newtype HappyWrap51 = HappyWrap51 ((Formula,[[Update]]))
happyIn51 :: ((Formula,[[Update]])) -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn51 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap51 x)
{-# INLINE happyIn51 #-}
happyOut51 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> HappyWrap51
happyOut51 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut51 #-}
newtype HappyWrap52 = HappyWrap52 ((Formula,[[Update]]))
happyIn52 :: ((Formula,[[Update]])) -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn52 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap52 x)
{-# INLINE happyIn52 #-}
happyOut52 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> HappyWrap52
happyOut52 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut52 #-}
newtype HappyWrap53 = HappyWrap53 (Tk)
happyIn53 :: (Tk) -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn53 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap53 x)
{-# INLINE happyIn53 #-}
happyOut53 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> HappyWrap53
happyOut53 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut53 #-}
newtype HappyWrap54 = HappyWrap54 ([[Update]])
happyIn54 :: ([[Update]]) -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn54 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap54 x)
{-# INLINE happyIn54 #-}
happyOut54 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> HappyWrap54
happyOut54 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut54 #-}
newtype HappyWrap55 = HappyWrap55 ([Update])
happyIn55 :: ([Update]) -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn55 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap55 x)
{-# INLINE happyIn55 #-}
happyOut55 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> HappyWrap55
happyOut55 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut55 #-}
happyIn56 :: t56 -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn56 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn56 #-}
happyOut56 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> t56
happyOut56 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut56 #-}
newtype HappyWrap57 = HappyWrap57 (QSizeVar)
happyIn57 :: (QSizeVar) -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyIn57 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap57 x)
{-# INLINE happyIn57 #-}
happyOut57 :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> HappyWrap57
happyOut57 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut57 #-}
happyInTok :: (Tk) -> (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56)
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t56) -> (Tk)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyExpList :: HappyAddr
happyExpList = HappyA# "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x78\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x07\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x07\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x12\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x78\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x30\x07\x00\x09\x00\xc0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x30\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe0\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xfc\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x06\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x03\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0\x1c\x00\x24\x00\x00\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\xc0\xed\x67\x24\x08\x00\x10\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x80\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x23\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0c\x00\x40\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x60\x00\x00\x12\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x03\x00\x90\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x18\x00\x80\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x60\x00\x00\x12\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x98\x03\x80\x04\x00\x60\x00\x00\x00\x00\x00\x00\x00\xc0\x1c\x00\x24\x00\x00\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0c\x00\x40\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x60\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x21\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe0\x01\x7c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x90\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb7\x00\x90\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\xb8\x05\x80\x04\x00\x00\x02\x00\x00\x00\x00\x00\x00\xc0\x2d\x00\x24\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x70\x0b\x00\x09\x00\x00\x04\x00\x00\x00\x00\x00\x00\x80\x5b\x00\x48\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf0\x02\x3e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xdc\x02\x40\x02\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x40\x0f\xe0\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x78\x00\x1f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc1\x03\xf8\x00\x00\x00\x00\x00\x00\x00\x00\xc0\x2d\x66\x24\x08\x00\x10\x00\x00\x00\x00\x00\x00\x00\x6e\x01\x20\x01\x00\x80\x00\x00\x00\x00\x00\x00\x00\x70\x8b\x19\x09\x02\x00\x04\x00\x00\x00\x00\x00\x00\x80\x5b\x00\x48\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\xdc\x02\x40\x02\x00\x00\x01\x00\x00\x00\x00\x00\x00\xe0\x16\x00\x12\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\xb7\x00\x90\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\xb8\x05\x80\x04\x00\x00\x02\x00\x00\x00\x00\x00\x00\xc0\x2d\x00\x24\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x6e\x01\x20\x01\x00\x80\x00\x00\x00\x00\x00\x00\x00\x70\x0b\x00\x09\x00\x00\x04\x00\x00\x00\x00\x00\x00\x80\x5b\x00\x48\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\xdc\x62\x46\x82\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x78\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0\x1c\x00\x24\x00\x00\x03\x00\x00\x00\x00\x00\x00\x00\xe6\x00\x20\x01\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x60\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x0c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x60\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x6e\x31\x23\x41\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x07\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x3c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe0\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x27\xf0\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x00\x00\x00\x00\x00\x00\x00\x00\x00\x6e\x01\x20\x01\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb7\x00\x90\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xdc\x62\x46\x82\x00\x00\x01\x00\x00\x00\x00\x00\x00\xe0\x16\x33\x12\x04\x00\x08\x00\x00\x00\x00\x00\x00\x00\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xdc\x02\x40\x02\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f\xe0\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x9e\xc0\x07\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb7\x00\x90\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0\x2d\x66\x24\x08\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\xdc\x02\x40\x02\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x2f\xe0\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x78\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_parseProg","%start_parseLPrimDecl","Prog","LInclude","LInclude1","Include","LPrimDecl","LPrimDecl1","PrimDecl","LMethDecl","LMethDecl1","MethDecl","Ref","LQLabel","LQLabel1","QLabel","Label","EB","LTypedParam","LTypedParam1","TypedParam","LLabelledFormula","LLabelledFormula1","LabelledFormula","LLabelledExp","LLabelledExp1","LabelledExp","LVarDecl","VarDecl","LVarorIntNum","LVar1","LIntNum","OptInit","AnnTy","AnnPrimTy","OptAnn","AnnArrTy","LAnnPrimTy","LExp","LExp1","Exp","SimpleExp","Var","Const","Num","FormulaWithBkt","Formula","QFormula","LBExpr","BExpr","RelOp","LAExpr","AExpr","LPorUSizeVar","PorUSizeVar","lit","intNum","floatNum","stringLit","true","false","bogus","void","int","bool","float","if","ifnd","then","else","while","for","do","ref","'+'","'-'","'*'","'/'","'('","')'","';'","':='","'['","']'","'{'","'}'","','","'='","'<'","'>'","'>='","'<='","'&&'","'||'","where","':'","'.'","exists","forall","prime","rec","'error'","'#'","'include'","%eof"]
        bit_start = st Prelude.* 107
        bit_end = (st Prelude.+ 1) Prelude.* 107
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..106]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\xf8\xff\x24\x02\xf8\xff\xee\xff\xf8\xff\x00\x00\x0a\x00\x56\x00\x24\x02\x00\x00\xc7\x00\xc2\x00\x00\x00\x00\x00\xc9\x00\xc9\x00\x00\x00\xdc\x00\x00\x00\x1f\x01\x00\x00\x24\x02\x17\x01\x00\x00\x3c\x01\x00\x00\x00\x00\xfd\xff\x00\x00\x24\x02\x00\x00\x6e\x01\x00\x00\x00\x00\x36\x00\x00\x00\xe8\xff\x3f\x01\x00\x00\x00\x00\x24\x02\x24\x02\x7d\x01\x8b\x01\x00\x00\x51\x01\x36\x00\xaf\x01\xc1\x01\xeb\x01\x00\x00\x00\x00\xda\x01\x00\x00\xdc\x01\xf9\xff\xdb\x01\x3c\x00\xf6\xff\x00\x00\x06\x02\x00\x00\xb4\x01\xe7\x00\x00\x00\x8d\x00\xfd\x01\x00\x00\x00\x00\x00\x00\x42\x01\x3c\x00\xec\x01\xef\x01\xf2\x01\x00\x00\x00\x00\xf5\x01\xf6\x01\x01\x00\x3b\x02\x46\x02\x46\x02\x35\x00\x2d\x01\x00\x00\x46\x02\x00\x00\x4f\x02\x00\x00\x00\x00\xd9\x00\xd9\x00\xd9\x00\xd9\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd9\x00\x00\x00\x3c\x00\x3c\x00\xf3\x01\x00\x00\x00\x02\xd9\x00\x41\x01\x00\x02\x00\x00\x00\x00\x3a\x01\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x62\x00\x50\x01\x00\x00\xfe\x01\x38\x02\x00\x00\x00\x00\x30\x02\x00\x00\x40\x02\x24\x00\x43\x00\x35\x01\xa5\x01\x06\x01\x00\x00\x00\x00\x33\x02\x00\x00\x00\x00\x00\x00\x00\x00\x61\x01\x32\x00\x32\x00\x32\x00\x43\x02\x32\x00\x32\x00\x00\x00\x69\x00\x3d\x02\x5d\x02\x37\x02\x68\x01\x00\x00\x00\x00\x32\x00\x4f\x01\x37\x01\x49\x01\x21\x00\x32\x00\x21\x00\x32\x00\x32\x00\x32\x00\x32\x00\x32\x00\x32\x00\x32\x00\x32\x00\x32\x00\x21\x00\x00\x00\x44\x02\x86\x01\x44\x02\x00\x00\x48\x01\x60\x02\x42\x02\x4b\x02\x63\x02\x64\x02\x3c\x00\x3c\x00\x00\x00\x00\x00\x2d\x01\x8f\x00\xc3\x00\x00\x00\x00\x00\x00\x00\x48\x02\x00\x00\x4c\x02\x4d\x02\xa1\x00\x00\x00\x00\x00\x21\x00\x4a\x02\x4e\x02\x50\x02\x00\x00\x00\x00\x00\x00\x00\x00\xaa\x01\xaa\x01\xaa\x01\xaa\x01\xaa\x01\x00\x00\x00\x00\x8e\x01\x8e\x01\x52\x02\x51\x02\x53\x02\x1c\x02\x59\x02\x55\x02\x55\x02\x55\x02\x7a\x01\x00\x00\x69\x02\x56\x02\x54\x02\x57\x02\xfa\xff\x32\x00\x00\x00\x5c\x02\x65\x02\x00\x00\x32\x00\x5b\x02\x76\x02\x78\x02\x79\x02\x00\x00\x21\x00\x21\x00\xb1\x01\x7a\x02\x00\x00\x00\x00\x58\x02\x5e\x02\x5f\x02\x00\x00\x61\x02\x66\x02\x67\x02\x6a\x02\x00\x00\x00\x00\x32\x00\xbc\x01\x68\x02\x68\x02\x8c\x01\x00\x00\x6b\x02\x6c\x02\x7b\x02\x7b\x02\x32\x00\x00\x00\x00\x00\x1c\x02\x00\x00\x00\x00\x6d\x02\x81\x02\x83\x02\x00\x00\x21\x00\x71\x02\x00\x00\x72\x02\x32\x00\x93\x01\x6f\x02\x70\x02\x62\x02\x73\x02\x74\x02\x86\x02\x75\x02\x7c\x02\x1c\x02\x00\x00\x00\x00\x77\x02\x6e\x02\x7d\x02\x90\x02\x7e\x02\x7f\x02\x80\x02\x82\x02\x00\x00\x84\x02\x85\x02\x88\x02\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\x34\x02\x26\x00\x4a\x00\x31\x02\x93\x02\x00\x00\x00\x00\x00\x00\x28\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x87\x02\x89\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x63\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd2\x01\x00\x00\xf0\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd5\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x8b\x02\x26\x02\x00\x00\x00\x00\x00\x00\x00\x00\xb3\x01\x53\x00\x00\x00\x00\x00\x00\x00\x00\x00\x8a\x02\x00\x00\x00\x00\x91\x02\x00\x00\xb9\x01\x00\x00\x00\x00\x8c\x02\x00\x00\x8d\x02\x00\x00\x00\x00\x00\x00\x8e\x02\x00\x00\x00\x00\x00\x00\x8f\x02\xc2\x01\x00\x00\x00\x00\x00\x00\x00\x00\x94\x02\x95\x02\x00\x00\x44\x00\x85\x01\x1f\x02\x21\x02\x00\x00\x00\x00\x00\x00\x92\x02\x00\x00\x00\x00\x00\x00\x00\x00\x75\x00\xbb\x00\x18\x02\x63\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1d\x02\x00\x00\xcb\x01\xd4\x01\x00\x00\x00\x00\x00\x00\x19\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x2e\x00\x98\x00\x9c\x00\x00\x00\xa2\x00\xa6\x00\x00\x00\x96\x02\x00\x00\x0e\x02\x00\x00\x00\x00\x00\x00\x00\x00\xaa\x00\x00\x00\x00\x00\x00\x00\x4b\x00\xae\x00\x54\x00\xb9\x00\xcb\x00\xcf\x00\xd6\x00\xda\x00\xde\x00\xe2\x00\xec\x00\xff\x00\x76\x00\x00\x00\x98\x02\x96\x00\x99\x02\x00\x00\xf3\xff\x0f\x01\x00\x00\x9a\x02\x9b\x02\x97\x02\xdd\x01\xe6\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7b\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x9d\x02\x9f\x02\xa0\x02\x00\x00\x00\x00\x9c\x02\x00\x00\x9e\x02\x00\x00\xa1\x02\x03\x01\x00\x00\x00\x00\x00\x00\x00\x00\x09\x01\x00\x00\x00\x00\xa2\x02\x00\x00\x00\x00\x68\x00\x71\x00\xfd\x00\xcc\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa9\x02\x00\x00\x00\x00\x0d\x01\x00\x00\xa3\x02\xa4\x02\x00\x00\x00\x00\x00\x00\x00\x00\x11\x02\x32\x02\x11\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x06\x00\x00\x00\x85\x00\x00\x00\x00\x00\xaa\x02\x15\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x49\x02\x00\x00\xa5\x02\x00\x00\x00\x00\x00\x00\xa6\x02\x00\x00\x00\x00\x36\x02\x00\x00\xab\x02\x00\x00\x00\x00\x00\x00\xa7\x02\x00\x00\xac\x02\x00\x00\x00\x00"#

happyAdjustOffset :: Happy_GHC_Exts.Int# -> Happy_GHC_Exts.Int#
happyAdjustOffset off = off

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\xfc\xff\xf7\xff\x00\x00\xea\xff\xfb\xff\xfa\xff\x00\x00\x00\x00\xf6\xff\xf5\xff\x00\x00\xc3\xff\xc2\xff\xc1\xff\xbd\xff\xbd\xff\xc0\xff\x00\x00\xbe\xff\x00\x00\xbf\xff\x00\x00\x00\x00\xf4\xff\x00\x00\xf9\xff\xfd\xff\xea\xff\xf0\xff\x00\x00\xe9\xff\x00\x00\xef\xff\xf8\xff\xea\xff\xba\xff\x00\x00\x00\x00\xbc\xff\xbb\xff\x00\x00\x00\x00\x00\x00\xdf\xff\xde\xff\x00\x00\xea\xff\xea\xff\x00\x00\x00\x00\xb9\xff\xdc\xff\x00\x00\xdd\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x90\xff\x89\xff\x86\xff\x00\x00\x7d\xff\x75\xff\x71\xff\x77\xff\x8c\xff\x8b\xff\x8a\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xeb\xff\xd1\xff\x00\x00\x00\x00\x00\x00\xdb\xff\x00\x00\x00\x00\x00\x00\x7d\xff\x74\xff\x76\xff\x79\xff\x00\x00\x70\xff\x6f\xff\x00\x00\x00\x00\x00\x00\x00\x00\x83\xff\x7f\xff\x81\xff\x82\xff\x80\xff\x00\x00\x91\xff\x00\x00\x00\x00\x8d\xff\x8e\xff\x85\xff\x00\x00\x7e\xff\x84\xff\x7b\xff\x7c\xff\x6e\xff\x78\xff\x7a\xff\x8f\xff\x00\x00\x72\xff\x00\x00\x00\x00\xe4\xff\x00\x00\xda\xff\xd9\xff\xe2\xff\x00\x00\xae\xff\x00\x00\x00\x00\x00\x00\x00\x00\xb4\xff\xaa\xff\xad\xff\x95\xff\x98\xff\x93\xff\x92\xff\x97\xff\x96\xff\xc1\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa6\xff\x00\x00\x00\x00\xdb\xff\x00\x00\x00\x00\x94\xff\xa7\xff\x00\x00\x00\x00\x00\x00\x00\x00\xb8\xff\x00\x00\xb8\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe1\xff\xc5\xff\x00\x00\xc5\xff\xd0\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x6d\xff\x6c\xff\x00\x00\x00\x00\x00\x00\x73\xff\xe3\xff\xd7\xff\x00\x00\xd8\xff\x00\x00\x00\x00\x00\x00\x98\xff\xcf\xff\x00\x00\x00\x00\xcb\xff\xca\xff\xc9\xff\xc7\xff\xce\xff\xb3\xff\x9d\xff\x9e\xff\x9f\xff\xa0\xff\xa1\xff\xa2\xff\xa3\xff\xa4\xff\xa5\xff\x00\x00\xb7\xff\xb6\xff\xab\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xac\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb0\xff\x00\x00\x00\x00\xa8\xff\x00\x00\x99\xff\x00\x00\x00\x00\x00\x00\xc4\xff\xb8\xff\xb8\xff\x00\x00\xd6\xff\x87\xff\x88\xff\x00\x00\x00\x00\xd5\xff\xd4\xff\x00\x00\x00\x00\x00\x00\xc5\xff\xc8\xff\xc6\xff\x00\x00\xb5\xff\x00\x00\x00\x00\x00\x00\xec\xff\x00\x00\x00\x00\xdb\xff\xe8\xff\x00\x00\xb1\xff\xb2\xff\x9b\xff\xcc\xff\xa9\xff\x9a\xff\x00\x00\x00\x00\xf3\xff\x00\x00\xd2\xff\xd3\xff\xc5\xff\x00\x00\x00\x00\x00\x00\xe7\xff\xe6\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x9c\xff\xcd\xff\xaf\xff\x00\x00\xe5\xff\x00\x00\xe8\xff\x00\x00\x00\x00\x00\x00\x00\x00\xee\xff\x00\x00\x00\x00\x00\x00\xed\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x13\x00\x01\x00\x02\x00\x03\x00\x1d\x00\x05\x00\x06\x00\x20\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x19\x00\x13\x00\x10\x00\x11\x00\x20\x00\x0e\x00\x22\x00\x15\x00\x1e\x00\x1e\x00\x18\x00\x20\x00\x28\x00\x26\x00\x27\x00\x18\x00\x1e\x00\x32\x00\x28\x00\x01\x00\x02\x00\x03\x00\x01\x00\x05\x00\x06\x00\x30\x00\x08\x00\x04\x00\x05\x00\x06\x00\x0c\x00\x0d\x00\x32\x00\x2f\x00\x10\x00\x11\x00\x01\x00\x02\x00\x03\x00\x15\x00\x05\x00\x06\x00\x18\x00\x08\x00\x31\x00\x0e\x00\x01\x00\x02\x00\x1e\x00\x1c\x00\x05\x00\x06\x00\x07\x00\x01\x00\x1f\x00\x20\x00\x15\x00\x22\x00\x13\x00\x18\x00\x01\x00\x02\x00\x03\x00\x19\x00\x19\x00\x2f\x00\x15\x00\x0e\x00\x0f\x00\x18\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x0e\x00\x0f\x00\x26\x00\x27\x00\x0a\x00\x1a\x00\x1c\x00\x20\x00\x2f\x00\x0e\x00\x0f\x00\x20\x00\x12\x00\x22\x00\x2b\x00\x2c\x00\x29\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x0e\x00\x0f\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x0e\x00\x0f\x00\x18\x00\x20\x00\x20\x00\x0e\x00\x0f\x00\x23\x00\x1e\x00\x32\x00\x0e\x00\x0f\x00\x29\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x0e\x00\x0f\x00\x24\x00\x25\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x0e\x00\x32\x00\x19\x00\x34\x00\x0e\x00\x26\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x0e\x00\x1b\x00\x1c\x00\x1d\x00\x0e\x00\x26\x00\x27\x00\x2a\x00\x0e\x00\x18\x00\x2d\x00\x2e\x00\x0e\x00\x1c\x00\x28\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x0e\x00\x01\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x0e\x00\x01\x00\x02\x00\x19\x00\x0e\x00\x1c\x00\x0a\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x0e\x00\x10\x00\x11\x00\x12\x00\x0e\x00\x26\x00\x27\x00\x22\x00\x0e\x00\x32\x00\x15\x00\x34\x00\x0e\x00\x18\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x0e\x00\x14\x00\x15\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x0e\x00\x32\x00\x1f\x00\x20\x00\x0e\x00\x22\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x0e\x00\x1b\x00\x1c\x00\x1d\x00\x0e\x00\x0d\x00\x0e\x00\x18\x00\x0e\x00\x01\x00\x1b\x00\x1c\x00\x0e\x00\x15\x00\x28\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x06\x00\x18\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x04\x00\x14\x00\x15\x00\x01\x00\x02\x00\x0e\x00\x19\x00\x1f\x00\x20\x00\x01\x00\x22\x00\x14\x00\x15\x00\x16\x00\x17\x00\x1a\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x1f\x00\x14\x00\x15\x00\x0e\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x14\x00\x15\x00\x16\x00\x17\x00\x12\x00\x23\x00\x14\x00\x15\x00\x16\x00\x17\x00\x2d\x00\x2e\x00\x18\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x01\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x14\x00\x15\x00\x16\x00\x17\x00\x29\x00\x2a\x00\x1a\x00\x14\x00\x15\x00\x16\x00\x17\x00\x1f\x00\x19\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x01\x00\x02\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x14\x00\x15\x00\x16\x00\x17\x00\x0d\x00\x0e\x00\x1a\x00\x32\x00\x19\x00\x34\x00\x13\x00\x14\x00\x15\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x14\x00\x15\x00\x16\x00\x17\x00\x16\x00\x17\x00\x1a\x00\x14\x00\x15\x00\x16\x00\x17\x00\x20\x00\x19\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x01\x00\x02\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x14\x00\x15\x00\x16\x00\x17\x00\x0a\x00\x14\x00\x15\x00\x16\x00\x17\x00\x13\x00\x10\x00\x11\x00\x12\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x14\x00\x15\x00\x16\x00\x17\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x0e\x00\x09\x00\x0a\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x16\x00\x17\x00\x18\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x28\x00\x31\x00\x32\x00\x01\x00\x34\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x18\x00\x31\x00\x32\x00\x19\x00\x34\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x20\x00\x31\x00\x32\x00\x01\x00\x34\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x18\x00\x31\x00\x32\x00\x18\x00\x34\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x18\x00\x31\x00\x32\x00\x1e\x00\x34\x00\x2c\x00\x2d\x00\x2e\x00\x2f\x00\x20\x00\x31\x00\x32\x00\x26\x00\x34\x00\x0d\x00\x0e\x00\x1f\x00\x0d\x00\x0e\x00\x20\x00\x13\x00\x14\x00\x15\x00\x13\x00\x14\x00\x15\x00\x21\x00\x22\x00\x23\x00\x24\x00\x25\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x14\x00\x15\x00\x16\x00\x17\x00\x00\x00\x01\x00\x02\x00\x03\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x01\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x1f\x00\x20\x00\x01\x00\x22\x00\x31\x00\x32\x00\x32\x00\x34\x00\x34\x00\x31\x00\x32\x00\x01\x00\x34\x00\x33\x00\x34\x00\x33\x00\x34\x00\x0d\x00\x0e\x00\x20\x00\x29\x00\x1a\x00\x18\x00\x29\x00\x20\x00\x01\x00\x1b\x00\x29\x00\x01\x00\x20\x00\x18\x00\x01\x00\x01\x00\x1e\x00\x1d\x00\x1c\x00\x1c\x00\x01\x00\x0f\x00\x18\x00\x1a\x00\x20\x00\x1d\x00\x20\x00\x20\x00\x19\x00\x1e\x00\x0f\x00\x1f\x00\x1b\x00\x20\x00\x02\x00\x01\x00\x01\x00\x01\x00\x01\x00\x1f\x00\x1d\x00\x20\x00\x19\x00\x29\x00\x01\x00\x1d\x00\x01\x00\x1b\x00\x1e\x00\x01\x00\x1b\x00\x1e\x00\x1e\x00\x1a\x00\x2a\x00\x1b\x00\x1f\x00\x18\x00\x20\x00\x01\x00\x1f\x00\xff\xff\x20\x00\x20\x00\x03\x00\xff\xff\x2a\x00\xff\xff\x1e\x00\x1e\x00\x18\x00\x1e\x00\x20\x00\x1f\x00\x0f\x00\xff\xff\x20\x00\xff\xff\xff\xff\x20\x00\x1e\x00\xff\xff\x21\x00\x0e\x00\x21\x00\x20\x00\x0f\x00\x19\x00\x0f\x00\x0f\x00\x0f\x00\xff\xff\x0f\x00\x0f\x00\x0f\x00\x2b\x00\x1e\x00\x1e\x00\xff\xff\xff\xff\x0f\x00\x0f\x00\x30\x00\x30\x00\xff\xff\xff\xff\x2b\x00\x2b\x00\x34\x00\x34\x00\x28\x00\x2b\x00\x34\x00\x1e\x00\x1e\x00\x2b\x00\x28\x00\x34\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x2b\x00\x2b\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x1f\x00\x88\x00\x89\x00\x8a\x00\x28\x00\x8b\x00\x8c\x00\x29\x00\x8d\x00\x0f\x00\x10\x00\x11\x00\x8e\x00\x8f\x00\x66\x00\x1f\x00\x90\x00\x91\x00\xc3\x00\xf9\x00\xc4\x00\x92\x00\x4d\x00\x4d\x00\x93\x00\x0a\x01\xc5\x00\x67\x00\x68\x00\x19\x01\x4d\x00\xf2\xff\x4e\x00\x88\x00\x89\x00\x8a\x00\xb0\x00\x8b\x00\x8c\x00\x07\x00\x9a\x00\x07\x00\x08\x00\x09\x00\x8e\x00\x8f\x00\xf1\xff\x94\x00\x90\x00\x91\x00\x88\x00\x89\x00\x8a\x00\x92\x00\x8b\x00\x8c\x00\x93\x00\x9a\x00\x19\x00\x97\x00\x42\x00\x43\x00\x4d\x00\x16\x00\x44\x00\x45\x00\x46\x00\xae\x00\x0a\x00\x0b\x00\x92\x00\x0c\x00\x1f\x00\x93\x00\x03\x00\x04\x00\x05\x00\x74\x00\xe0\xff\x94\x00\x47\x00\x7d\x00\x7e\x00\x48\x00\x9e\x00\x84\x00\x85\x00\x86\x00\x97\x00\x7e\x00\x67\x00\x68\x00\x29\x00\x7f\x00\xaf\x00\xb7\x00\x94\x00\x97\x00\x7e\x00\x80\x00\x35\x00\x81\x00\x49\x00\x4a\x00\xb9\x00\x82\x00\x83\x00\x84\x00\x85\x00\x86\x00\xdd\x00\xda\x00\xdb\x00\x83\x00\x84\x00\x85\x00\x86\x00\x97\x00\x7e\x00\xd9\x00\xda\x00\xdb\x00\x83\x00\x84\x00\x85\x00\x86\x00\x97\x00\x7e\x00\x3a\x00\xb7\x00\x23\x00\x97\x00\x7e\x00\x24\x00\x97\x00\xff\xff\x97\x00\x7e\x00\xb8\x00\xff\x00\xda\x00\xdb\x00\x83\x00\x84\x00\x85\x00\x86\x00\x97\x00\x7e\x00\xfe\x00\xda\x00\xdb\x00\x83\x00\x84\x00\x85\x00\x86\x00\xcf\x00\x83\x00\x84\x00\x85\x00\x86\x00\xf2\x00\x83\x00\x84\x00\x85\x00\x86\x00\x97\x00\x6f\x00\xf9\x00\x40\x00\x97\x00\x18\x01\x83\x00\x84\x00\x85\x00\x86\x00\x97\x00\xc9\x00\xca\x00\xcb\x00\x97\x00\x67\x00\x68\x00\x59\x00\x97\x00\xf4\x00\x5a\x00\x5b\x00\x97\x00\xf5\x00\xcc\x00\x9d\x00\x84\x00\x85\x00\x86\x00\x9c\x00\x84\x00\x85\x00\x86\x00\x97\x00\x17\x00\x9a\x00\x84\x00\x85\x00\x86\x00\x98\x00\x84\x00\x85\x00\x86\x00\xe1\x00\x84\x00\x85\x00\x86\x00\xdc\x00\x84\x00\x85\x00\x86\x00\x97\x00\x42\x00\x43\x00\xf8\x00\x97\x00\x16\x00\x29\x00\xd8\x00\x84\x00\x85\x00\x86\x00\x97\x00\x2a\x00\x2b\x00\x2c\x00\x97\x00\x67\x00\x68\x00\x14\x00\x97\x00\x6e\x00\x47\x00\x40\x00\x97\x00\x6c\x00\xd7\x00\x84\x00\x85\x00\x86\x00\xd6\x00\x84\x00\x85\x00\x86\x00\x97\x00\x5c\x00\x5d\x00\xd5\x00\x84\x00\x85\x00\x86\x00\xd4\x00\x84\x00\x85\x00\x86\x00\xd3\x00\x84\x00\x85\x00\x86\x00\xd2\x00\x84\x00\x85\x00\x86\x00\x97\x00\xff\xff\x1f\x00\x0b\x00\x97\x00\x0c\x00\xd1\x00\x84\x00\x85\x00\x86\x00\x97\x00\xfd\x00\xca\x00\xcb\x00\x97\x00\x77\x00\x78\x00\xa0\x00\x97\x00\x26\x00\xa1\x00\xa2\x00\x97\x00\xc2\x00\xcc\x00\xd0\x00\x84\x00\x85\x00\x86\x00\x07\x01\x84\x00\x85\x00\x86\x00\x17\x00\x23\x00\x04\x01\x84\x00\x85\x00\x86\x00\x10\x01\x84\x00\x85\x00\x86\x00\x1c\x01\x84\x00\x85\x00\x86\x00\x25\x01\x84\x00\x85\x00\x86\x00\x22\x00\x5c\x00\x5d\x00\x42\x00\x57\x00\xe0\x00\x73\x00\x0a\x00\x0b\x00\xc7\x00\x0c\x00\xa3\x00\xa4\x00\xa5\x00\xa6\x00\xac\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xad\x00\x5c\x00\x5d\x00\xdf\x00\xa7\x00\xa8\x00\xa9\x00\xaa\x00\xab\x00\xa3\x00\xa4\x00\xa5\x00\xa6\x00\xe1\x00\x27\x00\xa3\x00\xa4\x00\xa5\x00\xa6\x00\xba\x00\xbb\x00\x2f\x00\xa7\x00\xa8\x00\xa9\x00\xaa\x00\xab\x00\x2e\x00\xa7\x00\xa8\x00\xa9\x00\xaa\x00\xab\x00\x94\xff\x94\xff\x94\xff\x94\xff\xb5\x00\xb6\x00\x94\xff\xa3\x00\xa4\x00\xa5\x00\xa6\x00\x94\xff\xe3\x00\x94\xff\x94\xff\x94\xff\x94\xff\x94\xff\xc7\x00\xce\x00\xa7\x00\xa8\x00\xa9\x00\xaa\x00\xab\x00\xa3\x00\xa4\x00\xa5\x00\xa6\x00\x77\x00\x78\x00\xe9\x00\x6c\x00\x31\x00\x40\x00\x79\x00\x7a\x00\x7b\x00\xa7\x00\xa8\x00\xa9\x00\xaa\x00\xab\x00\xa3\x00\xa4\x00\xa5\x00\xa6\x00\xa5\x00\xa6\x00\x0e\x01\xa3\x00\xa4\x00\xa5\x00\xa6\x00\x30\x00\x25\x01\xa7\x00\xa8\x00\xa9\x00\xaa\x00\xab\x00\xc7\x00\xce\x00\xa7\x00\xa8\x00\xa9\x00\xaa\x00\xab\x00\xa3\x00\xa4\x00\xa5\x00\xa6\x00\x29\x00\xa3\x00\xa4\x00\xa5\x00\xa6\x00\x1f\x00\x36\x00\x2b\x00\x2c\x00\xa7\x00\xa8\x00\xa9\x00\xaa\x00\xab\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa3\x00\xa4\x00\xa5\x00\xa6\x00\x5f\x00\x60\x00\x61\x00\x62\x00\x63\x00\x64\x00\xf9\x00\x20\x00\x1d\x00\xa7\x00\xa8\x00\xa9\x00\xaa\x00\xab\x00\xfa\x00\xfb\x00\xfc\x00\x3a\x00\x3b\x00\x3c\x00\x3d\x00\x35\x00\x3e\x00\x3f\x00\x34\x00\x40\x00\x53\x00\x3b\x00\x3c\x00\x3d\x00\x3a\x00\x3e\x00\x54\x00\x38\x00\x40\x00\x69\x00\x3b\x00\x3c\x00\x3d\x00\x4b\x00\x3e\x00\x3f\x00\x42\x00\x40\x00\x68\x00\x3b\x00\x3c\x00\x3d\x00\x53\x00\x3e\x00\x3f\x00\x52\x00\x40\x00\xbd\x00\x3b\x00\x3c\x00\x3d\x00\x3a\x00\x3e\x00\x3f\x00\x51\x00\x40\x00\xbc\x00\x3b\x00\x3c\x00\x3d\x00\x95\x00\x3e\x00\x3f\x00\x67\x00\x40\x00\x77\x00\x78\x00\xb4\x00\x77\x00\x78\x00\x5f\x00\xe4\x00\x7a\x00\x7b\x00\x20\x01\x7a\x00\x7b\x00\x60\x00\x61\x00\x62\x00\x63\x00\x64\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xa3\x00\xa4\x00\xa5\x00\xa6\x00\x11\x00\x03\x00\x04\x00\x05\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x7d\x00\x1d\x01\x1e\x01\x1f\x01\x78\x00\x2e\x01\x1e\x01\x1f\x01\x78\x00\x31\x00\x0b\x00\x42\x00\x0c\x00\x6d\x00\x3f\x00\xbb\x00\x40\x00\x40\x00\x6a\x00\x3f\x00\x71\x00\x40\x00\x76\x00\x75\x00\x74\x00\x75\x00\x29\x01\x78\x00\xb3\x00\xb2\x00\xb1\x00\x9c\x00\xe2\xff\xe6\x00\x7d\x00\xc9\x00\xe4\x00\x7d\x00\xc2\x00\x3a\x00\x7d\x00\x42\x00\xf7\x00\xf2\x00\x16\x00\xf6\x00\xc7\x00\x07\x01\x3a\x00\xac\x00\xf1\x00\xef\x00\xf0\x00\xee\x00\xed\x00\x4d\x00\x06\x01\xe8\x00\x04\x01\x0b\x01\x03\x01\xc7\x00\x01\x01\x7d\x00\x7d\x00\x17\x01\x15\x01\x16\x01\x13\x01\x18\x01\x1b\x01\x14\x01\x7d\x00\xc9\x00\x4d\x00\x7d\x00\x1c\x01\x0d\x01\x0c\x01\xac\x00\xb6\x00\xc9\x00\x24\x01\x3a\x00\x23\x01\x7d\x00\x22\x01\x00\x00\x2b\x01\x29\x01\x19\x00\x00\x00\xb6\x00\x00\x00\x4d\x00\x2c\x01\x3a\x00\x4d\x00\x2e\x01\x30\x01\x4b\x00\x00\x00\x32\x01\x00\x00\x00\x00\x34\x01\x4d\x00\x00\x00\x14\x00\xbf\x00\x12\x00\x32\x00\xeb\x00\x4f\x00\xea\x00\xe9\x00\x08\x01\x00\x00\x0f\x01\x0e\x01\x27\x01\x38\x00\xce\x00\xc7\x00\x00\x00\x00\x00\x30\x01\x34\x01\x64\x00\x5d\x00\x00\x00\x00\x00\x4e\x00\x95\x00\x57\x00\x55\x00\xc5\x00\xc0\x00\x71\x00\x11\x01\x26\x01\xe6\x00\x01\x01\xbe\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x2c\x01\x32\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (2, 147) [
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
	(87 , happyReduce_87),
	(88 , happyReduce_88),
	(89 , happyReduce_89),
	(90 , happyReduce_90),
	(91 , happyReduce_91),
	(92 , happyReduce_92),
	(93 , happyReduce_93),
	(94 , happyReduce_94),
	(95 , happyReduce_95),
	(96 , happyReduce_96),
	(97 , happyReduce_97),
	(98 , happyReduce_98),
	(99 , happyReduce_99),
	(100 , happyReduce_100),
	(101 , happyReduce_101),
	(102 , happyReduce_102),
	(103 , happyReduce_103),
	(104 , happyReduce_104),
	(105 , happyReduce_105),
	(106 , happyReduce_106),
	(107 , happyReduce_107),
	(108 , happyReduce_108),
	(109 , happyReduce_109),
	(110 , happyReduce_110),
	(111 , happyReduce_111),
	(112 , happyReduce_112),
	(113 , happyReduce_113),
	(114 , happyReduce_114),
	(115 , happyReduce_115),
	(116 , happyReduce_116),
	(117 , happyReduce_117),
	(118 , happyReduce_118),
	(119 , happyReduce_119),
	(120 , happyReduce_120),
	(121 , happyReduce_121),
	(122 , happyReduce_122),
	(123 , happyReduce_123),
	(124 , happyReduce_124),
	(125 , happyReduce_125),
	(126 , happyReduce_126),
	(127 , happyReduce_127),
	(128 , happyReduce_128),
	(129 , happyReduce_129),
	(130 , happyReduce_130),
	(131 , happyReduce_131),
	(132 , happyReduce_132),
	(133 , happyReduce_133),
	(134 , happyReduce_134),
	(135 , happyReduce_135),
	(136 , happyReduce_136),
	(137 , happyReduce_137),
	(138 , happyReduce_138),
	(139 , happyReduce_139),
	(140 , happyReduce_140),
	(141 , happyReduce_141),
	(142 , happyReduce_142),
	(143 , happyReduce_143),
	(144 , happyReduce_144),
	(145 , happyReduce_145),
	(146 , happyReduce_146),
	(147 , happyReduce_147)
	]

happy_n_terms = 51 :: Prelude.Int
happy_n_nonterms = 53 :: Prelude.Int

#if __GLASGOW_HASKELL__ >= 710
happyReduce_2 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_2 = happySpecReduce_2  0# happyReduction_2
happyReduction_2 happy_x_2
	happy_x_1
	 =  case happyOut6 happy_x_1 of { (HappyWrap6 happy_var_1) -> 
	case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn5
		 (sequence happy_var_1 >>= \incl -> 
  let (inclFilenames,inclStrs) = unzip incl in
  let inclPrims = runP (concat inclStrs) parseLPrimDecl in
	  return $ Prog inclFilenames inclPrims (reverse happy_var_2)
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_3 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_3 = happySpecReduce_0  1# happyReduction_3
happyReduction_3  =  happyIn6
		 ([]
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_4 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_4 = happySpecReduce_1  1# happyReduction_4
happyReduction_4 happy_x_1
	 =  case happyOut7 happy_x_1 of { happy_var_1 -> 
	happyIn6
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_5 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_5 = happySpecReduce_1  2# happyReduction_5
happyReduction_5 happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	happyIn7
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_6 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_6 = happySpecReduce_2  2# happyReduction_6
happyReduction_6 happy_x_2
	happy_x_1
	 =  case happyOut7 happy_x_1 of { happy_var_1 -> 
	case happyOut8 happy_x_2 of { happy_var_2 -> 
	happyIn7
		 (happy_var_2:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_7 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_7 = happySpecReduce_3  3# happyReduction_7
happyReduction_7 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_3 of { (TkString happy_var_3) -> 
	happyIn8
		 (--  putStrLn ("Include..."++happy_var_3) >> 
  readFile happy_var_3 >>= \contents ->  
  return (happy_var_3,(' ':contents))
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_8 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_8 = happySpecReduce_0  4# happyReduction_8
happyReduction_8  =  happyIn9
		 ([]
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_9 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_9 = happySpecReduce_1  4# happyReduction_9
happyReduction_9 happy_x_1
	 =  case happyOut10 happy_x_1 of { happy_var_1 -> 
	happyIn9
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_10 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_10 = happySpecReduce_1  5# happyReduction_10
happyReduction_10 happy_x_1
	 =  case happyOut11 happy_x_1 of { happy_var_1 -> 
	happyIn10
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_11 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_11 = happySpecReduce_2  5# happyReduction_11
happyReduction_11 happy_x_2
	happy_x_1
	 =  case happyOut10 happy_x_1 of { happy_var_1 -> 
	case happyOut11 happy_x_2 of { happy_var_2 -> 
	happyIn10
		 (happy_var_2:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_12 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_12 = happyReduce 15# 6# happyReduction_12
happyReduction_12 (happy_x_15 `HappyStk`
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
	 = case happyOut36 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { (TkAlphaNum happy_var_2) -> 
	case happyOut21 happy_x_4 of { happy_var_4 -> 
	case happyOut48 happy_x_7 of { happy_var_7 -> 
	case happyOut24 happy_x_10 of { happy_var_10 -> 
	case happyOut27 happy_x_14 of { happy_var_14 -> 
	happyIn11
		 (PrimDecl {primParams=((PassByVal,happy_var_1,happy_var_2):(reverse happy_var_4)),
              primPost=happy_var_7,
              primPres=(reverse happy_var_10),
              primTests=(reverse happy_var_14)}
	) `HappyStk` happyRest}}}}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_13 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_13 = happySpecReduce_0  7# happyReduction_13
happyReduction_13  =  happyIn12
		 ([]
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_14 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_14 = happySpecReduce_1  7# happyReduction_14
happyReduction_14 happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	happyIn12
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_15 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_15 = happySpecReduce_1  8# happyReduction_15
happyReduction_15 happy_x_1
	 =  case happyOut14 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_16 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_16 = happySpecReduce_2  8# happyReduction_16
happyReduction_16 happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut14 happy_x_2 of { happy_var_2 -> 
	happyIn13
		 (happy_var_2:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_17 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_17 = happyReduce 20# 9# happyReduction_17
happyReduction_17 (happy_x_20 `HappyStk`
	happy_x_19 `HappyStk`
	happy_x_18 `HappyStk`
	happy_x_17 `HappyStk`
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
	 = case happyOut15 happy_x_1 of { happy_var_1 -> 
	case happyOut36 happy_x_2 of { happy_var_2 -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	case happyOut21 happy_x_5 of { happy_var_5 -> 
	case happyOut48 happy_x_8 of { happy_var_8 -> 
	case happyOut24 happy_x_11 of { happy_var_11 -> 
	case happyOut16 happy_x_15 of { happy_var_15 -> 
	case happyOut48 happy_x_18 of { happy_var_18 -> 
	case happyOut20 happy_x_20 of { happy_var_20 -> 
	happyIn14
		 (MethDecl {methParams=((happy_var_1,happy_var_2,happy_var_3):(reverse happy_var_5)),
             methExternal=False,
             methPost=[happy_var_8,fTrue,fTrue],
             methPres=(reverse happy_var_11),
             methUpsis=(reverse happy_var_15),
             methInv=happy_var_18,
             methOK=FormulaBogus,methERRs=[],
             methNEVER=FormulaBogus,methMUSTs=[],methMAY=([],FormulaBogus),
             methBody=happy_var_20}
	) `HappyStk` happyRest}}}}}}}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_18 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_18 = happyReduce 24# 9# happyReduction_18
happyReduction_18 (happy_x_24 `HappyStk`
	happy_x_23 `HappyStk`
	happy_x_22 `HappyStk`
	happy_x_21 `HappyStk`
	happy_x_20 `HappyStk`
	happy_x_19 `HappyStk`
	happy_x_18 `HappyStk`
	happy_x_17 `HappyStk`
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
	 = case happyOut15 happy_x_1 of { happy_var_1 -> 
	case happyOut36 happy_x_2 of { happy_var_2 -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	case happyOut21 happy_x_5 of { happy_var_5 -> 
	case happyOut48 happy_x_8 of { happy_var_8 -> 
	case happyOut48 happy_x_10 of { happy_var_10 -> 
	case happyOut48 happy_x_12 of { happy_var_12 -> 
	case happyOut24 happy_x_15 of { happy_var_15 -> 
	case happyOut16 happy_x_19 of { happy_var_19 -> 
	case happyOut48 happy_x_22 of { happy_var_22 -> 
	case happyOut20 happy_x_24 of { happy_var_24 -> 
	happyIn14
		 (MethDecl {methParams=((happy_var_1,happy_var_2,happy_var_3):(reverse happy_var_5)),
              methExternal=False,
              methPost=[happy_var_8,happy_var_10,happy_var_12],
              methPres=(reverse happy_var_15),
              methUpsis=(reverse happy_var_19),
              methInv=happy_var_22,
              methOK=FormulaBogus,methERRs=[],
              methNEVER=FormulaBogus,methMUSTs=[],methMAY=([],FormulaBogus),
              methBody=happy_var_24}
	) `HappyStk` happyRest}}}}}}}}}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_19 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_19 = happyReduce 13# 9# happyReduction_19
happyReduction_19 (happy_x_13 `HappyStk`
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
	 = case happyOut15 happy_x_1 of { happy_var_1 -> 
	case happyOut36 happy_x_2 of { happy_var_2 -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	case happyOut21 happy_x_5 of { happy_var_5 -> 
	case happyOut48 happy_x_8 of { happy_var_8 -> 
	case happyOut24 happy_x_11 of { happy_var_11 -> 
	case happyOut20 happy_x_13 of { happy_var_13 -> 
	happyIn14
		 (MethDecl {methParams=((happy_var_1,happy_var_2,happy_var_3):(reverse happy_var_5)),
              methExternal=False,
              methPost=[happy_var_8,fTrue,fTrue],
              methPres=(reverse happy_var_11),
              methUpsis=[],
              methInv=FormulaBogus,
              methOK=FormulaBogus,methERRs=[],
              methNEVER=FormulaBogus,methMUSTs=[],methMAY=([],FormulaBogus),
              methBody=happy_var_13}
	) `HappyStk` happyRest}}}}}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_20 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_20 = happyReduce 7# 9# happyReduction_20
happyReduction_20 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut15 happy_x_1 of { happy_var_1 -> 
	case happyOut36 happy_x_2 of { happy_var_2 -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	case happyOut21 happy_x_5 of { happy_var_5 -> 
	case happyOut20 happy_x_7 of { happy_var_7 -> 
	happyIn14
		 (MethDecl {methParams=((happy_var_1,happy_var_2,happy_var_3):(reverse happy_var_5)),
              methExternal=False,
              methPost=(triple FormulaBogus),
              methPres=[],
              methUpsis=[],
              methInv=FormulaBogus,
              methOK=FormulaBogus,methERRs=[],
              methNEVER=FormulaBogus,methMUSTs=[],methMAY=([],FormulaBogus),
              methBody=happy_var_7}
	) `HappyStk` happyRest}}}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_21 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_21 = happySpecReduce_0  10# happyReduction_21
happyReduction_21  =  happyIn15
		 (PassByVal
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_22 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_22 = happySpecReduce_1  10# happyReduction_22
happyReduction_22 happy_x_1
	 =  happyIn15
		 (PassByRef
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_23 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_23 = happySpecReduce_0  11# happyReduction_23
happyReduction_23  =  happyIn16
		 ([]
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_24 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_24 = happySpecReduce_1  11# happyReduction_24
happyReduction_24 happy_x_1
	 =  case happyOut17 happy_x_1 of { happy_var_1 -> 
	happyIn16
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_25 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_25 = happySpecReduce_1  12# happyReduction_25
happyReduction_25 happy_x_1
	 =  case happyOut18 happy_x_1 of { happy_var_1 -> 
	happyIn17
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_26 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_26 = happySpecReduce_3  12# happyReduction_26
happyReduction_26 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut17 happy_x_1 of { happy_var_1 -> 
	case happyOut18 happy_x_3 of { happy_var_3 -> 
	happyIn17
		 (happy_var_3:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_27 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_27 = happySpecReduce_1  13# happyReduction_27
happyReduction_27 happy_x_1
	 =  case happyOut19 happy_x_1 of { happy_var_1 -> 
	happyIn18
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_28 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_28 = happySpecReduce_3  13# happyReduction_28
happyReduction_28 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_1 of { happy_var_1 -> 
	case happyOut19 happy_x_3 of { happy_var_3 -> 
	happyIn18
		 (happy_var_3:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_29 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_29 = happySpecReduce_1  14# happyReduction_29
happyReduction_29 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	happyIn19
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_30 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_30 = happyReduce 4# 15# happyReduction_30
happyReduction_30 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut30 happy_x_2 of { happy_var_2 -> 
	case happyOut43 happy_x_3 of { happy_var_3 -> 
	happyIn20
		 (ExpBlock (reverse happy_var_2) happy_var_3
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_31 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_31 = happySpecReduce_0  16# happyReduction_31
happyReduction_31  =  happyIn21
		 ([]
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_32 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_32 = happySpecReduce_1  16# happyReduction_32
happyReduction_32 happy_x_1
	 =  case happyOut22 happy_x_1 of { happy_var_1 -> 
	happyIn21
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_33 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_33 = happySpecReduce_1  17# happyReduction_33
happyReduction_33 happy_x_1
	 =  case happyOut23 happy_x_1 of { happy_var_1 -> 
	happyIn22
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_34 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_34 = happySpecReduce_3  17# happyReduction_34
happyReduction_34 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut22 happy_x_1 of { happy_var_1 -> 
	case happyOut23 happy_x_3 of { happy_var_3 -> 
	happyIn22
		 (happy_var_3:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_35 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_35 = happySpecReduce_3  18# happyReduction_35
happyReduction_35 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut15 happy_x_1 of { happy_var_1 -> 
	case happyOut36 happy_x_2 of { happy_var_2 -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn23
		 ((happy_var_1,happy_var_2,happy_var_3)
	)}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_36 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_36 = happySpecReduce_0  19# happyReduction_36
happyReduction_36  =  happyIn24
		 ([]
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_37 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_37 = happySpecReduce_1  19# happyReduction_37
happyReduction_37 happy_x_1
	 =  case happyOut25 happy_x_1 of { happy_var_1 -> 
	happyIn24
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_38 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_38 = happySpecReduce_1  20# happyReduction_38
happyReduction_38 happy_x_1
	 =  case happyOut26 happy_x_1 of { happy_var_1 -> 
	happyIn25
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_39 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_39 = happySpecReduce_3  20# happyReduction_39
happyReduction_39 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut25 happy_x_1 of { happy_var_1 -> 
	case happyOut26 happy_x_3 of { happy_var_3 -> 
	happyIn25
		 (happy_var_3:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_40 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_40 = happySpecReduce_3  21# happyReduction_40
happyReduction_40 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_1 of { happy_var_1 -> 
	case happyOut48 happy_x_3 of { happy_var_3 -> 
	happyIn26
		 (((reverse happy_var_1),happy_var_3)
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_41 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_41 = happySpecReduce_0  22# happyReduction_41
happyReduction_41  =  happyIn27
		 ([]
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_42 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_42 = happySpecReduce_1  22# happyReduction_42
happyReduction_42 happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	happyIn27
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_43 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_43 = happySpecReduce_1  23# happyReduction_43
happyReduction_43 happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	happyIn28
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_44 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_44 = happySpecReduce_3  23# happyReduction_44
happyReduction_44 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_1 of { happy_var_1 -> 
	case happyOut29 happy_x_3 of { happy_var_3 -> 
	happyIn28
		 (happy_var_3:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_45 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_45 = happySpecReduce_3  24# happyReduction_45
happyReduction_45 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut19 happy_x_1 of { happy_var_1 -> 
	case happyOut43 happy_x_3 of { happy_var_3 -> 
	happyIn29
		 ((happy_var_1,happy_var_3)
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_46 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_46 = happySpecReduce_0  25# happyReduction_46
happyReduction_46  =  happyIn30
		 ([]
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_47 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_47 = happySpecReduce_3  25# happyReduction_47
happyReduction_47 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut30 happy_x_1 of { happy_var_1 -> 
	case happyOut31 happy_x_2 of { happy_var_2 -> 
	happyIn30
		 (happy_var_2:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_48 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_48 = happySpecReduce_3  26# happyReduction_48
happyReduction_48 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { (TkAlphaNum happy_var_2) -> 
	case happyOut35 happy_x_3 of { happy_var_3 -> 
	happyIn31
		 (VarDecl happy_var_1 happy_var_2 happy_var_3
	)}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_49 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_49 = happySpecReduce_3  26# happyReduction_49
happyReduction_49 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut39 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_2 of { (TkAlphaNum happy_var_2) -> 
	case happyOut35 happy_x_3 of { happy_var_3 -> 
	happyIn31
		 (VarDecl happy_var_1 happy_var_2 happy_var_3
	)}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_50 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_50 = happyReduce 8# 26# happyReduction_50
happyReduction_50 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut19 happy_x_1 of { happy_var_1 -> 
	case happyOut39 happy_x_3 of { happy_var_3 -> 
	case happyOut32 happy_x_5 of { happy_var_5 -> 
	case happyOutTok happy_x_7 of { (TkAlphaNum happy_var_7) -> 
	case happyOut35 happy_x_8 of { happy_var_8 -> 
	happyIn31
		 (LblArrVarDecl (Just happy_var_1) happy_var_3 (reverse happy_var_5) happy_var_7 happy_var_8
	) `HappyStk` happyRest}}}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_51 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_51 = happyReduce 6# 26# happyReduction_51
happyReduction_51 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut39 happy_x_1 of { happy_var_1 -> 
	case happyOut32 happy_x_3 of { happy_var_3 -> 
	case happyOutTok happy_x_5 of { (TkAlphaNum happy_var_5) -> 
	case happyOut35 happy_x_6 of { happy_var_6 -> 
	happyIn31
		 (LblArrVarDecl Nothing happy_var_1 (reverse happy_var_3) happy_var_5 happy_var_6
	) `HappyStk` happyRest}}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_52 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_52 = happySpecReduce_1  27# happyReduction_52
happyReduction_52 happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	happyIn32
		 (map (\v -> ExpVar v) happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_53 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_53 = happySpecReduce_1  27# happyReduction_53
happyReduction_53 happy_x_1
	 =  case happyOut34 happy_x_1 of { happy_var_1 -> 
	happyIn32
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_54 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_54 = happySpecReduce_1  28# happyReduction_54
happyReduction_54 happy_x_1
	 =  case happyOut45 happy_x_1 of { happy_var_1 -> 
	happyIn33
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_55 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_55 = happySpecReduce_3  28# happyReduction_55
happyReduction_55 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	case happyOut45 happy_x_3 of { happy_var_3 -> 
	happyIn33
		 (happy_var_3:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_56 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_56 = happySpecReduce_1  29# happyReduction_56
happyReduction_56 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkIntNum happy_var_1) -> 
	happyIn34
		 ([KIntNum happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_57 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_57 = happySpecReduce_3  29# happyReduction_57
happyReduction_57 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut34 happy_x_1 of { happy_var_1 -> 
	case happyOutTok happy_x_3 of { (TkIntNum happy_var_3) -> 
	happyIn34
		 (KIntNum happy_var_3:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_58 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_58 = happySpecReduce_0  30# happyReduction_58
happyReduction_58  =  happyIn35
		 (ExpBogus
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_59 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_59 = happySpecReduce_2  30# happyReduction_59
happyReduction_59 happy_x_2
	happy_x_1
	 =  case happyOut43 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_60 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_60 = happySpecReduce_1  31# happyReduction_60
happyReduction_60 happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	happyIn36
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_61 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_61 = happySpecReduce_1  31# happyReduction_61
happyReduction_61 happy_x_1
	 =  case happyOut39 happy_x_1 of { happy_var_1 -> 
	happyIn36
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_62 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_62 = happySpecReduce_1  32# happyReduction_62
happyReduction_62 happy_x_1
	 =  happyIn37
		 (PrimVoid{anno=Nothing}
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_63 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_63 = happySpecReduce_1  32# happyReduction_63
happyReduction_63 happy_x_1
	 =  happyIn37
		 (PrimFloat{anno=Nothing}
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_64 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_64 = happySpecReduce_2  32# happyReduction_64
happyReduction_64 happy_x_2
	happy_x_1
	 =  case happyOut38 happy_x_2 of { happy_var_2 -> 
	happyIn37
		 (PrimInt{anno=happy_var_2}
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_65 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_65 = happySpecReduce_2  32# happyReduction_65
happyReduction_65 happy_x_2
	happy_x_1
	 =  case happyOut38 happy_x_2 of { happy_var_2 -> 
	happyIn37
		 (PrimBool{anno=happy_var_2}
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_66 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_66 = happySpecReduce_0  33# happyReduction_66
happyReduction_66  =  happyIn38
		 (Nothing
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_67 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_67 = happySpecReduce_3  33# happyReduction_67
happyReduction_67 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_2 of { (TkAlphaNum happy_var_2) -> 
	happyIn38
		 ((Just happy_var_2)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_68 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_68 = happyReduce 4# 34# happyReduction_68
happyReduction_68 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut37 happy_x_1 of { happy_var_1 -> 
	case happyOut40 happy_x_3 of { happy_var_3 -> 
	happyIn39
		 (ArrayType happy_var_1 (reverse happy_var_3)
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_69 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_69 = happySpecReduce_1  35# happyReduction_69
happyReduction_69 happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	happyIn40
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_70 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_70 = happySpecReduce_3  35# happyReduction_70
happyReduction_70 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut40 happy_x_1 of { happy_var_1 -> 
	case happyOut37 happy_x_3 of { happy_var_3 -> 
	happyIn40
		 (happy_var_3:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_71 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_71 = happySpecReduce_0  36# happyReduction_71
happyReduction_71  =  happyIn41
		 ([]
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_72 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_72 = happySpecReduce_1  36# happyReduction_72
happyReduction_72 happy_x_1
	 =  case happyOut42 happy_x_1 of { happy_var_1 -> 
	happyIn41
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_73 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_73 = happySpecReduce_1  37# happyReduction_73
happyReduction_73 happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	happyIn42
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_74 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_74 = happySpecReduce_3  37# happyReduction_74
happyReduction_74 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut42 happy_x_1 of { happy_var_1 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn42
		 (happy_var_3:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_75 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_75 = happySpecReduce_1  38# happyReduction_75
happyReduction_75 happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	happyIn43
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_76 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_76 = happySpecReduce_3  38# happyReduction_76
happyReduction_76 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	case happyOut43 happy_x_3 of { happy_var_3 -> 
	happyIn43
		 (Seq happy_var_1 happy_var_3
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_77 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_77 = happyReduce 6# 38# happyReduction_77
happyReduction_77 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut44 happy_x_2 of { happy_var_2 -> 
	case happyOut20 happy_x_4 of { happy_var_4 -> 
	case happyOut20 happy_x_6 of { happy_var_6 -> 
	happyIn43
		 (If False happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_78 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_78 = happyReduce 6# 38# happyReduction_78
happyReduction_78 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut44 happy_x_2 of { happy_var_2 -> 
	case happyOut20 happy_x_4 of { happy_var_4 -> 
	case happyOut20 happy_x_6 of { happy_var_6 -> 
	happyIn43
		 (If True happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_79 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_79 = happyReduce 4# 38# happyReduction_79
happyReduction_79 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut44 happy_x_2 of { happy_var_2 -> 
	case happyOut20 happy_x_4 of { happy_var_4 -> 
	happyIn43
		 (While happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_80 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_80 = happyReduce 9# 38# happyReduction_80
happyReduction_80 (happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut44 happy_x_3 of { happy_var_3 -> 
	case happyOut44 happy_x_5 of { happy_var_5 -> 
	case happyOut44 happy_x_7 of { happy_var_7 -> 
	case happyOut20 happy_x_9 of { happy_var_9 -> 
	happyIn43
		 (For happy_var_3 happy_var_5 happy_var_7 happy_var_9
	) `HappyStk` happyRest}}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_81 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_81 = happySpecReduce_1  38# happyReduction_81
happyReduction_81 happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	happyIn43
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_82 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_82 = happySpecReduce_1  39# happyReduction_82
happyReduction_82 happy_x_1
	 =  case happyOut46 happy_x_1 of { happy_var_1 -> 
	happyIn44
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_83 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_83 = happySpecReduce_3  39# happyReduction_83
happyReduction_83 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_2 of { happy_var_2 -> 
	happyIn44
		 (happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_84 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_84 = happySpecReduce_3  39# happyReduction_84
happyReduction_84 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut45 happy_x_1 of { happy_var_1 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (AssignVar happy_var_1 happy_var_3
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_85 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_85 = happySpecReduce_1  39# happyReduction_85
happyReduction_85 happy_x_1
	 =  case happyOut45 happy_x_1 of { happy_var_1 -> 
	happyIn44
		 (ExpVar happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_86 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_86 = happyReduce 6# 39# happyReduction_86
happyReduction_86 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut19 happy_x_1 of { happy_var_1 -> 
	case happyOut45 happy_x_3 of { happy_var_3 -> 
	case happyOut41 happy_x_5 of { happy_var_5 -> 
	happyIn44
		 (LblMethCall (Just happy_var_1) happy_var_3 (reverse happy_var_5)
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_87 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_87 = happyReduce 4# 39# happyReduction_87
happyReduction_87 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut45 happy_x_1 of { happy_var_1 -> 
	case happyOut41 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (LblMethCall Nothing happy_var_1 (reverse happy_var_3)
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_88 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_88 = happySpecReduce_2  39# happyReduction_88
happyReduction_88 happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_2 of { happy_var_2 -> 
	happyIn44
		 (LblMethCall (Nothing) "minus" ((KIntNum 0):[happy_var_2])
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_89 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_89 = happySpecReduce_1  39# happyReduction_89
happyReduction_89 happy_x_1
	 =  happyIn44
		 (ExpError
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_90 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_90 = happySpecReduce_3  39# happyReduction_90
happyReduction_90 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (LblMethCall (Nothing) "plus" (happy_var_1:[happy_var_3])
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_91 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_91 = happySpecReduce_3  39# happyReduction_91
happyReduction_91 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (LblMethCall (Nothing) "minus" (happy_var_1:[happy_var_3])
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_92 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_92 = happySpecReduce_3  39# happyReduction_92
happyReduction_92 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (LblMethCall (Nothing) "mul" (happy_var_1:[happy_var_3])
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_93 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_93 = happySpecReduce_3  39# happyReduction_93
happyReduction_93 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (LblMethCall (Nothing) "divide" (happy_var_1:[happy_var_3])
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_94 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_94 = happySpecReduce_3  39# happyReduction_94
happyReduction_94 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (LblMethCall (Nothing) "eq" (happy_var_1:[happy_var_3])
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_95 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_95 = happySpecReduce_3  39# happyReduction_95
happyReduction_95 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (LblMethCall (Nothing) "lt" (happy_var_1:[happy_var_3])
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_96 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_96 = happySpecReduce_3  39# happyReduction_96
happyReduction_96 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (LblMethCall (Nothing) "gt" (happy_var_1:[happy_var_3])
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_97 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_97 = happySpecReduce_3  39# happyReduction_97
happyReduction_97 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (LblMethCall (Nothing) "gte" (happy_var_1:[happy_var_3])
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_98 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_98 = happySpecReduce_3  39# happyReduction_98
happyReduction_98 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOut44 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (LblMethCall (Nothing) "lte" (happy_var_1:[happy_var_3])
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_99 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_99 = happyReduce 8# 39# happyReduction_99
happyReduction_99 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut19 happy_x_1 of { happy_var_1 -> 
	case happyOut45 happy_x_3 of { happy_var_3 -> 
	case happyOut41 happy_x_5 of { happy_var_5 -> 
	case happyOut44 happy_x_8 of { happy_var_8 -> 
	happyIn44
		 (LblMethCall (Just happy_var_1) "assign" ((ExpVar happy_var_3):(reverse (happy_var_8:happy_var_5)))
	) `HappyStk` happyRest}}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_100 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_100 = happyReduce 6# 39# happyReduction_100
happyReduction_100 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut45 happy_x_1 of { happy_var_1 -> 
	case happyOut41 happy_x_3 of { happy_var_3 -> 
	case happyOut44 happy_x_6 of { happy_var_6 -> 
	happyIn44
		 (LblMethCall Nothing "assign" ((ExpVar happy_var_1):(reverse (happy_var_6:happy_var_3)))
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_101 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_101 = happyReduce 6# 39# happyReduction_101
happyReduction_101 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut19 happy_x_1 of { happy_var_1 -> 
	case happyOut45 happy_x_3 of { happy_var_3 -> 
	case happyOut41 happy_x_5 of { happy_var_5 -> 
	happyIn44
		 (LblMethCall (Just happy_var_1) "sub" ((ExpVar happy_var_3):(reverse happy_var_5))
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_102 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_102 = happyReduce 4# 39# happyReduction_102
happyReduction_102 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut45 happy_x_1 of { happy_var_1 -> 
	case happyOut41 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (LblMethCall Nothing "sub" ((ExpVar happy_var_1):(reverse happy_var_3))
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_103 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_103 = happySpecReduce_1  40# happyReduction_103
happyReduction_103 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	happyIn45
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_104 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_104 = happySpecReduce_1  41# happyReduction_104
happyReduction_104 happy_x_1
	 =  happyIn46
		 (KTrue
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_105 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_105 = happySpecReduce_1  41# happyReduction_105
happyReduction_105 happy_x_1
	 =  happyIn46
		 (KFalse
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_106 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_106 = happySpecReduce_1  41# happyReduction_106
happyReduction_106 happy_x_1
	 =  case happyOut47 happy_x_1 of { happy_var_1 -> 
	happyIn46
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_107 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_107 = happySpecReduce_1  41# happyReduction_107
happyReduction_107 happy_x_1
	 =  happyIn46
		 (KVoid
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_108 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_108 = happySpecReduce_1  42# happyReduction_108
happyReduction_108 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkIntNum happy_var_1) -> 
	happyIn47
		 (KIntNum happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_109 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_109 = happySpecReduce_1  42# happyReduction_109
happyReduction_109 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkFloatNum happy_var_1) -> 
	happyIn47
		 (KFloatNum happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_110 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_110 = happySpecReduce_3  43# happyReduction_110
happyReduction_110 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut49 happy_x_2 of { happy_var_2 -> 
	happyIn48
		 (happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_111 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_111 = happySpecReduce_1  44# happyReduction_111
happyReduction_111 happy_x_1
	 =  case happyOut50 happy_x_1 of { (HappyWrap50 happy_var_1) -> 
	happyIn49
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_112 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_112 = happySpecReduce_3  44# happyReduction_112
happyReduction_112 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut49 happy_x_2 of { happy_var_2 -> 
	happyIn49
		 (happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_113 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_113 = happySpecReduce_3  44# happyReduction_113
happyReduction_113 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut49 happy_x_1 of { happy_var_1 -> 
	case happyOut49 happy_x_3 of { happy_var_3 -> 
	happyIn49
		 (And [happy_var_1,happy_var_3]
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_114 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_114 = happySpecReduce_3  44# happyReduction_114
happyReduction_114 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut49 happy_x_1 of { happy_var_1 -> 
	case happyOut49 happy_x_3 of { happy_var_3 -> 
	happyIn49
		 (Or [happy_var_1,happy_var_3]
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_115 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_115 = happySpecReduce_1  44# happyReduction_115
happyReduction_115 happy_x_1
	 =  happyIn49
		 (fTrue
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_116 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_116 = happySpecReduce_1  44# happyReduction_116
happyReduction_116 happy_x_1
	 =  happyIn49
		 (fFalse
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_117 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_117 = happySpecReduce_1  44# happyReduction_117
happyReduction_117 happy_x_1
	 =  happyIn49
		 (FormulaBogus
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_118 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_118 = happySpecReduce_1  45# happyReduction_118
happyReduction_118 happy_x_1
	 =  case happyOut51 happy_x_1 of { (HappyWrap51 happy_var_1) -> 
	happyIn50
		 (let (f,rest)=happy_var_1 in f
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_119 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_119 = happyReduce 6# 45# happyReduction_119
happyReduction_119 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut56 happy_x_3 of { happy_var_3 -> 
	case happyOut49 happy_x_5 of { happy_var_5 -> 
	happyIn50
		 (fExists (reverse happy_var_3) happy_var_5
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_120 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_120 = happyReduce 6# 45# happyReduction_120
happyReduction_120 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut56 happy_x_3 of { happy_var_3 -> 
	case happyOut49 happy_x_5 of { happy_var_5 -> 
	happyIn50
		 (fForall (reverse happy_var_3) happy_var_5
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_121 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_121 = happySpecReduce_1  46# happyReduction_121
happyReduction_121 happy_x_1
	 =  case happyOut52 happy_x_1 of { (HappyWrap52 happy_var_1) -> 
	happyIn51
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_122 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_122 = happySpecReduce_3  46# happyReduction_122
happyReduction_122 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut51 happy_x_1 of { (HappyWrap51 happy_var_1) -> 
	case happyOut53 happy_x_2 of { (HappyWrap53 happy_var_2) -> 
	case happyOut54 happy_x_3 of { (HappyWrap54 happy_var_3) -> 
	happyIn51
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
happyReduce_123 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_123 = happySpecReduce_3  47# happyReduction_123
happyReduction_123 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut54 happy_x_1 of { (HappyWrap54 happy_var_1) -> 
	case happyOut53 happy_x_2 of { (HappyWrap53 happy_var_2) -> 
	case happyOut54 happy_x_3 of { (HappyWrap54 happy_var_3) -> 
	happyIn52
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
happyReduce_124 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_124 = happySpecReduce_1  48# happyReduction_124
happyReduction_124 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn53
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_125 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_125 = happySpecReduce_1  48# happyReduction_125
happyReduction_125 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn53
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_126 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_126 = happySpecReduce_1  48# happyReduction_126
happyReduction_126 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn53
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_127 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_127 = happySpecReduce_1  48# happyReduction_127
happyReduction_127 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn53
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_128 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_128 = happySpecReduce_1  48# happyReduction_128
happyReduction_128 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn53
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_129 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_129 = happySpecReduce_3  49# happyReduction_129
happyReduction_129 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut54 happy_x_1 of { (HappyWrap54 happy_var_1) -> 
	case happyOut55 happy_x_3 of { (HappyWrap55 happy_var_3) -> 
	happyIn54
		 (happy_var_3:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_130 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_130 = happySpecReduce_1  49# happyReduction_130
happyReduction_130 happy_x_1
	 =  case happyOut55 happy_x_1 of { (HappyWrap55 happy_var_1) -> 
	happyIn54
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_131 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_131 = happySpecReduce_3  50# happyReduction_131
happyReduction_131 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut55 happy_x_1 of { (HappyWrap55 happy_var_1) -> 
	case happyOut55 happy_x_3 of { (HappyWrap55 happy_var_3) -> 
	happyIn55
		 (happy_var_1 ++ happy_var_3
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_132 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_132 = happySpecReduce_3  50# happyReduction_132
happyReduction_132 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut55 happy_x_1 of { (HappyWrap55 happy_var_1) -> 
	case happyOut55 happy_x_3 of { (HappyWrap55 happy_var_3) -> 
	happyIn55
		 (happy_var_1 ++ (minus_update happy_var_3)
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_133 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_133 = happySpecReduce_3  50# happyReduction_133
happyReduction_133 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut55 happy_x_2 of { (HappyWrap55 happy_var_2) -> 
	happyIn55
		 (happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_134 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_134 = happySpecReduce_2  50# happyReduction_134
happyReduction_134 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkIntNum happy_var_1) -> 
	case happyOut57 happy_x_2 of { (HappyWrap57 happy_var_2) -> 
	happyIn55
		 ([ Coef happy_var_2 happy_var_1 ]
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_135 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_135 = happySpecReduce_3  50# happyReduction_135
happyReduction_135 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_2 of { (TkIntNum happy_var_2) -> 
	case happyOut57 happy_x_3 of { (HappyWrap57 happy_var_3) -> 
	happyIn55
		 ([ Coef happy_var_3 (-happy_var_2) ]
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_136 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_136 = happySpecReduce_1  50# happyReduction_136
happyReduction_136 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkIntNum happy_var_1) -> 
	happyIn55
		 ([ Const happy_var_1 ]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_137 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_137 = happySpecReduce_2  50# happyReduction_137
happyReduction_137 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_2 of { (TkIntNum happy_var_2) -> 
	happyIn55
		 ([ Const (- happy_var_2)]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_138 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_138 = happySpecReduce_1  50# happyReduction_138
happyReduction_138 happy_x_1
	 =  case happyOut57 happy_x_1 of { (HappyWrap57 happy_var_1) -> 
	happyIn55
		 ([ Coef happy_var_1 1 ]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_139 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_139 = happySpecReduce_2  50# happyReduction_139
happyReduction_139 happy_x_2
	happy_x_1
	 =  case happyOut57 happy_x_2 of { (HappyWrap57 happy_var_2) -> 
	happyIn55
		 ([ Coef happy_var_2 (-1) ]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_140 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_140 = happySpecReduce_3  51# happyReduction_140
happyReduction_140 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut56 happy_x_1 of { happy_var_1 -> 
	case happyOut57 happy_x_3 of { (HappyWrap57 happy_var_3) -> 
	happyIn56
		 (happy_var_3:happy_var_1
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_141 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_141 = happySpecReduce_1  51# happyReduction_141
happyReduction_141 happy_x_1
	 =  case happyOut57 happy_x_1 of { (HappyWrap57 happy_var_1) -> 
	happyIn56
		 ([happy_var_1]
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_142 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_142 = happySpecReduce_1  52# happyReduction_142
happyReduction_142 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	happyIn57
		 ((stringToQsv happy_var_1)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_143 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_143 = happySpecReduce_2  52# happyReduction_143
happyReduction_143 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	happyIn57
		 ((SizeVar happy_var_1,Primed)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_144 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_144 = happySpecReduce_2  52# happyReduction_144
happyReduction_144 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	happyIn57
		 ((SizeVar happy_var_1,Recursive)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_145 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_145 = happySpecReduce_3  52# happyReduction_145
happyReduction_145 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn57
		 (if (happy_var_3=="min") 
        then ((ArrSizeVar happy_var_1 Min),Unprimed)
        else 
          if (happy_var_3=="max") 
            then ((ArrSizeVar happy_var_1 Max),Unprimed) 
            else error $ "neither min or max after QSizeVar"
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_146 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_146 = happyReduce 4# 52# happyReduction_146
happyReduction_146 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn57
		 (if (happy_var_3=="min") 
        then ((ArrSizeVar happy_var_1 Min),Primed)
        else 
          if (happy_var_3=="max") 
            then ((ArrSizeVar happy_var_1 Max),Primed) 
            else error $ "neither min or max after QSizeVar"
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_147 :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_147 = happyReduce 4# 52# happyReduction_147
happyReduction_147 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TkAlphaNum happy_var_1) -> 
	case happyOutTok happy_x_3 of { (TkAlphaNum happy_var_3) -> 
	happyIn57
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
	TkEOF -> happyDoAction 50# tk action sts stk;
	TkAlphaNum happy_dollar_dollar -> cont 1#;
	TkIntNum happy_dollar_dollar -> cont 2#;
	TkFloatNum happy_dollar_dollar -> cont 3#;
	TkString happy_dollar_dollar -> cont 4#;
	TkTrue -> cont 5#;
	TkFalse -> cont 6#;
	TkBogus -> cont 7#;
	TkKwVoid -> cont 8#;
	TkKwInt -> cont 9#;
	TkKwBool -> cont 10#;
	TkKwFloat -> cont 11#;
	TkKwIf -> cont 12#;
	TkKwIfND -> cont 13#;
	TkKwThen -> cont 14#;
	TkKwElse -> cont 15#;
	TkKwWhile -> cont 16#;
	TkKwFor -> cont 17#;
	TkKwDo -> cont 18#;
	TkKwRef -> cont 19#;
	TkPlus -> cont 20#;
	TkMinus -> cont 21#;
	TkMul -> cont 22#;
	TkDiv -> cont 23#;
	TkLBr -> cont 24#;
	TkRBr -> cont 25#;
	TkSemiColon -> cont 26#;
	TkAssign -> cont 27#;
	TkLSqBr -> cont 28#;
	TkRSqBr -> cont 29#;
	TkLAcc -> cont 30#;
	TkRAcc -> cont 31#;
	TkComma -> cont 32#;
	TkEq -> cont 33#;
	TkLT -> cont 34#;
	TkGT -> cont 35#;
	TkGTE -> cont 36#;
	TkLTE -> cont 37#;
	TkAnd -> cont 38#;
	TkOr -> cont 39#;
	TkWhere -> cont 40#;
	TkColon -> cont 41#;
	TkDot -> cont 42#;
	TkExists -> cont 43#;
	TkForall -> cont 44#;
	TkPrime -> cont 45#;
	TkRec -> cont 46#;
	TkError -> cont 47#;
	TkHash -> cont 48#;
	TkKwInclude -> cont 49#;
	_ -> happyError' (tk, [])
	})

happyError_ explist 50# tk = happyError' (tk, explist)
happyError_ explist _ tk = happyError' (tk, explist)

happyThen :: () => P a -> (a -> P b) -> P b
happyThen = (Prelude.>>=)
happyReturn :: () => a -> P a
happyReturn = (Prelude.return)
#if __GLASGOW_HASKELL__ >= 710
happyParse :: () => Happy_GHC_Exts.Int# -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

happyNewToken :: () => Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

happyDoAction :: () => Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

happyReduceArr :: () => Happy_Data_Array.Array Prelude.Int (Happy_GHC_Exts.Int# -> Tk -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))

#endif
happyThen1 :: () => P a -> (a -> P b) -> P b
happyThen1 = happyThen
happyReturn1 :: () => a -> P a
happyReturn1 = happyReturn
happyError' :: () => ((Tk), [Prelude.String]) -> P a
happyError' tk = (\(tokens, explist) -> happyError) tk
parseProg = happySomeParser where
 happySomeParser = happyThen (happyParse 0#) (\x -> happyReturn (let {(HappyWrap5 x') = happyOut5 x} in x'))

parseLPrimDecl = happySomeParser where
 happySomeParser = happyThen (happyParse 1#) (\x -> happyReturn (let {x' = happyOut9 x} in x'))

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
parse :: String -> IO Prog
parse s = runP s parseProg 
--parseFormula s = runP s parseFormula1
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
