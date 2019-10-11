{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE GADTs                 #-}
module Generics.MRSOP.STDiff.Enum where

import Control.Monad
import Control.Applicative
import Data.Proxy
import Data.Type.Equality

import Generics.MRSOP.Base
import Generics.MRSOP.STDiff.Types

-- VCM: pottentially duplicate function
getFixSNat :: IsNat ix => Fix ki codes ix -> SNat ix
getFixSNat _ = getSNat (Proxy :: Proxy ix)





enumAt :: (MonadPlus m , TestEquality ki , EqHO ki)
       => NA ki (Fix ki codes) at
       -> NA ki (Fix ki codes) at
       -> m (At ki codes at)
enumAt (NA_I x) (NA_I y) = AtFix <$> enumAlmu x y
enumAt (NA_K x) (NA_K y) = return $ AtSet (Trivial x y)

enumAl :: (MonadPlus m , TestEquality ki , EqHO ki)
       => PoA ki (Fix ki codes) p1
       -> PoA ki (Fix ki codes) p2
       -> m (Al ki codes p1 p2)
enumAl Nil Nil = return A0
enumAl (x :* xs) Nil = ADel x <$> enumAl xs Nil
enumAl Nil (y :* ys) = AIns y <$> enumAl Nil ys
enumAl (x :* xs) (y :* ys)
  =     (ADel x <$> enumAl xs (y :* ys))
    <|> (AIns y <$> enumAl (x :* xs) ys)
    <|> case testEquality x y of
          Just Refl -> AX <$> (enumAt x y) <*> enumAl xs ys
          Nothing   -> mzero

enumSpn :: (MonadPlus m , TestEquality ki , EqHO ki)
        => SNat ix -> SNat iy
        -> Rep ki (Fix ki codes) (Lkup ix codes)
        -> Rep ki (Fix ki codes) (Lkup iy codes)
        -> m (Spine ki codes (Lkup ix codes) (Lkup iy codes))
enumSpn six siy (sop -> Tag cx px) (sop -> Tag cy py)
  = case testEquality six siy of
      Nothing -> SChg cx cy <$> enumAl px py
      Just Refl -> 
        case testEquality cx cy of
           Nothing   -> SChg cx cy <$> enumAl px py
           Just Refl -> if eqHO px py
                        then return Scp
                        else SCns cx <$> mapNPM (uncurry' enumAt) (zipNP px py)

enumDelCtx :: forall m ki codes iy prod
            . (MonadPlus m , TestEquality ki , EqHO ki , IsNat iy)
           => PoA ki (Fix ki codes) prod
           -> Fix ki codes iy
           -> m (DelCtx ki codes iy prod)
enumDelCtx Nil            _ = mzero
enumDelCtx (NA_K x :* xs) f = T (NA_K x) <$> enumDelCtx xs f
enumDelCtx (NA_I x :* xs) f
  = (flip H xs . AlmuMin) <$> enumAlmu x f
    <|> T (NA_I x) <$> enumDelCtx xs f

enumInsCtx :: forall m ki codes iy prod
            . (MonadPlus m , TestEquality ki , EqHO ki , IsNat iy)
           => Fix ki codes iy
           -> PoA ki (Fix ki codes) prod
           -> m (InsCtx ki codes iy prod)
enumInsCtx _ Nil            = mzero
enumInsCtx f (NA_K x :* xs) = T (NA_K x) <$> enumInsCtx f xs
enumInsCtx f (NA_I x :* xs) 
  = (flip H xs) <$> enumAlmu f x
    <|> T (NA_I x) <$> enumInsCtx f xs 
    
enumAlmu :: forall m ki codes ix iy
          . (MonadPlus m , TestEquality ki , EqHO ki , IsNat ix , IsNat iy)
         => Fix ki codes ix
         -> Fix ki codes iy
         -> m (Almu ki codes ix iy)
enumAlmu x y
  =    enumDel (sop $ unFix x) y
   <|> enumIns x (sop $ unFix y)
   <|> Spn <$> enumSpn (snatFixIdx x) (snatFixIdx y) (unFix x) (unFix y)
  where
    enumDel :: View ki (Fix ki codes) (Lkup ix codes)
            -> Fix ki codes iy
            -> m (Almu ki codes ix iy)
    enumDel (Tag c p) y0 = Del c <$> enumDelCtx p y0

    enumIns :: Fix ki codes ix
            -> View ki (Fix ki codes) (Lkup iy codes)
            -> m (Almu ki codes ix iy)
    enumIns x0 (Tag c p) = Ins c <$> enumInsCtx x0 p
