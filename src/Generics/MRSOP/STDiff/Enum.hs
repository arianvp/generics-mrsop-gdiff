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

enumAt :: MonadPlus m
       => NA ki (Fix ki codes) at
       -> NA ki (Fix ki codes) at
       -> m (At ki codes at)
enumAt (NA_I x) (NA_I y) = AtFix <$> enumAlmu x y
enumAt (NA_K x) (NA_K y) = return $ AtSet (Trivial x y)

enumDelCtx :: forall m ki codes iy prod
            . (MonadPlus m , IsNat iy)
           => PoA ki (Fix ki codes) prod
           -> Fix ki codes iy
           -> m (DelCtx ki codes iy prod)
enumDelCtx Nil            _ = mzero
enumDelCtx (NA_K x :* xs) f = T (NA_K x) <$> enumDelCtx xs f
enumDelCtx (NA_I x :* xs) f
  = (flip H xs . AlmuMin) <$> enumAlmu x f
    <|> T (NA_I x) <$> enumDelCtx xs f

enumInsCtx :: forall m ki codes iy prod
            . (MonadPlus m , IsNat iy)
           => Fix ki codes iy
           -> PoA ki (Fix ki codes) prod
           -> m (InsCtx ki codes iy prod)
enumInsCtx f Nil            = mzero
enumInsCtx f (NA_K x :* xs) = T (NA_K x) <$> enumInsCtx f xs
enumInsCtx f (NA_I x :* xs) 
  = (flip H xs) <$> enumAlmu f x
    <|> T (NA_I x) <$> enumInsCtx f xs 
    
enumAlmu :: forall m ki codes ix iy
          . (MonadPlus m , IsNat ix , IsNat iy)
         => Fix ki codes ix
         -> Fix ki codes iy
         -> m (Almu ki codes ix iy)
enumAlmu x y =
  let d = enumDel (sop $ unFix x) y
      i = enumIns x (sop $ unFix y)
   in case testEquality (getFixSNat x) (getFixSNat y) of
        Nothing   -> d <|> i
        Just Refl -> (Spn <$> _) <|> d <|> i
  where
    enumDel :: View ki (Fix ki codes) (Lkup ix codes)
            -> Fix ki codes iy
            -> m (Almu ki codes ix iy)
    enumDel (Tag c p) y = Del c <$> enumDelCtx p y

    enumIns :: Fix ki codes ix
            -> View ki (Fix ki codes) (Lkup iy codes)
            -> m (Almu ki codes ix iy)
    enumIns x (Tag c p) = Ins c <$> enumInsCtx x p
