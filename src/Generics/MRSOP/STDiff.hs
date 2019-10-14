{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Generics.MRSOP.STDiff
  ( module Generics.MRSOP.STDiff.Types
  , apply , merge , diff
  ) where

import Data.Proxy
import Data.Type.Equality hiding (apply)
import Control.Monad
import Generics.MRSOP.Base

import Generics.MRSOP.STDiff.Types
import Generics.MRSOP.STDiff.Merge
import Generics.MRSOP.STDiff.Compute


applyAt :: EqHO ki
        => (At ki codes :*: NA ki (Fix ki codes)) a
        -> Either String (NA ki (Fix ki codes) a)
applyAt (AtSet (Trivial a' b) :*: NA_K a)  
  | eqHO a' b  = pure (NA_K a)
  | eqHO a' a  = pure (NA_K b)
  | otherwise = Left "atom"
applyAt (AtFix x :*: NA_I x') = NA_I <$> applyAlmu x x'

applyAl
  :: EqHO ki
  => Al ki codes xs ys
  -> PoA ki (Fix ki codes) xs
  -> Either String (PoA ki (Fix ki codes) ys)
applyAl A0 Nil = return Nil
applyAl (AX dx dxs) (x :* xs) =
  (:*) <$> applyAt (dx :*: x) <*> applyAl dxs xs
applyAl (AIns x dxs) xs =
  (x :*) <$> applyAl dxs xs 
applyAl (ADel x dxs) (x' :* xs) =
  if eqHO x x' then applyAl dxs xs else Left "al del"
  -- applyAl dxs xs

testEquality' :: (TestEquality f)
              => f a -> f b -> Either String (a :~: b)
testEquality' x y = case testEquality x y of
  Just r -> Right r
  Nothing -> Left "err"

applySpine 
  :: EqHO ki
  => SNat ix
  -> SNat iy
  -> Spine ki codes (Lkup ix codes) (Lkup iy codes)
  -> Rep ki (Fix ki codes) (Lkup ix codes)
  -> Either String (Rep ki (Fix ki codes) (Lkup iy codes))
applySpine _ _ Scp x = return x
applySpine ix iy (SCns c1 dxs) (sop -> Tag c2 xs) =  do
  Refl <- testEquality' ix iy
  Refl <- testEquality' c1 c2
  inj c2 <$> (mapNPM applyAt (zipNP dxs xs))
applySpine _ _ (SChg c1 c2 al) (sop -> Tag c3 xs) = do
  Refl <- testEquality' c1 c3
  inj c2 <$> applyAl al xs

insCtx
  :: (IsNat ix, EqHO ki)
  => InsCtx ki codes ix xs
  -> Fix ki codes ix
  -> Either String (PoA ki (Fix ki codes) xs)
insCtx (H x x2) x1 = (\xi -> NA_I xi :* x2) <$> applyAlmu x x1
insCtx (T x x2) x1 = (x :*) <$> insCtx x2 x1

delCtx
  :: (EqHO ki, IsNat ix)
  => DelCtx ki codes ix xs
  -> PoA ki (Fix ki codes) xs
  -> Either String (Fix ki codes ix)
delCtx (H spu _) (NA_I x :* _) = applyAlmu (unAlmuMin spu) x
delCtx (T _ al)  (_ :* p)      = delCtx al p

applyAlmu 
  :: forall ki codes ix iy. (IsNat ix, IsNat iy, EqHO ki)
  => Almu ki codes ix iy
  -> Fix ki codes ix
  -> Either String (Fix ki codes iy)
applyAlmu (Spn spine) (Fix rep) = Fix <$> applySpine (getSNat (Proxy @ix)) (getSNat (Proxy @iy)) spine rep
applyAlmu (Ins c ctx) f@(Fix _) = Fix . inj c <$> insCtx ctx f
applyAlmu (Del c ctx) (Fix rep) = delCtx ctx <=< m2e . match c $ rep
  where
    m2e Nothing  = Left (show "del")
    m2e (Just r) = Right r

-- |Applies a patch to an element
apply :: forall ki codes ix iy
       . (IsNat ix, IsNat iy, EqHO ki)
      => Almu ki codes ix iy
      -> Fix ki codes ix
      -> Maybe (Fix ki codes iy)
apply almu x = case applyAlmu almu x of
                 Left  _ -> Nothing
                 Right y -> Just y
