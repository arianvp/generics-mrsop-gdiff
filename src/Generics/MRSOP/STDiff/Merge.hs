{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PolyKinds             #-}
module Generics.MRSOP.STDiff.Merge (merge) where

import Data.Proxy
import Data.Type.Equality
import Control.Monad (guard)

import Generics.MRSOP.Base

import Generics.MRSOP.STDiff.Types

mergeAt :: EqHO ki
        => At ki codes a
        -> At ki codes a
        -> Maybe (At ki codes a)
mergeAt  (AtSet (Trivial k1 k2)) (AtSet (Trivial k3 k4)) = 
   if eqHO k1 k2
   then pure $ AtSet $ Trivial k3 k4
   else if eqHO k3 k4
   then pure $ AtSet $ Trivial k3 k4
   else Nothing
mergeAt (AtFix x) (AtFix y) = AtFix <$> mergeAlmu x y

mergeAtAl :: EqHO ki
          => NP (At ki codes) xs
          -> Al ki codes xs ys
          -> Maybe (Al ki codes xs ys)
mergeAtAl Nil A0 = pure A0
mergeAtAl xs (AIns at al) = AIns at <$> mergeAtAl xs al
mergeAtAl (x :* xs) (ADel at al)
  | identityAt x = ADel at <$> mergeAtAl xs al
  | otherwise    = Nothing
mergeAtAl (x :* xs) (AX at al) = AX <$> (mergeAt x at)  <*> mergeAtAl xs al

identityAt :: (EqHO ki) => At ki codes a -> Bool
identityAt (AtFix (Spn Scp)) = True
identityAt (AtSet (Trivial k1 k2)) = eqHO k1 k2
identityAt _ = False

makeIdAt :: NA ki (Fix ki codes) a -> At ki codes a
makeIdAt (NA_I _) = AtFix (Spn Scp)
makeIdAt (NA_K k) = AtSet (Trivial k k)

mergeAlAt :: EqHO ki
          => Al ki codes xs ys
          -> NP (At ki codes) xs
          -> Maybe (NP (At ki codes) ys)
mergeAlAt A0 Nil = pure Nil
mergeAlAt (AIns at al) xs = (makeIdAt at :*) <$> mergeAlAt al xs
mergeAlAt (ADel _  al) (x :* xs)
  | identityAt x = mergeAlAt al xs
  | otherwise    = Nothing
mergeAlAt (AX a al)   (x :* xs) = (:*) <$> mergeAt a x <*> mergeAlAt al xs


mergeAts :: EqHO ki
         => NP (At ki codes) xs
         -> NP (At ki codes) xs
         -> Maybe (NP (At ki codes) xs)
mergeAts Nil Nil = pure Nil
mergeAts (x :* xs) (y :* ys) = (:*) <$> mergeAt x y <*> mergeAts xs ys

mergeSpine :: EqHO ki
           => SNat ix
           -> SNat iy
           -> Spine ki codes (Lkup ix codes) (Lkup iy codes)
           -> Spine ki codes (Lkup ix codes) (Lkup iy codes)
           -> Maybe (Spine ki codes (Lkup ix codes) (Lkup iy codes))
mergeSpine _ _ Scp s = pure s
mergeSpine _ _ _ Scp = pure Scp
mergeSpine _ _ (SCns cx xs) (SCns cy ys) = do
  Refl <- testEquality cx cy
  SCns cx <$> mergeAts xs ys
mergeSpine _ _ (SCns cx xs) (SChg cy cz al) = do
  Refl <- testEquality cx cy
  SChg cy cz <$> mergeAtAl xs al
mergeSpine ix iy (SChg cx cy al) (SCns cz zs) = do
  Refl <- testEquality ix iy
  Refl <- testEquality cx cz
  SCns cy <$> mergeAlAt al zs
mergeSpine _ _ SChg{} SChg{} = Nothing

mergeCtxAt :: forall ki codes ix iy xs
            . (EqHO ki, IsNat ix, IsNat iy) 
           => DelCtx ki codes iy xs
           -> NP (At ki codes) xs
           -> Maybe (Almu ki codes ix iy)
mergeCtxAt (H (AlmuMin almu') _) (AtFix almu :* xs) = do
  Refl <- testEquality (almuDest almu) (almuDest almu')
  x <- mergeAlmu almu' almu
  Refl <- testEquality (almuSrc x) (getSNat (Proxy @ix))
  guard (and $ elimNP identityAt xs)
  pure x
mergeCtxAt (T _ ctx) (x :* xs) = do
  guard (identityAt x)
  mergeCtxAt ctx xs

mergeAtCtx :: (EqHO ki, IsNat iy)
           => NP (At ki codes) xs
           -> DelCtx ki codes iy xs
           -> Maybe (DelCtx ki codes iy xs)
mergeAtCtx (AtFix almu :* xs) (H (AlmuMin almu') rest) = do
  Refl <- testEquality (almuDest almu) (almuDest almu')
  almu'' <- mergeAlmu almu almu'
  guard (and $ elimNP identityAt xs)
  pure $ H  (AlmuMin almu'') rest
mergeAtCtx (x :* xs) (T a  ctx) = do
   guard (identityAt x)
   T a  <$> mergeAtCtx xs ctx
mergeAtCtx Nil _ = error "unreachable" -- check x's type to be sure!

almuDest :: forall ix iy ki codes. IsNat iy => Almu ki codes ix iy -> SNat iy
almuDest _ = getSNat (Proxy @iy)

almuSrc :: forall ix iy ki codes. IsNat ix => Almu ki codes ix iy -> SNat ix
almuSrc _ = getSNat (Proxy @ix)

mergeCtxAlmu :: (EqHO ki, IsNat ix )
             => InsCtx ki codes ix xs
             -> Almu ki codes ix ix
             -> Maybe (NP (At ki codes) xs)
mergeCtxAlmu (H almu' rest) almu = do 
  Refl <- testEquality (almuDest almu) (almuDest almu')
  x <- AtFix <$> mergeAlmu almu' almu
  pure $ x :* mapNP makeIdAt rest
mergeCtxAlmu (T a    ctx) almu = 
  (makeIdAt a :*) <$> mergeCtxAlmu ctx almu

mergeAlmuCtx :: (EqHO ki, IsNat ix)
             => Almu ki codes ix ix
             -> InsCtx ki codes ix xs
             -> Maybe (InsCtx ki codes ix xs)
mergeAlmuCtx almu (H almu' rest) = do
  Refl <- testEquality (almuDest almu) (almuDest almu')
  almu'' <- mergeAlmu almu almu'
  pure (H almu'' rest)
mergeAlmuCtx almu (T a ctx) = T a <$> mergeAlmuCtx almu ctx

mergeAlmu :: forall ki codes ix iy
           . (EqHO ki, IsNat ix, IsNat iy)
          => Almu ki codes ix iy
          -> Almu ki codes ix iy
          -> Maybe (Almu ki codes ix iy)
mergeAlmu (Ins _ _) (Ins _ _) = Nothing
mergeAlmu (Ins c1 s1) (Spn s2) =  do
  Refl <- testEquality (getSNat (Proxy @ix)) (getSNat (Proxy @iy))
  Spn . SCns c1 <$> mergeCtxAlmu s1 (Spn s2)
mergeAlmu (Ins c1 s1) (Del c2 s2) = do
  Refl <- testEquality (getSNat (Proxy @ix)) (getSNat (Proxy @iy))
  Spn . SCns c1 <$> mergeCtxAlmu s1 (Del c2 s2)
mergeAlmu (Spn s1) (Ins c2 s2) = do
  Refl <- testEquality (getSNat (Proxy @ix)) (getSNat (Proxy @iy))
  Ins c2 <$> (mergeAlmuCtx (Spn s1) s2)
mergeAlmu (Del c1 s1) (Ins c2 s2) = do
  Refl <- testEquality (getSNat (Proxy @ix)) (getSNat (Proxy @iy))
  Ins c2 <$> (mergeAlmuCtx (Del c1 s1) s2)

mergeAlmu (Spn s1) (Spn s2) = Spn <$> mergeSpine (getSNat (Proxy @ix)) (getSNat (Proxy @iy)) s1 s2
mergeAlmu (Spn Scp) (Del c2 s2) = pure $ Del c2 s2
mergeAlmu (Spn (SCns c1 at1)) (Del c2 s2) = do
  
  Refl <- testEquality c1 c2
  Del c1 <$> mergeAtCtx at1 s2
mergeAlmu (Spn (SChg _ _ _)) (Del _ _) = Nothing
mergeAlmu (Del _ _) (Spn Scp) = pure $ Spn Scp
mergeAlmu (Del c1 s1) (Spn (SCns c2 at2)) = do
  Refl <- testEquality c1 c2
  mergeCtxAt s1 at2
mergeAlmu (Del _ _) (Spn (SChg _ _ _)) = Nothing
mergeAlmu (Del _ _) (Del _ _) = Nothing

-- |Merges two patches in the /stdiff/ style. Satisfies the following
-- postcondition:
--
-- > if merge p q == Just pq && merge q p == Just qp
-- > then apply pq . q == apply qp . p
--
merge :: forall ki codes ix
       . (EqHO ki, IsNat ix)
      => Almu ki codes ix ix
      -> Almu ki codes ix ix
      -> Maybe (Almu ki codes ix ix)
merge = mergeAlmu
