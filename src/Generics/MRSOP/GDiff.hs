{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE GADTs                #-}
-- |This module has been taken from arianvp/generics-mrsop-diff, it essentially
-- isolates Arian's fixes over GDiff and adapts them to work over newer versions
-- of generics-mrsop.
--
module Generics.MRSOP.GDiff
  ( Cof(..)
  , cofIdx , cofWitnessI , cofHeq
  , ES(..)
  , apply, apply' , applyES
  , diff , diff'
  , cost
  ) where

import Control.Monad
import Data.Proxy
import Data.Type.Equality  hiding (apply)
import Generics.MRSOP.Base hiding (listPrfNP)
import Generics.MRSOP.GDiff.Util
import Generics.MRSOP.Util ( SNat
                           , EqHO
                           , IsNat
                           , (:++:)
                           , Lkup
                           , ShowHO
                           , Idx
                           , El(..)
                           , getSNat)

-- | A 'Cof' represents a leaf of the flattened representation of our tree. Hence,
-- it will be either a constructor of a particular datatype or an opaque value.
data Cof (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Atom kon -> [Atom kon] -> * where
  -- | A constructor tells us the type of its arguments and which type in the family it constructs
  ConstrI :: (IsNat c, IsNat n) => Constr (Lkup n codes) c -> ListPrf (Lkup c (Lkup n codes)) -> Cof ki codes ('I n) (Lkup c (Lkup n codes))

  -- | Requires no arguments to complete
  ConstrK :: ki k -> Cof ki codes ('K k) '[]

-- |Extracts a proxy from a 'Cof'
cofWitnessI :: Cof ki codes ('I n) t -> Proxy n
cofWitnessI _ = Proxy
 
-- |Extracts an 'SNat' from a 'Cof'
cofIdx :: forall ki codes xs n. IsNat n => Cof ki codes ('I n) xs -> SNat n
cofIdx _ = getSNat @n Proxy

-- |Values of type 'Cof' support heterogeneous equality checking.
cofHeq :: (EqHO ki, TestEquality ki)
       => Cof ki codes a t1
       -> Cof ki codes b t2
       -> Maybe (a :~: b, t1 :~: t2)
cofHeq cx@(ConstrI x _) cy@(ConstrI y _) =
  case testEquality (getSNat (cofWitnessI cx)) (getSNat (cofWitnessI cy)) of
    Nothing -> Nothing
    Just Refl ->
      case testEquality x y of
        Nothing -> Nothing
        Just Refl -> Just (Refl, Refl)
cofHeq (ConstrK x) (ConstrK y) =
  case testEquality x y of
    Just Refl ->
      if x == y
        then Just (Refl, Refl)
        else Nothing
    Nothing -> Nothing
cofHeq _ _ = Nothing

-- |An edit script will insert, delete or copy 'Cof's. We keep the cost
-- of the edit script annotated in the constructor
data ES (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  ES0 :: ES ki codes '[] '[]
  Ins :: Int -> Cof ki codes a t -> ES ki codes i          (t :++: j) -> ES ki codes i        (a ': j)
  Del :: Int -> Cof ki codes a t -> ES ki codes (t :++: i) j          -> ES ki codes (a ': i) j
  Cpy :: Int -> Cof ki codes a t -> ES ki codes (t :++: i) (t :++: j) -> ES ki codes (a ': i) (a ': j)

{-# INLINE cost #-}
-- |Extracts the cost of an edit script
cost :: ES ki codes txs tys -> Int
cost ES0 = 0
cost (Ins k _ _) = k
cost (Del k _ _) = k
cost (Cpy k _ _) = k

{-# INLINE meet #-}
meet :: ES ki codes txs tys -> ES ki codes txs tys -> ES ki codes txs tys
meet d1 d2 = if cost d1 <= cost d2 then d1 else d2

-- Heuristic:
--
--    many diffs have largely unchanged heads. Simply skip those
--
--    TODO: We can do the same with the tail in an imperative language
--    however, we cant due to the way our diff structure is a stack,
--
--    TODO: We can even emit CpyTree's here, using hashing, but we'll
--    also have to update the conversion to stdiff


skipFront 
  :: (TestEquality ki, EqHO ki)
  => PoA ki (Fix ki codes) xs
  -> PoA ki (Fix ki codes) ys
  -> ES ki codes xs ys
skipFront (x@(sopNA -> TagNA cx px) :* xs) (y@(sopNA -> TagNA cy py) :* ys) =
  case cofHeq cx cy of
    Just (Refl, Refl) ->
      let c = skipFront (appendNP px xs) (appendNP py ys)
       in Cpy (cost c) cx $ c
    Nothing -> getDiff $ diffT (x :* xs) (y :* ys)
skipFront xs ys = getDiff $ diffT xs ys

-- |This is an edit script table; which is how we memoize computations
-- to reuse them later. For more details check the last section in
-- /A Type-safe diff for families of datatypes/, by /Lempsink and Loh/.
data EST (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  NN :: ES ki codes '[] '[] 
     -> EST ki codes '[] '[]
  NC :: Cof ki codes y t
     -> ES ki codes '[] (y ': tys)
     -> EST ki codes '[] (t :++: tys)
     -> EST ki codes '[] (y ': tys)
  CN :: Cof ki codes x t
     -> ES ki codes (x ': txs) '[]
     -> EST ki codes (t :++: txs) '[]
     -> EST ki codes (x ': txs) '[]
  CC :: Cof ki codes x t1
     -> Cof ki codes y t2
     -> ES ki codes (x ': txs) (y ': tys)
     -> EST ki codes (x ': txs) (t2 :++: tys)
     -> EST ki codes (t1 :++: txs) (y ': tys)
     -> EST ki codes (t1:++: txs) (t2 :++: tys)
     -> EST ki codes (x ': txs) (y ': tys)


getDiff :: EST ki codes rxs rys -> ES ki codes rxs rys
getDiff (NN x) = x
getDiff (NC _ x _) = x
getDiff (CN _ x _) = x
getDiff (CC _ _ x _ _ _) = x

-- existential version of Cof, that hides its type
data ViewNA ki codes a where
  TagNA :: Cof ki codes a t -> PoA ki (Fix ki codes) t -> ViewNA ki codes a

-- | Non-CC version of matchConstructor
--
-- A version of sop but over NA instead of Rep
sopNA :: NA ki (Fix ki codes) a -> ViewNA ki codes a
sopNA (NA_K k) = TagNA (ConstrK k) Nil
sopNA (NA_I (Fix (sop -> Tag c poa))) = TagNA (ConstrI c (listPrfNP poa)) poa

data DES ki codes a xs ys where 
  DES :: Cof ki codes a t -> ES ki codes (a ': xs) ys -> EST ki codes (t :++: xs) ys -> DES ki codes a xs ys

data IES ki codes a xs ys where 
  IES :: Cof ki codes a t -> ES ki codes xs (a ': ys)-> EST ki codes xs (t :++: ys) -> IES ki codes a xs ys

extractd :: EST ki codes (a ': xs) ys -> DES ki codes a xs ys
extractd (CC f _ e _ i _) = DES f e i
extractd (CN g d i) = DES g d i

extracti :: EST ki codes xs (a ': ys) -> IES ki codes a xs ys
extracti (CC _ g e i _ _) = IES g e i
extracti (NC  g d i) = IES g d i

diffT :: (EqHO ki, TestEquality ki)
      => PoA ki (Fix ki codes) xs
      -> PoA ki (Fix ki codes) ys
      -> EST ki codes xs ys
diffT Nil Nil = NN ES0
diffT ((sopNA -> TagNA c poa) :* xs) Nil =
  let d = diffT (appendNP poa xs) Nil
  in CN c (Del (1 + cost (getDiff d)) c (getDiff d)) d
diffT Nil ((sopNA -> TagNA c poa) :* ys) =
  let i = diffT Nil (appendNP poa ys)
  in NC c (Ins (1 + cost (getDiff i)) c (getDiff i)) i
diffT ((sopNA -> TagNA c1 poa1) :* xs) ((sopNA -> TagNA c2 poa2) :* ys) =
  let 
    i = extendi c1 c
    d = extendd c2 c
    c = diffT (appendNP poa1 xs) (appendNP poa2 ys)
    es = bestDiffT c1 c2 i d c
  in CC c1 c2 es i d c

extendi 
  :: (EqHO ki, TestEquality ki)
  => Cof ki codes x t
  -> EST ki codes (t :++: xs) ys
  -> EST ki codes (x ': xs) ys
extendi c1 i@(NN d) = CN c1 (Del (1 + cost d) c1 d) i
extendi c1 i@(CN _ d _) =  CN c1 (Del (1 + cost d) c1 d) i
extendi c1 d@NC{} =
  case extracti d of
    IES c2 _ c -> 
      let i = extendi c1 c
      in CC c1 c2 (bestDiffT c1 c2 i d c) i d c
extendi c1 d@CC{} =
  case extracti d of
    IES c2 _ c -> 
      let i = extendi c1 c
      in CC c1 c2 (bestDiffT c1 c2 i d c) i d c
  
extendd
  :: (TestEquality ki, EqHO ki) 
  => Cof ki codes y t
  -> EST ki codes xs (t :++: ys)
  -> EST ki codes xs (y ': ys)
extendd c1 i@(NN d) = NC c1 (Ins (1 + cost d) c1 d) i
extendd c1 i@(NC _ d _) = NC c1 (Ins (1 + cost d) c1 d) i
extendd c1 i@CN{} =
  case extractd i of
    DES c2 _ c -> 
      let d = extendd c1 c 
      in CC c2 c1 (bestDiffT c2 c1 i d c) i d c
extendd c1 i@CC{} =
  case extractd i of
    DES c2 _ c -> 
      let d = extendd c1 c
      in CC c2 c1 (bestDiffT c2 c1 i d c) i d c

bestDiffT
  :: (EqHO ki, TestEquality ki)
  => Cof ki codes x t1
  -> Cof ki codes y t2
  -> EST ki codes (x ': xs) (t2 :++: ys)
  -> EST ki codes (t1 :++: xs) (y ': ys)
  -> EST ki codes (t1 :++: xs) (t2 :++: ys)
  -> ES ki codes (x ': xs) (y ': ys)
bestDiffT cx cy i d c =
  case cofHeq cx cy of
    Just (Refl, Refl) ->
      let c' = getDiff c
      in Cpy (cost c') cx c'
    Nothing -> 
      let
        i' = getDiff i
        d' = getDiff d
      in
        meet (Ins (1 + cost i') cy i') (Del (1 + cost d') cx d')
          
matchCof :: (EqHO ki)
         => Cof ki codes a t  -- NOTE: cof is a relation. not a function,
         -> NA ki (Fix ki codes) a
         -> Maybe (PoA ki (Fix ki codes) t)
matchCof (ConstrI c1 _) (NA_I (Fix x)) = match c1 x
matchCof (ConstrK k) (NA_K k2) = guard (k == k2) >> Just Nil

-- we need to give Haskell a bit of a hint that Tyof codes c reduces to an IsList
-- insCof is also really the only place where we _need_ IsList I think
insCof :: Cof ki codes a t
       -> PoA ki (Fix ki codes) (t :++: xs)
       -> PoA ki (Fix ki codes) (a ': xs)
insCof (ConstrI c ispoa) xs =
  let (poa, xs') = split ispoa xs
   in NA_I (Fix $ inj c poa) :* xs'
insCof (ConstrK k) xs = NA_K k :* xs 

delCof :: EqHO ki
       => Cof ki codes a t
       -> PoA ki (Fix ki codes) (a ': xs)
       -> Maybe (PoA ki (Fix ki codes) (t :++: xs))
delCof c (x :* xs) = flip appendNP xs <$> matchCof c x

-- * Application Function Variations

-- $applydocs
--
-- Different interfaces to the application function are made
-- available. This enables one to always have an /apply/ function
-- handy on any stage of a generic pipeline.

apply :: forall ki fam codes ty1 ty2 ix1 ix2.
         ( Family ki fam codes
         , ix1 ~ Idx ty1 fam
         , ix2 ~ Idx ty2 fam
         , Lkup ix1 fam ~ ty1
         , Lkup ix2 fam ~ ty2
         , IsNat ix1
         , IsNat ix2
         ,  EqHO ki
         , TestEquality ki
         )
      => ES ki codes '[ 'I ix1] '[ 'I ix2] -- ^ 
      -> ty1
      -> Maybe ty2
apply es a =
  case apply' es (deep a) of
    Just (Fix x) ->
      case dto @ix2 x of
        El b -> Just b
    Nothing -> Nothing

apply' ::
     (IsNat ix1, IsNat ix2,  EqHO ki)
  => ES ki codes '[ 'I ix1] '[ 'I ix2] -- ^ 
  -> Fix ki codes ix1
  -> Maybe (Fix ki codes ix2)
apply' es x = do
  res <- applyES es (NA_I x :* Nil)
  case res of
    (NA_I y :* Nil) -> pure y

applyES ::
     EqHO ki
  => ES ki codes xs ys -- ^ 
  -> PoA ki (Fix ki codes) xs
  -> Maybe (PoA ki (Fix ki codes) ys)
applyES ES0 _ = Just Nil
applyES (Ins _ c es) xs = insCof c <$> applyES es xs
applyES (Del _ c es) xs = delCof c xs >>= applyES es
applyES (Cpy _ c es) xs = insCof c <$> (delCof c xs >>= applyES es)


-- When Showing, we do not know what the family that we're showing is,
-- as edit scripts are not parameterised over the family.
-- hence, we can not get the datatype info
showCof :: forall ki fam codes a c.
     (HasDatatypeInfo ki fam codes, ShowHO ki) => Cof ki codes a c -> String
showCof (ConstrK k) = show k
showCof x@(ConstrI c _) = constructorName . constrInfoLkup c $ datatypeInfo (Proxy @fam) (cofIdx x)

instance (HasDatatypeInfo ki fam codes, ShowHO ki) =>
         Show (ES ki codes xs ys) where
  show ES0 = "ES0"
  show (Ins _ c d) = "Ins " ++ showCof c ++ " $ " ++ show d
  show (Del _ c d) = "Del " ++ showCof c ++ " $ " ++ show d
  show (Cpy _ c d) = "Cpy " ++ showCof c ++ " $ " ++ show d

-- * Diff Function Variations

-- $diffdocs
--
-- Different interfaces to the /diff/ function.


diff :: forall fam ki codes ix1 ix2 ty1 ty2.
        ( Family ki fam codes
        , ix1 ~ Idx ty1 fam
        , ix2 ~ Idx ty2 fam
        , Lkup ix1 fam ~ ty1
        , Lkup ix2 fam ~ ty2
        , IsNat ix1
        , IsNat ix2
        ,  EqHO ki
        , TestEquality ki
        )
     => ty1 -- ^ 
     -> ty2
     -> ES ki codes '[ 'I ix1] '[ 'I ix2]
diff a b = diff' (deep a) (deep b)

diff' :: ( EqHO ki, IsNat ix1, IsNat ix2, TestEquality ki)
      => Fix ki codes ix1 -- ^ 
      -> Fix ki codes ix2
      -> ES ki codes '[ 'I ix1] '[ 'I ix2]
diff' a b = skipFront (NA_I a :* Nil) (NA_I b :* Nil) 
