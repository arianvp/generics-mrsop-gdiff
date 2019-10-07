{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE GADTs                 #-}
module Generics.MRSOP.STDiff.Compute where

import Data.Function (on)
import Data.Ord      (comparing)
import Data.List     (maximumBy)
import Data.Coerce
import Data.Proxy
import Data.Type.Equality
import Data.Functor.Const

import Generics.MRSOP.Base
import Generics.MRSOP.AG

import qualified Generics.MRSOP.GDiff as GDiff
import           Generics.MRSOP.GDiff.Util
import           Generics.MRSOP.STDiff.Types

import Data.Maybe (fromJust)

-- * Annotating Trees
--
-- $annotating
--
-- First we use /gdiff/ to annotate the source and destination
-- forests before translating them to a 'Generics.MRSOP.STDiff.Almu'
-- The idea being that the information comming from /gdiff/ is sufficient
-- to know which constructors are copies and which have been modified.

-- |Annotations to be placed throughout the tree.
data Ann = Modify | Copy deriving Show

-- |Adds an annotated constructor to a product of atoms.
injCofAnn :: GDiff.Cof ki codes a t
          -> Const ann ix
          -> PoA ki (AnnFix ki codes (Const ann)) t
          -> NA ki (AnnFix ki codes (Const ann)) a
injCofAnn (GDiff.ConstrI c _) ann xs = NA_I (AnnFix (coerce ann) $ inj c xs)
injCofAnn (GDiff.ConstrK k)   _   _  = NA_K k

-- |Inserts an annotated constructor at the head of a
-- product of atoms.
insCofAnn :: GDiff.Cof ki codes a t
          -> Const ann ix
          -> PoA ki (AnnFix ki codes (Const ann)) (t :++: as)
          -> PoA ki (AnnFix ki codes (Const ann)) (a ': as)
insCofAnn (GDiff.ConstrK k)     _   xs = NA_K k :* xs
insCofAnn (GDiff.ConstrI c prf) ann xs =
  let (xs0, xs1) = split prf xs
   in  injCofAnn (GDiff.ConstrI c prf) ann xs0 :* xs1

{-
 - In Agda, it would be the following. However, I'm not sure
 - it is possible to carry around the IsJust constraint in Haskell
 - hence, we will be partial instead
 -  ann-source : ∀{txs tys}(xs : ⟦ txs ⟧A*)(p : ES txs tys)
 -           → (hip : IsJust (applyES p xs))
 -           → ⟦ txs ⟧Aₐ*
 -
 - However, it's morally total if you know beforehand that the
 - patch is gonna apply. Which we know by construction everywhere we use this
 - , so we can just `fromJust` it where appropriate
 -
 - WARNING: Morally dubious, but we know that this edit script was
 - generated hte same time as the datatype, so it should never
 - fail to apply
 -
 - TODO: Actually make it return Maybe and be honest
 -}

-- |Annotates the source of an edit script.
annSrc :: (EqHO ki , IsNat ix)
       => Fix ki codes ix -- ^ 
       -> GDiff.ES ki codes '[ 'I ix] ys
       -> AnnFix ki codes (Const Ann) ix
annSrc x0 es0 = case annSrc' (NA_I x0 :* Nil) es0 of
                  (NA_I y :* Nil) -> y
  where
    annSrc' :: EqHO ki
        => PoA ki (Fix ki codes) xs
        -> GDiff.ES ki codes xs ys
        -> PoA ki (AnnFix ki codes (Const Ann)) xs
    annSrc' _  GDiff.ES0 = Nil
    annSrc' Nil _  = Nil
    annSrc' xs (GDiff.Ins _ _ es) = annSrc' xs es
    annSrc' (x :* xs) (GDiff.Del _ c es) =
      let poa = fromJust $ GDiff.matchCof c x
       in insCofAnn c (Const Modify) (annSrc' (appendNP poa xs) es)
    annSrc' (x :* xs) (GDiff.Cpy _ c es) =
      let poa = fromJust $ GDiff.matchCof c x
       in insCofAnn c (Const Copy) (annSrc' (appendNP poa xs) es)

-- |Annotates the destination of an edit script.
annDest :: (EqHO ki , IsNat ix)
        => Fix ki codes ix -- ^ 
        -> GDiff.ES ki codes xs '[ 'I ix]
        -> AnnFix ki codes (Const Ann) ix
annDest x0 es0 = case annDest' (NA_I x0 :* Nil) es0 of
                   (NA_I y :* Nil) -> y
  where
    annDest' :: EqHO ki
             => PoA ki (Fix ki codes) ys
             -> GDiff.ES ki codes xs ys
             -> PoA ki (AnnFix ki codes (Const Ann)) ys
    annDest' _  GDiff.ES0 = Nil
    annDest' Nil _  = Nil
    annDest' (x :* xs) (GDiff.Del _ _ es) = annDest' (x :* xs) es
    annDest' (x :* xs) (GDiff.Ins _ c es)
     = let poa = fromJust $ GDiff.matchCof c x
       in insCofAnn c (Const Modify) (annDest' (appendNP poa xs) es)
    annDest' (x :* xs) (GDiff.Cpy _ c es) =
      let poa = fromJust $ GDiff.matchCof c x
       in insCofAnn c (Const Copy) (annDest' (appendNP poa xs) es)

-- * Differencing Annotated Trees
--
-- $diffann
--
-- Once we have annotated the trees on the source and destination of the
-- edit script, we can easily diff them in the /stdiff/ style.
--

-- ** Stiff Patches
--
-- $stiffpatches
--
-- We call a patch /stiff/ if it has no copies. It is trivial
-- to produce sauch a patch given two elements. We simply delete
-- the entire source and insert the entire destination.

stiffAlmu :: (TestEquality ki, EqHO ki)
          => Fix ki codes ix -- ^
          -> Fix ki codes iy
          -> Almu ki codes ix iy
stiffAlmu (Fix rep1) (Fix rep2) = Spn (stiffSpine rep1 rep2)

stiffSpine :: (TestEquality ki, EqHO ki)
           => Rep ki (Fix ki codes) xs -- ^ 
           -> Rep ki (Fix ki codes) ys
           -> Spine ki codes xs ys
stiffSpine (sop -> Tag c1 p1) (sop -> Tag c2 p2) = SChg c1 c2 (stiffAl p1 p2)

stiffAt :: (TestEquality ki, EqHO ki)
        => NA ki (Fix ki codes) x -- ^ 
        -> NA ki (Fix ki codes) x
        -> At ki codes x
stiffAt (NA_K x) (NA_K y) = AtSet (Trivial x y)
stiffAt (NA_I x) (NA_I y) = AtFix (stiffAlmu x y)

stiffAl :: (TestEquality ki, EqHO ki)
        => PoA ki (Fix ki codes) xs -- ^
        -> PoA ki (Fix ki codes) ys
        -> Al ki codes xs ys
stiffAl Nil Nil = A0
stiffAl (x :* xs) Nil = ADel x (stiffAl xs Nil)
stiffAl Nil (y :* ys) = AIns y (stiffAl Nil ys)
stiffAl (x :* xs) (y :* ys) = 
  case testEquality x y of
    Just Refl -> AX (stiffAt x y) (stiffAl xs ys)
    Nothing -> AIns y (ADel x (stiffAl xs ys))

-- ** Copy Counting
--
-- $copycounting
--
-- In order to decide which path to follow from the roof to the
-- leaves whenver we are faced with a choice, we will pre-compute
-- the amount of copies present in each subtree.

-- |Algebra for counting copies.
copiesAlgebra :: Const Ann ix -- ^
              -> Rep ki (Const Int) xs
              -> Const Int ix
copiesAlgebra (Const ann) r
  = let inAnn = elimRep (const 0) getConst sum r
     in Const $ case ann of
                  Modify -> inAnn
                  Copy   -> 1 + inAnn
          

-- |Annotates the tree with how many copies are underneath each node
-- (inclusive with self)
--
-- > copies Copy = 1 + copies children
-- > copies Modify = copies children
--
countCopies :: IsNat ix
            => AnnFix ki codes (Const Ann) ix -- ^
            -> AnnFix ki codes (Const Int :*: Const Ann) ix
countCopies = synthesizeAnn (\ca r -> copiesAlgebra ca (mapRep getFst r) :*: ca)
  where
    getFst :: (a :*: b) x -> a x
    getFst (x :*: _) = x

-- |Returns whether or not a subtree constains any copies.
hasCopies :: AnnFix ki codes (Const Int :*: chi) ix -> Bool
hasCopies (AnnFix (Const x :*: _) _) = x > 0

-- |Easily retrieves annotations
myGetAnn :: (Const Int :*: Const Ann) x -> Ann
myGetAnn (_ :*: Const ann) = ann

myGetAnnAt :: NA ki (AnnFix ki codes (Const Int :*: Const Ann)) ('I x) -> Ann
myGetAnnAt (NA_I (AnnFix ann _)) = myGetAnn ann

-- |Easily retrieves annotations
myGetCopies :: (Const Int :*: Const Ann) x -> Int
myGetCopies (Const copies :*: _) = copies

myForgetAnn :: NA ki (AnnFix ki codes (Const Int :*: Const Ann)) at
            -> NA ki (Fix ki codes) at
myForgetAnn = mapNA id forgetAnn

-- ** Computing the Patch
--
-- $computing
--
-- Given trees annotated with information about each of their constructors
-- and how many of those are supposed to be copied, we can finally
-- deterministically translate two tress into a patch.

data InsOrDel (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: (Nat -> Nat -> *) -> * where
  CtxIns :: InsOrDel ki codes (Almu ki codes)
  CtxDel :: InsOrDel ki codes (AlmuMin ki codes)


-- |Finds the element in the @PoA ... xs@ with the most copies
-- and diff the given @AnnFix@.
--
-- PRECONDITION: The @PoA .. xs@ must contain at least one tree with
--               a copy. Always guard this call with 'hasCopies'
--
--
diffCtx :: forall ki codes p ix xs
         . (EqHO ki, TestEquality ki, IsNat ix)
        => InsOrDel ki codes p
        -> AnnFix ki codes (Const Int :*: Const Ann) ix
        -> PoA ki (AnnFix ki codes (Const Int :*: Const Ann)) xs
        -> Ctx ki codes p ix xs
diffCtx cid x xs
 = let maxIdx  = fst $ maximumBy (comparing snd) zipped
       zipped  = zip [0 .. ] elimmed
       elimmed = elimNP (elimNA (const 0) (myGetCopies . getAnn)) xs
    in drop' maxIdx xs
  where
      drop' :: Int
            -> PoA ki (AnnFix ki codes (Const Int :*: Const Ann)) ys
            -> Ctx ki codes p ix ys
      drop' _ Nil = error "unreachable"
      drop' 0 (NA_I y :* ys) =
        case cid of
          CtxIns -> H (diffAlmu x y)           (mapNP myForgetAnn ys)
          CtxDel -> H (AlmuMin (diffAlmu y x)) (mapNP myForgetAnn ys)
      drop' n (y :* ys) = T (myForgetAnn y) (drop' (n - 1) ys)

-- | Takes two annotated trees, and produces a patch
diffAlmu :: forall ki codes ix iy
          . (EqHO ki, IsNat ix, IsNat iy, TestEquality ki)
         => AnnFix ki codes (Const Int :*: Const Ann) ix -- ^ 
         -> AnnFix ki codes (Const Int :*: Const Ann) iy
         -> Almu ki codes ix iy
diffAlmu x@(AnnFix ann1 rep1) y@(AnnFix ann2 rep2) =
  case (myGetAnn ann1, myGetAnn ann2) of
    (Copy, Copy) -> Spn (diffSpine (getSNat $ Proxy @ix) (getSNat $ Proxy @iy) rep1 rep2)
    (Copy, Modify) -> 
      if hasCopies y then diffIns x rep2 else stiffAlmu (forgetAnn x) (forgetAnn y)
    (Modify, Copy) ->
      if hasCopies x then diffDel rep1 y else stiffAlmu (forgetAnn x) (forgetAnn y)
    (Modify, Modify) ->
      if hasCopies x then diffDel rep1 y else stiffAlmu (forgetAnn x) (forgetAnn y)
    where
      diffIns :: AnnFix ki codes (Const Int :*: Const Ann) ix
              -> Rep ki (AnnFix ki codes (Const Int :*: Const Ann)) (Lkup iy codes)
              -> Almu ki codes ix iy
      diffIns x1 rep = case sop rep of Tag c xs -> Ins c (diffCtx CtxIns x1 xs)

      diffDel :: Rep ki (AnnFix ki codes (Const Int :*: Const Ann)) (Lkup ix codes)
              -> AnnFix ki codes (Const Int :*: Const Ann) iy
              -> Almu ki codes ix iy
      diffDel rep x1 = case sop rep of Tag c xs -> Del c (diffCtx CtxDel x1 xs)

-- | Takes two annotated 'Rep's, and produces a patch
diffSpine :: forall ki codes ix iy
           . (TestEquality ki, EqHO ki, IsNat ix, IsNat iy)
          => SNat ix -- ^ We need these to identify the mutrec family 
          -> SNat iy 
          -> Rep ki (AnnFix ki codes (Const Int :*: Const Ann)) (Lkup ix codes)
          -> Rep ki (AnnFix ki codes (Const Int :*: Const Ann)) (Lkup iy codes)
          -> Spine ki codes (Lkup ix codes) (Lkup iy codes)
diffSpine six siy s1@(sop -> Tag c1 p1) s2@(sop -> Tag c2 p2) =
  case testEquality six siy of
    Just Refl ->
      if ((==) `on` mapRep forgetAnn) s1 s2
        then Scp
        else case testEquality c1 c2 of
                   Just Refl ->
                     SCns c1 (mapNP (\(a :*: b) -> diffAt a b) (zipNP p1 p2))
                   Nothing -> SChg c1 c2 (diffAl p1 p2)
    Nothing -> SChg c1 c2 (diffAl p1 p2)


diffAl :: forall ki codes xs ys
        . (EqHO ki, TestEquality ki)
       => PoA ki (AnnFix ki codes (Const Int :*: Const Ann)) xs -- ^
       -> PoA ki (AnnFix ki codes (Const Int :*: Const Ann)) ys
       -> Al ki codes xs ys
diffAl Nil Nil = A0
diffAl Nil (y :* ys) = AIns (mapNA id forgetAnn y) (diffAl Nil ys)
diffAl (x :* xs) Nil = ADel (mapNA id forgetAnn x) (diffAl xs Nil)
diffAl (x@(NA_K k1) :* xs) (y@(NA_K k2) :* ys) = 
  case testEquality k1 k2 of
    Just Refl -> AX (diffAt x y) (diffAl xs ys)
    Nothing -> AIns (mapNA id forgetAnn y) (ADel (mapNA id forgetAnn x) (diffAl xs ys))
diffAl (x@(NA_K _) :* xs) (y@(NA_I _) :* ys) = 
  case myGetAnnAt y of
    Modify -> AIns (mapNA id forgetAnn y) (diffAl (x :* xs) ys)
    Copy -> ADel (mapNA id forgetAnn x) (diffAl xs (y :* ys))
diffAl (x@(NA_I _) :* xs) (y@(NA_K _) :* ys) =
  case myGetAnnAt x of
    Modify -> ADel (mapNA id forgetAnn x) (diffAl xs (y :* ys))
    Copy -> AIns (mapNA id forgetAnn y) (diffAl (x :* xs) ys)
diffAl (x@(NA_I _) :* xs) (y@(NA_I _) :* ys) = 
  case (myGetAnnAt x, myGetAnnAt y) of
    (Modify, _) -> ADel (mapNA id forgetAnn x) (diffAl xs (y :* ys))
    (Copy, Modify) -> AIns (mapNA id forgetAnn y) (diffAl (x :* xs) ys)
    (Copy, Copy) -> 
      case testEquality x y of
        Just Refl -> AX (diffAt x y) (diffAl xs ys)
        -- NOTE we added this case
        Nothing -> AIns (mapNA id forgetAnn y) (ADel (mapNA id forgetAnn x) (diffAl xs ys))

diffAt :: (EqHO ki, TestEquality ki)
       => NA ki (AnnFix ki codes (Const Int :*: Const Ann)) a -- ^
       -> NA ki (AnnFix ki codes (Const Int :*: Const Ann)) a
       -> At ki codes a
diffAt (NA_K x) (NA_K y) = AtSet (Trivial x y)
diffAt (NA_I x) (NA_I y) = AtFix $ diffAlmu x y

-- |The interface function which witnesses thecomplete pipeline.
-- its implementation is straightforward:
--
-- > diff x y = let es = GDiff.diff' x y
-- >                ax = countCopies $ annSrc  x es
-- >                ay = countCopies $ annDest y es
-- >             in diffAlmu ax ay
--
diff :: (EqHO ki , TestEquality ki , IsNat ix)
     => Fix ki codes ix -- ^
     -> Fix ki codes ix
     -> Almu ki codes ix ix
diff x y = let es = GDiff.diff' x y
               ax = countCopies $ annSrc  x es
               ay = countCopies $ annDest y es
            in diffAlmu ax ay

