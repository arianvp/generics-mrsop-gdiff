{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds       #-}

-- | For the lack of a better name, here we put random stuff
module Generics.MRSOP.GDiff.Util where

import Generics.MRSOP.Base hiding (listPrfNP)
import Generics.MRSOP.Util ((:++:))

-- |Convenient constraint synonyms
type L1 xs          = (IsList xs) 
type L2 xs ys       = (IsList xs, IsList ys) 
type L3 xs ys zs    = (IsList xs, IsList ys, IsList zs) 
type L4 xs ys zs as = (IsList xs, IsList ys, IsList zs, IsList as) 

data RList :: [k] -> * where
  RList :: IsList ts => RList ts

-- this seems more like "Coerce" to me
{-# INLINE reify #-}
reify :: ListPrf ts -> RList ts
reify LP_Nil      = RList
reify (LP_Cons x) = case reify x of RList -> RList

-- |Proves that the index of a value of type 'NP' is a list.
--  This is useful for pattern matching on said list without
--  having to carry the product around.
listPrfNP :: NP p xs -> ListPrf xs
listPrfNP Nil       = LP_Nil
listPrfNP (_ :* xs) = LP_Cons $ listPrfNP xs

-- In Agda this would be:
-- ++⁻ : {A : Set}
--       {P : A -> Set}
--       (xs : List A)
--       {ys : List A} 
--     → All P (xs ++ ys) → All P xs × All P ys
-- ++⁻ []       p          = [] , p
-- ++⁻ (x ∷ xs) (px ∷ pxs) = Prod.map (px ∷_) id (++⁻ _ pxs)
--
--   Note in particular, that xs is not an implicit argument,
--   and that we explicitly pattern match on it.
--
--   In haskell, types and values are separated, but we can 
--   carry around the Singleton LstPrf in order to
--   discover on the type-level the list, by pattern matching
split :: ListPrf xs -> NP p (xs :++: ys) -> (NP p xs, NP p ys)
split LP_Nil poa = (Nil, poa)
split (LP_Cons p) (x :* rs) =
  let (xs, rest) = split p rs
   in (x :* xs, rest)

