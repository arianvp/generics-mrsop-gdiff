{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}

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
reify Nil = RList
reify (Cons x) = case reify x of RList -> RList

-- |Proves that the index of a value of type 'NP' is a list.
--  This is useful for pattern matching on said list without
--  having to carry the product around.
listPrfNP :: NP p xs -> ListPrf xs
listPrfNP NP0       = Nil
listPrfNP (_ :* xs) = Cons $ listPrfNP xs
