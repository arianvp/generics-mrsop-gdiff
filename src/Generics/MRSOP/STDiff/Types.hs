{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE GADTs                 #-}
module Generics.MRSOP.STDiff.Types where

import Generics.MRSOP.Base

-- * Functorial Changes
--
-- $functorialchanges
--
-- Represents changes on the /first layer/ of two values of
-- mutually recursive families. For a more in-depth explanation
-- of the datatypes and their meaning we refer the interested reader
-- to the relevant literature:
--
--  - Miraldo, Dagand and Swierstra, TyDe 2017 <https://victorcmiraldo.github.io/data/tyde2017.pdf pdf>
--  - van Putten, MSc thesis <https://dspace.library.uu.nl/handle/1874/380853>
--

-- |Represents a change between two opaque values. When they
-- are equal represents a copy.
data TrivialK (ki :: kon -> *) :: kon -> * where
  Trivial :: ki kon -> ki kon -> TrivialK ki kon 

-- |Represents a change between two atoms, where an atom is
-- either a recursive or an opaque value.
data At (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Atom kon -> * where
  AtSet :: TrivialK ki kon                   -> At ki codes ('K kon)
  AtFix :: (IsNat ix) => Almu ki codes ix ix -> At ki codes ('I ix)

-- |Represents an alignment between two product of atoms.
data Al (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  A0 :: Al ki codes '[] '[]
  AX :: At ki codes x -> Al ki codes xs ys -> Al ki codes (x ': xs)  (x ': ys)
  ADel :: NA ki (Fix ki codes) x -> Al ki codes xs ys -> Al ki codes (x ': xs) ys
  AIns :: NA ki (Fix ki codes) x -> Al ki codes xs ys -> Al ki codes xs (x ': ys)

-- |Represents a change at the coproduct structure.
data Spine (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [[Atom kon]] -> * where
  Scp  :: Spine ki codes s1
  SCns :: Constr s1 c1 
       -> NP (At ki codes) (Lkup c1 s1)
       -> Spine ki codes s1
  SChg :: Constr s1 c1
       -> Constr s1 c2
       -> Al ki codes (Lkup c1 s1) (Lkup c2 s1)
       -> Spine ki codes s1 

-- * Fixpoint Changes
--
-- $fixpointchanges
--
-- The next datatypes represent a sequence of 'Spine', 'Al' and 'At' assembled
-- coupled with operators to describe changes in the recursive structure such
-- as inserting and deleting constructors.


-- |Represents a /one-hole context/ over a @NP (NA ki (fix ki codes)) xs@ where
-- the hole is in a distinguished element indexed by @'I ix@ and is filled
-- with applying @p@ to the relevant indexes.
data Ctx (ki :: kon -> *) (codes :: [[[Atom kon]]]) (p :: Nat -> Nat -> *)
         (ix :: Nat) :: [Atom kon] -> * where
  H :: IsNat iy
    => p ix iy
    -> PoA ki (Fix ki codes) xs
    -> Ctx ki codes p ix ('I iy ': xs)
  T :: NA ki (Fix ki codes) a
    -> Ctx ki codes p ix xs
    -> Ctx ki codes p ix (a ': xs)

-- |Simple synonym for contexts.
type InsCtx ki codes ix xs = Ctx ki codes (Almu ki codes) ix xs

-- |A deletion context needs to swap the indexes in the hole, hence
-- we use a newtype for that.
type DelCtx ki codes ix xs = Ctx ki codes (AlmuMin ki codes) ix xs

-- |The newtype used to swap the indexes to |Almu|.
newtype AlmuMin ki codes ix iy = AlmuMin  { unAlmuMin :: Almu ki codes iy ix }

-- |Represent recursive spines.
data Almu (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Nat -> Nat -> * where
  Spn :: Spine ki codes (Lkup ix codes) -> Almu ki codes ix ix
  Ins :: Constr (Lkup iy codes) c
      -> InsCtx ki codes ix (Lkup c (Lkup iy codes)) -- its an ix with an iy typed-hoed
      -> Almu ki codes ix iy
  Del :: IsNat iy
      => Constr (Lkup ix codes) c
      -> DelCtx ki codes iy (Lkup c (Lkup ix codes))
      -> Almu ki codes ix iy

{-

{-
instance (ShowHO ki) => Show (At ki codes at) where
  show (AtSet t) = show t
  show (AtFix a) = a

instance ShowHO ki => Show (TrivialK ki x) where
  show (Trivial x y) = show x ++ "|" ++ show y


-}  



{-
instance (HasDatatypeInfo ki fam codes, Show1 ki) => Show (Al ki codes xs ys) where
  show A0 = "A0"
  show (AX x xs) = "(AX " ++ show1 x  ++ " " ++ show xs  ++ ")"
  show (ADel x xs) = "(ADel " ++ show x  ++ " " ++ show xs  ++ ")"
  show (AIns x xs) = "(AIns " ++ show x  ++ " " ++ show xs  ++ ")"
-}

{-
instance (IsNat ix,IsNat iy, HasDatatypeInfo ki fam codes, Show1 ki) => Show (AlmuMin ki codes ix iy) where
  show (AlmuMin x) = show x
-}

-- | An NP p xs, but there exists an x in xs such that h x
--
-- Note that:  NP p xs <=> Ctx' p p xs
--
-- and that the list is never empty, because it contains at
-- least the pointed element
--


instance (IsNat ix, HasDatatypeInfo ki fam codes, Show1 ki) => Show (InsCtx ki codes ix xs) where
  show (H p poa) = "(H " ++ show p ++ " " ++ show poa ++ ")"
  show (T n c)   = "(T " ++ show n  ++ " " ++ show c ++ ")"
instance (IsNat ix, HasDatatypeInfo ki fam codes, Show1 ki) => Show (DelCtx ki codes ix xs) where
  show (H p poa) = "(H " ++ show p ++ " " ++ show poa ++ ")"
  show (T n c)   = "(T " ++ show n  ++ " " ++ show c ++ ")"


  -- TODO ins del


instance forall ki fam codes ix iy. (IsNat ix, IsNat iy, Show1 ki, HasDatatypeInfo ki fam codes) => Show (Almu ki codes ix iy) where
  show (Spn s) = "(Spn " ++ showSpine (getSNat @ix Proxy) (getSNat @iy Proxy) s ++ ")"
  show (Ins c ic) = "(Ins " ++ showC c ++ " " ++ show ic ++ ")"
    where showC c = constructorName . constrInfoLkup c $ (datatypeInfo (Proxy @fam) (getSNat @iy Proxy))
  show (Del c ic) = "(Del " ++ showC c ++ " " ++ show ic ++ ")"
    where showC c = constructorName . constrInfoLkup c $ (datatypeInfo (Proxy @fam) (getSNat @ix Proxy))

instance (Show1 p) => Show1 (NP p) where
  show1 np = parens . concat . intersperse " "  $ elimNP show1 np
    where
      parens x = "(" ++ x  ++ ")"


showSpine :: forall ki fam codes ix iy. (Show1 ki, HasDatatypeInfo ki fam codes, IsNat ix,  IsNat iy) => SNat ix -> SNat iy -> Spine ki codes (Lkup ix codes) (Lkup iy codes) -> String
showSpine six siy Scp = "Scp"
showSpine six siy (SCns c x) =  "(Scns " ++ showC c six ++ " " ++ show1 x ++ ")" 
    where showC c six = constructorName . constrInfoLkup c $ (datatypeInfo (Proxy @fam) six)
showSpine six siy (SChg c1 c2 a) = "(SChg " ++ showCX  ++ " " ++ showCY ++ " " ++ show a  ++ ")"
    where showCX = constructorName . constrInfoLkup c1 $ (datatypeInfo (Proxy @fam) six)
          showCY = constructorName . constrInfoLkup c2 $ (datatypeInfo (Proxy @fam) siy)
{-
instance (HasDatatypeInfo ki fam codes, Show1 ki) => Show (Spine ki codes x y) where
  show Scp = "COPY"
  show (SCns c x) = "(Scns " ++ showC c ++ " " ++ show1 x ++ ")" 
    where 
      showC 
      showC c = constructorName . consterInfoLookup c (datatypeInfo (Proxy @fam) (getSNat @ix Proxy))
  show (SChg c1 c2 a) = "(SChg " ++ showC c1  ++ " " ++ showC c2  ++ " " ++ show a  ++ ")"
    where showC c = constructorName . consterInfoLookup c (datatypeInfo (Proxy @fam) (getSNat @ix Proxy))
-}

-- OR what about:  ix iy
guard' :: String -> Bool -> Either String ()
guard' s False = Left s
guard' _ True  = Right ()

instance Show1 SNat where
  show1 = show . go
    where
     go :: SNat n -> Int
     go SZ = 0
     go (SS s) = 1 + go s

-}
