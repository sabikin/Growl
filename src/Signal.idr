module Signal

import Control.Category
import Monoidal

%access public export

data Tag = Event | Behavior
data Kind = MkKind Tag Type

event : Type -> Kind
event a = MkKind Event a

behavior : Type -> Kind
behavior a = MkKind Behavior a

spike : Kind
spike = event Unit

data PairKind = PK Kind | PKNil | PKPair PairKind PairKind

infixr 3 ><
(><) : PairKind -> PairKind -> PairKind
(><) = PKPair

kpair : Kind -> Kind -> PairKind
kpair k0 k1 = PKPair (PK k0) (PK k1)

data VecKind = VK (List Kind)

fold_vk : VecKind -> PairKind
fold_vk (VK []) = PKNil
fold_vk (VK (x :: xs)) = (PK x) >< (fold_vk (VK xs))

interface Tagged (f: Type->k) where
  (><) : k -> k -> k

data SF : PairKind -> PairKind -> Type where
  Identity : SF a a
  Compose : SF b c -> SF a b -> SF a c
  First : SF a b -> SF (a >< c) (b >< c)
  CutL : SF (PKNil >< a) a
  UncutL : SF a (PKNil >< a)
  Assoc : SF ((a >< b) >< c) (a >< (b >< c))
  Unassoc : SF (a >< (b >< c)) ((a >< b) >< c)
  Drop : SF a PKNil
  Copy : SF a (a >< a)
  Swap : SF (a >< b) (b >< a)
  Loop : SF (a >< c) (b >< c) -> SF a b

  LiftB : (a -> b) -> SF (PK $ behavior a) (PK $ behavior b)
  Auto : (a -> s -> Pair b s) -> s -> SF (PK $ event a) (PK $ event b)
  Hold : SF (PK $ event a) (PK $ behavior a)
  Sample : SF (kpair (behavior a) Signal.spike) (PK $ event a)
infixr 1 ~~>
(~~>) : PairKind -> PairKind -> Type
(~~>) = SF

liftE : (a -> b) -> SF (PK $ event a) (PK $ event b)
liftE f = Auto ( \x => \_ => (f x, ()) ) ()

Category SF where
  id = Identity
  (.) = Compose

[G_SF] GArrow SF (><) PKNil where
  ga_first = First
  ga_second f = Swap >>> (First f) >>> Swap
  ga_cutl = CutL
  ga_cutr = Swap >>> CutL
  ga_uncutl = UncutL
  ga_uncutr = UncutL >>> Swap
  ga_assoc = Assoc
  ga_unassoc = Unassoc

[GDrop_SF] GArrowDrop SF (><) PKNil using G_SF where
  ga_drop = Drop

[GCopy_SF] GArrowCopy SF (><) PKNil using G_SF where
  ga_copy = Copy

[GSwap_SF] GArrowSwap SF (><) PKNil using G_SF where
  ga_swap = Swap

[GLoop_SF] GArrowLoop SF (><) PKNil using GSwap_SF where
  ga_loopl = Loop
  ga_loopr f = Loop (ga_swap >>> f >>> ga_swap)
