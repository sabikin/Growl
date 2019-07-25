module Signal

import Control.Category
import GArrow

infixr 3 ><

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

(><) : PairKind -> PairKind -> PairKind
(><) = PKPair

kpair : Kind -> Kind -> PairKind
kpair k0 k1 = PKPair (PK k0) (PK k1)

data VecKind = VK (List Kind)

fold_vk : VecKind -> PairKind
fold_vk (VK []) = PKNil
fold_vk (VK (x :: xs)) = (PK x) >< (fold_vk (VK xs))


data SF : PairKind -> PairKind -> Type where
  Identity : SF a a
  Compose : SF b c -> SF a b -> SF a c
  First : SF a b -> SF (a >< c) (b >< c)
  Second : SF a b -> SF (c >< a) (c >< b)
  CutL : SF (PKNil >< a) a
  CutR : SF (a >< PKNil) a
  UncutL : SF a (PKNil >< a)
  UncutR : SF a (a >< PKNil)
  Assoc : SF ((a >< b) >< c) (a >< (b >< c))
  Unassoc : SF (a >< (b >< c)) ((a >< b) >< c)

  LiftB : (a -> b) -> SF (PK $ behavior a) (PK $ behavior b)
  Automata : (a -> s -> Pair b s) -> s -> SF (PK $ event a) (PK $ event b)
  Hold : SF (PK $ event a) (PK $ behavior a)
  Sample : SF (kpair (behavior a) Signal.spike) (PK $ event a)
infixr 1 ~~>
(~~>) : PairKind -> PairKind -> Type
(~~>) = SF

liftE : (a -> b) -> SF (PK $ event a) (PK $ event b)
liftE f = Automata ( \x => \_ => (f x, ()) ) ()

implementation Category SF where
  id = Identity
  (.) = Compose

implementation GArrow SF (><) PKNil where
  ga_first = First
  ga_second = Second
  ga_cutl = CutL
  ga_cutr = CutR
  ga_uncutl = UncutL
  ga_uncutr = UncutR
  ga_assoc = Assoc
  ga_unassoc = Unassoc