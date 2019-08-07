module Duplex

import Control.Category
import GArrow
import Signal

data Connector = CNil | Forward Signal.Kind | Backward Signal.Kind | CPair Connector Connector

infixr 3 ><
(><) : Connector -> Connector -> Connector
(><) = CPair

inv : Connector -> Connector
inv CNil = CNil
inv (Forward x) = (Forward x)
inv (Backward x) = (Forward x)
inv (CPair x y) = (inv x) >< (inv y)

from_pk : Signal.PairKind -> Connector
from_pk PKNil = CNil
from_pk (PK x) = Forward x
from_pk (PKPair x y) = CPair (from_pk x) (from_pk y)

io : Signal.PairKind -> Signal.PairKind -> Connector
io a b = (from_pk a) >< (inv $ from_pk b)

duplex : Signal.PairKind -> Connector
duplex a = io a a

data Block : Connector -> Connector -> Type where
  SF : Signal.SF a b -> Block (from_pk a) (from_pk b)

  Identity : Block a a
  Compose : Block b c -> Block a b -> Block a c
  First : Block a b -> Block (a >< c) (b >< c)
  CutL : Block (CNil >< a) a
  UncutL : Block a (CNil >< a)
  Assoc : Block ((a >< b) >< c) (a >< (b >< c))
  Unassoc : Block (a >< (b >< c)) ((a >< b) >< c)
  Drop : Block a CNil
  Copy : Block a (a >< a)
  Swap : Block (a >< b) (b >< a)
  Loop : Block (a >< c) (b >< c) -> Block a b

  Invert : Block (a >< b) (c >< d) -> Block (a >< (inv d)) (c >< (inv b))

Category Block where
  id = Identity
  (.) = Compose

[G_Block] GArrow Block (><) CNil where
  ga_first = First
  ga_second f = Swap >>> (First f) >>> Swap
  ga_cutl = CutL
  ga_cutr = Swap >>> CutL
  ga_uncutl = UncutL
  ga_uncutr = UncutL >>> Swap
  ga_assoc = Assoc
  ga_unassoc = Unassoc

[GDrop_Block] GArrowDrop Block (><) CNil using G_Block where
  ga_drop = Drop

[GCopy_Block] GArrowCopy Block (><) CNil using G_Block where
  ga_copy = Copy

[GSwap_Block] GArrowSwap Block (><) CNil using G_Block where
  ga_swap = Swap

[GLoop_Block] GArrowLoop Block (><) CNil using GSwap_Block where
  ga_loopl = Loop
  ga_loopr f = Loop (ga_swap >>> f >>> ga_swap)
