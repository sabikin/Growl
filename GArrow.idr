module GArrow

import Control.Category

%access public export

infixr 3 ><

interface Category g => GArrow (g: k->k->Type) (p: k->k->k) (u: k) where
  ga_first : g x y -> g (p x z) (p y z)
  ga_second : g x y -> g (p z x) (p z y)
  ga_cutl : g (p u x) x
  ga_cutr : g (p x u) x
  ga_uncutl : g x (p u x)
  ga_uncutr : g x (p x u)
  ga_assoc : g (p (p x y) z) (p x (p y z))
  ga_unassoc : g (p x (p y z)) (p (p x y) z)

interface GArrow g p u => GArrowDrop (g: k->k->Type) (p: k->k->k) (u: k) where
  ga_drop : g x u

interface GArrow g p u => GArrowCopy (g: k->k->Type) (p: k->k->k) (u: k) where
  ga_copy : g x (p x x)

interface GArrow g p u => GArrowSwap (g: k->k->Type) (p: k->k->k) (u: k) where
  ga_swap : g (p x y) (p y x)

interface GArrow g p u => GArrowConst (g: Type->Type->Type) (p: Type->Type->Type) u t where
  ga_const : t -> g u t

interface GArrow g p u => GArrowLoop (g: k->k->Type) (p: k->k->k) (u: k) where
  ga_loopl : g (p z x) (p z y) -> g x y
  ga_loopr : g (p x z) (p y z) -> g x y


interface GArrow g p u => GArrowPair (g: k->k->Type) (p: k->k->k) (u: k) where
  (><) : k -> k -> k

implementation GArrow g p u => GArrowPair g p u where
  a >< b = p a b
