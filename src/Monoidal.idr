module Monoidal

import Control.Category
import Control.Arrow
import Data.Morphisms

%access public export

interface Category hom => Monoidal (hom: ob->ob->Type) (prod: ob->ob->ob) (unit: ob) | hom where
  product : hom x y -> hom x' y' -> hom (prod x x') (prod y y')
  l_unitor : hom (prod unit x) x
  r_unitor : hom (prod x unit) x
  l_ununitor : hom x (prod unit x)
  r_ununitor : hom x (prod x unit)
  assoc : hom (prod (prod x y) z) (prod x (prod y z))
  unassoc : hom (prod x (prod y z)) (prod (prod x y) z)

infixr 3 ><
(><) : Monoidal{ob} hom prod unit => ob -> ob -> ob
(><){prod} = prod

infixr 3 ***
(***) : Monoidal{ob} hom prod unit => hom x y -> hom x' y' -> hom (prod x x') (prod y y')
(***){prod}{unit} = product{prod}{unit}

first : Monoidal hom prod unit => hom x y -> hom (prod x z) (prod y z)
first = (*** id)

second : Monoidal hom prod unit => hom x y -> hom (prod z x) (prod z y)
second = (id ***)

interface Monoidal g p u => SymmetricMonoidal (g: k->k->Type) (p: k->k->k) (u: k) where
  braid : g (p x y) (p y x)

interface SymmetricMonoidal g p u => TracedMonoidal (g: k->k->Type) (p: k->k->k) (u: k) where
  trace : g (p x z) (p y z) -> g x y

interface Monoidal m p u => CartesianMonoidal (m: k->k->Type) (p: k->k->k) (u: k) where
  diag : m x (p x x)
  aug : m x u

interface CartesianMonoidal hom p u => CartesianClosedMonoidal (hom: k->k->Type) (internal_hom: k->k->k) (p: k->k->k) (u: k) where
  ev : hom (p (internal_hom x y) x) y


Arrow a => Monoidal a Pair Unit where
  product = (***)
  l_unitor = arrow ( \((),x) => x )
  r_unitor = arrow ( \(x,()) => x )
  l_ununitor = arrow ( \x => ((),x) )
  r_ununitor = arrow ( \x => (x,()) )
  assoc = arrow ( \((x,y),z) => (x,(y,z)) )
  unassoc = arrow ( \(x,(y,z)) => ((x,y),z) )

Arrow a => SymmetricMonoidal a Pair Unit where
  braid = arrow ( \(x,y) => (y,x) )

ArrowLoop a => TracedMonoidal a Pair Unit where
  trace = loop

Arrow a => CartesianMonoidal a Pair Unit where
  diag = arrow ( \x => (x,x) )
  aug = arrow ( \x => () )

ArrowApply a => CartesianClosedMonoidal a a Pair Unit where
  ev = app


interface SymmetricMonoidal hom prod unit => CompactClosed (hom: ob->ob->Type) (prod: ob->ob->ob) (unit: ob) where
  dual : ob -> ob
  ev : hom (prod (dual x) x) unit
  coev : hom unit (prod x (dual x))

interface TracedMonoidal m p u => Circuit (m: k->k->Type) (p: k->k->k) (u: k) where
  delay : m a a

{-

Arrow a => MonoidalReify a Pair Unit x y x y where
  ga_reify = arrow

Arrow a => MonoidalConst a Pair Unit t where
  ga_const = arrow . const

interface Monoidal g p u => MonoidalReify (g: Type->Type->Type) (p: Type->Type->Type) u a b c d where
  ga_reify : (a -> b) -> g c d

interface Monoidal g p u => MonoidalConst (g: Type->Type->Type) (p: Type->Type->Type) u t where
  ga_const : t -> g u t

-}

{-
  data Expr : Monoidal{k} g p u => k -> Type where
    Var : Monoidal{k} g p u => String -> Expr{k}{g}{p}{u} a
    App : Monoidal{k} g p u => g a b -> Expr{k}{g}{p}{u} a -> Expr{k}{g}{p}{u} b

  data Assign : Monoidal{k} g p u => k -> Type where
    MkAssign : Monoidal{k} g p u => String -> Expr{k}{g}{p}{u} a -> Assign{k}{g}{p}{u} a

  infixr 4 :=
  (:=) : Monoidal g p u => String -> Expr{g}{p}{u} a -> Assign{g}{p}{u} a
  (:=) = MkAssign

  infixr 4 <$$>
  (<$$>) : Monoidal g p u => g a b -> Expr{g}{p}{u} a -> Expr{g}{p}{u} b
  (<$$>) {g}{p}{u} f x = App{g}{p}{u} f x

  f : Integer -> Integer
  f x = x+1

  g : Morphism Integer Integer
  g = ga_reify{p=Pair}{u=Unit} f

  counter : Automata Bool Int
  counter = garrow "Reset" "Count" [
    "Count" := If (Var "Reset") Then 0 Else (delay (Var "Count") + 1)
  ]
-}
