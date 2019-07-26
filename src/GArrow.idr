module GArrow

import Control.Category
import Control.Arrow
import Data.Morphisms

%access public export

interface Category g => GArrow (g: k->k->Type) (p: k->k->k) (u: k) | g where
  ga_first : g x y -> g (p x z) (p y z)
  ga_second : g x y -> g (p z x) (p z y)
  ga_cutl : g (p u x) x
  ga_cutr : g (p x u) x
  ga_uncutl : g x (p u x)
  ga_uncutr : g x (p x u)
  ga_assoc : g (p (p x y) z) (p x (p y z))
  ga_unassoc : g (p x (p y z)) (p (p x y) z)
infixr 3 ><
(><) : GArrow{k} g p u => k -> k -> k
(><){p} = p

interface GArrow g p u => GArrowDrop (g: k->k->Type) (p: k->k->k) (u: k) where
  ga_drop : g x u

interface GArrow g p u => GArrowCopy (g: k->k->Type) (p: k->k->k) (u: k) where
  ga_copy : g x (p x x)

interface GArrow g p u => GArrowSwap (g: k->k->Type) (p: k->k->k) (u: k) where
  ga_swap : g (p x y) (p y x)

interface GArrow g p u => GArrowReify (g: Type->Type->Type) (p: Type->Type->Type) u a b c d where
  ga_reify : (a -> b) -> g c d

interface GArrow g p u => GArrowConst (g: Type->Type->Type) (p: Type->Type->Type) u t where
  ga_const : t -> g u t

interface GArrow g p u => GArrowLoop (g: k->k->Type) (p: k->k->k) (u: k) where
  ga_loopl : g (p x z) (p y z) -> g x y
  ga_loopr : g (p z x) (p z y) -> g x y

interface GArrow g p u => GArrowApply (g: Type->Type->Type) (p: Type->Type->Type) u where
  ga_applyl : g (p a (g a b)) b
  ga_applyr : g (p (g a b) a) b

interface GArrowLoop g p u => Circuit (g: k->k->Type) (p: k->k->k) (u: k) where
  delay : g a a

Arrow a => GArrow a Pair Unit where
  ga_first = first
  ga_second = second
  ga_cutl = arrow ( \((),x) => x )
  ga_cutr = arrow ( \(x,()) => x )
  ga_uncutl = arrow ( \x => ((),x) )
  ga_uncutr = arrow ( \x => (x,()) )
  ga_assoc = arrow ( \((x,y),z) => (x,(y,z)) )
  ga_unassoc = arrow ( \(x,(y,z)) => ((x,y),z) )

Arrow a => GArrowDrop a Pair Unit where
  ga_drop = arrow ( \x => () )

Arrow a => GArrowSwap a Pair Unit where
  ga_swap = arrow ( \(x,y) => (y,x) )

Arrow a => GArrowReify a Pair Unit x y x y where
  ga_reify = arrow

Arrow a => GArrowConst a Pair Unit t where
  ga_const = arrow . const

ArrowLoop a => GArrowLoop a Pair Unit where
  ga_loopl = loop
  ga_loopr f = loop (ga_swap{u=Unit} >>> f >>> ga_swap{u=Unit})

ArrowApply a => GArrowApply a Pair Unit where
  ga_applyl = ga_swap{u=Unit} >>> app
  ga_applyr = app


data Expr : GArrow{k} g p u => k -> Type where
  Var : GArrow{k} g p u => String -> Expr{k}{g}{p}{u} a
  App : GArrow{k} g p u => g a b -> Expr{k}{g}{p}{u} a -> Expr{k}{g}{p}{u} b

data Assign : GArrow{k} g p u => k -> Type where
  MkAssign : GArrow{k} g p u => String -> Expr{k}{g}{p}{u} a -> Assign{k}{g}{p}{u} a

infixr 4 :=
(:=) : GArrow g p u => String -> Expr{g}{p}{u} a -> Assign{g}{p}{u} a
(:=) = MkAssign

infixr 4 <$$>
(<$$>) : GArrow g p u => g a b -> Expr{g}{p}{u} a -> Expr{g}{p}{u} b
(<$$>) {g}{p}{u} f x = App{g}{p}{u} f x

f : Integer -> Integer
f x = x+1

g : Morphism Integer Integer
g = ga_reify{p=Pair}{u=Unit} f

{-
  counter : Automata Bool Int
  counter = garrow "Reset" "Count" [
    "Count" := If (Var "Reset") Then 0 Else (delay (Var "Count") + 1)
  ]
-}
