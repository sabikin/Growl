import Control.Category
import Control.Arrow

%access public export

data Auto a b = MkAuto (a -> s -> Pair b s)

loop : (Pair a (Lazy c) -> s -> Lazy (Pair (Pair b (Lazy c)) s)) -> a -> s -> Pair b s
loop f x s = let ((y,_), s') = f (x,z) s in (y,s') where
  z = Basics.snd $ Basics.fst (f (x,z) s)

cnter : Pair Unit (Lazy Unit) -> Nat -> Lazy (Pair (Pair Nat (Lazy Unit)) Nat)
cnter _ s = ((s,()), s+1)

{-
  let (y,z) = f x z
  {y = fst (f x z) ; z = snd (f x z)}

  z = snd (f x z)
  z = snd . (f x) z

  x = f x
  x is a fixpoint of f.

  therefore, z is a fixpoint of `snd . (f x)`.
-}

Category Auto where
  id = MkAuto{s=Unit} MkPair

  (MkAuto{s=sg} g) . (MkAuto{s=sf} f) =
    MkAuto{s = Pair sf sg} ( \x => \s =>
      let (s0,s1) = s in
      let (y,s0') = f x s0 in
      let (z,s1') = g y s1 in
      let s' = (s0',s1') in
      (z, s')
    )

Arrow Auto where
  arrow f = MkAuto{s=Unit} (MkPair . f)
  first (MkAuto{s} f) = MkAuto{s} ( \(x,y) => \s =>
    let (x', s') = f x s in ((x',y), s') )

{-
ArrowLoop Auto where
  loop (Aut{s} f) = Aut{s} (Main.loop f)
-}

counter : Auto Bool Nat
counter = MkAuto (
  \reset => \n => let 
      n' = if reset then 0 else n+1
    in (n', n')
)
