import Control.Category
import Control.Arrow

-- %default total
%access public export

record Channel where
  constructor Ch
  f_nyq : Nat

f_sampling : Channel -> Nat
f_sampling c = (f_nyq c) * 2

Show Channel where
  show ch = "Ch " ++ show (f_nyq ch)

data Automata a b = Aut (a -> s -> Pair b s)

loop : ((Pair a c) -> s -> (Pair (Pair b c) s)) -> a -> s -> (Pair b s)
loop f x s = let ((y,_), s') = f (x,z) s in (y,s') where
  z = Basics.snd $ Basics.fst (f (x,z) s)

cnter : (Pair Unit (Lazy Unit)) -> Nat -> (Pair (Pair Nat (Lazy Unit)) Nat)
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

cnter' : Unit -> Nat -> (Pair Nat Nat) 
cnter' = Main.loop cnter

main : IO Unit
main = do
  printLn (cnter' () 3)

{-
aut_loop : Automata (Pair a c) (Pair b c) -> Automata a b
aut_loop (Aut{s} f) = Aut{s} ( \x => \s => let (y,z) = f (x,z) s in y )
-}

Category Automata where
  id = Aut{s=Unit} MkPair

  (Aut{s=sg} g) . (Aut{s=sf} f) =
    Aut{s = Pair sf sg} ( \x => \s =>
      let (s0,s1) = s in
      let (y,s0') = f x s0 in
      let (z,s1') = g y s1 in
      let s' = (s0',s1') in
      (z, s')
    )

Arrow Automata where
  arrow f = Aut{s=Unit} (MkPair . f)
  first (Aut{s} f) = Aut{s} ( \(x,y) => \s =>
    let (x', s') = f x s in ((x',y), s') )

{-
ArrowLoop Automata where
  loop (Aut{s} f) = Aut{s} ( \(x,z) => \s => let (y,z) = f (x,z) s in y )
-}

counter : Automata Bool Nat
counter = Aut (
  \reset => \n => let 
      n' = if reset then 0 else n+1
    in (n', n')
)
