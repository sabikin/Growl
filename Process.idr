import Control.Category
import Control.Arrow
import Automata

%access public export

record Channel where
  constructor MKChannel
  f_nyq : Nat

f_sampling : Channel -> Nat
f_sampling c = (f_nyq c) * 2
