module Circuit

import GArrow

%access public export

interface GArrowLoop g p u => Circuit (g: k->k->Type) (p: k->k->k) (u: k) where
  delay : g a a
