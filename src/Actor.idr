module Actor

record Msg addr where
  constructor MkMsg
  address : addr
  payload : a

record Actor addr where
  constructor MkActor
  behavior : Msg addr -> s -> Pair (List $ Msg addr) s
  state : s
  mailbox : List $ Msg addr

record System addr where
  actors : SortedMap addr Actor
