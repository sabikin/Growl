module ActorS where

switchB : Behavior (Behavior a) -> Behavior a

Actor a : Behavior (Vec n a) -> Behavior (Vec n a)
