module Data.Functor.Of

infixl 0 :>

public export
record Of a b where
  constructor (:>)
  fst : a
  snd : Lazy b

export
Bifunctor Of where
  mapFst f (a :> b) = f a :> b
  mapSnd f (a :> b) = a :> f b
  bimap f g (a :> b) = f a :> g b

export
Functor (Of a) where
  map = mapSnd

export
from_pair : Pair a b -> Of a b
from_pair (a, b) = a :> b

export
to_pair : Of a b -> Pair a b
to_pair (a :> b) = (a, b)
