module Streaming.Core

import Control.Monad.Error.Interface
import Control.Monad.RWS.Interface
import Control.Monad.Reader.Interface
import Control.Monad.State.Interface
import Control.Monad.Trans
import Control.Monad.Writer.Interface
import Control.Monad.Morph
import Data.Functor.Of
import Data.List
import Data.Nat

%default total

||| based on: https://github.com/MarcelineVQ/idris2-streaming/blob/master/src/Streaming/Internal.idr
public export
data Stream : (f : Type -> Type) -> (m : Type -> Type) -> (r : Type) -> Type where
  Step : Inf (f (Stream f m r)) -> Stream f m r
  Effect : Inf (m (Stream f m r)) -> Stream f m r
  Return : r -> Stream f m r
  Build : (forall b. (r -> b) -> (m b -> b) -> (f b -> b) -> b) -> Stream f m r

||| Wrap a new layer of a `Stream`
public export
wrap : f (Stream f m r) -> Stream f m r
wrap x = Step x

||| Wrap a new effect layer of a `Stream`
public export
effect : m (Stream f m r) -> Stream f m r
effect x = Effect x

export
build : (forall b. (r -> b) -> (m b -> b) -> (f b -> b) -> b) -> Stream f m r
build = \phi => phi Return (\x => Effect x) (\x => Step x)

||| collapse a `Stream` into another thing
export
fold : (Functor f, Monad m) => (r -> b) -> (m b -> b) -> (f b -> b) -> Stream f m r -> b
fold return effect step (Return x) = return x
fold return effect step (Effect x) = effect (assert_total fold return effect step <$> x)
fold return effect step (Step x) = step (assert_total fold return effect step <$> x)
fold return effect step (Build g) = g return effect step

||| `fold` but the argument positions are different
export
destroy : (Functor f, Monad m) => (f a -> a) -> (m a -> a) -> (r -> a) -> Stream f m r -> a
destroy step effect return = fold return effect step

||| unfold a `Stream`
export
unfold : (Functor f, Monad m) => (a -> m (Either r (f a))) -> a -> Stream f m r
unfold f a = Effect $ do
  Right a' <- f a
  | Left r => pure (Return r)
  pure (Step (assert_total unfold f <$> a'))

export
inspect : (Functor f, Monad m) => Stream f m r -> m (Either r (f (Stream f m r)))
inspect = destroy (pure . (Right . map (effect {f} {m} . map (either Return wrap)))) join (pure . Left)

export
Functor f => MFunctor (Stream f) where
  hoist f = fold Return (\x => Effect $ f x) (\x => Step x)

export
(Functor f, Monad m) => Functor (Stream f m) where
  map f x = Build (\return, effect, step => fold (return . f) effect step x)

mutual
  export
  (Functor f, Monad m) => Applicative (Stream f m) where
    pure = Return
    x <*> y = do
      assert_total (>>=) x $ \x => y >>= \y => pure (x y)

  export
    (Functor f, Monad m) => Monad (Stream f m) where
      x >>= k = Build (\return, effect, step => fold (fold return effect step . k) effect step x)

export
MonadTrans (Stream f) where
  lift x = Effect (map Return x)

export
(HasIO m, Monad (Stream f m)) => HasIO (Stream f m) where
  liftIO x = lift (liftIO x)

export
(Functor f, MonadState s m) => MonadState s (Stream f m) where
  get = lift get
  put = lift . put
  state f = lift (state f)

export
(Functor f, MonadReader s m) => MonadReader s (Stream f m) where
  ask = lift ask
  local f = hoist (local f)

export
(Functor f, MonadError e m) => MonadError e (Stream f m) where
  throwError = lift . throwError
  stream `catchError` f = fold pure (\x => assert_total catchError (Effect x) f) wrap stream

||| analogous to `Prelude.unfoldr` but for `Stream (Of a)`
export
unfoldr : Monad m => (s -> m (Either r (a, s))) -> s -> Stream (Of a) m r
unfoldr f = unfold $ \x => map from_pair <$> f x

||| analogous to `Data.Stream.iterate` but for `Stream (Of a)`
export
iterate : Monad m => (a -> a) -> a -> Stream (Of a) m r
iterate f = unfoldr $ \x => pure $ Right $ dup (f x)

||| analogous to `Data.Stream.repeat` but for `Stream (Of a)`
export
repeat : Monad m => a -> Stream (Of a) m r
repeat = iterate id

||| yield an element / analogous to `Prelude.singleton` but for `Stream (Of a)`
export
yield : Monad m => a -> Stream (Of a) m ()
yield x = Step (x :> Return ())

||| `Stream m m r` basically means that `Step`s and `Effect`s of the stream are the same thing, we still use `join` to collapse the entire `Stream`
export
run : Monad m => Stream m m r -> m r
run (Return x) = pure x
run (Effect x) = x >>= assert_total run
run (Step x) = x >>= assert_total run
run (Build g) = assert_total run (build g)

||| turns a `Stream` into a list
export
toList : Monad m => Stream (Of a) m r -> m (List a, r)
toList = destroy (\(a :> b) => map (mapFst (a ::)) b) join (\x => pure (Nil, x))

||| `toList` but discards the result
export
toList_ : Monad m => Stream (Of a) m r -> m (List a)
toList_ = destroy (\(a :> b) => map (a ::) b) join (const (pure Nil))

||| construct a `Stream` from a `List` with a result type
export
fromList : r -> List a -> Stream (Of a) m r
fromList r Nil = Return r
fromList r (a :: as) = Step (a :> fromList r as)

||| `fromList` but discards the result
export
fromList_ : List a -> Stream (Of a) m ()
fromList_ = fromList ()

||| cons an element into a `Stream (Of a)`
export
cons : a -> Stream (Of a) m r -> Stream (Of a) m r
cons x stream = Step (x :> stream)

||| essentially the "un" version fo `cons`
export
next : Monad m => Stream (Of a) m r -> m (Either r (a, Stream (Of a) m r))
next stream = case !(inspect stream) of
  Left r => pure (Left r)
  Right (x :> xs) => pure (Right (x, xs))

||| map `Step`s
export
mapf : (Functor f, Monad m) => (forall x. f x -> g x) -> Stream f m r -> Stream g m r
mapf f s = Build (\return, effect, step => fold return effect (step . f) s)

||| monadic version of `mapf`
export
mapfM : (Monad m, Functor f) => (forall x. f x -> m (g x)) -> Stream f m r -> Stream g m r
mapfM f stream = Build (\return, effect, step => fold return effect (effect . map step . f) stream)

||| map values in a `Stream (Of a)`
export
maps : Monad m => (a -> b) -> Stream (Of a) m r -> Stream (Of b) m r
maps f s = mapf (mapFst f) s

||| monadic version of `mapsM`
export
mapsM : Monad m => (a -> m b) -> Stream (Of a) m r -> Stream (Of b) m r
mapsM f s = mapfM (\(c :> g) => (:> g) <$> f c) s

||| replace each element of a stream with an associated `Stream`
export
traverse : (Monad m, Functor f) => (a -> Stream f m x) -> Stream (Of a) m r -> Stream f m r
traverse f = fold pure effect (\(x :> xs) => ignore (f x) >> xs)

||| `for = flip traverse`
export
for : (Monad m, Functor f) => Stream (Of a) m r -> (a -> Stream f m x) -> Stream f m r
for = flip traverse

export
mapM_ : Monad m => (a -> m b) -> Stream (Of a) m r -> m r
mapM_ f = fold pure join (\(x :> xs) => ignore (f x) >> xs)

export
scan : Functor m => (acc -> a -> acc) -> (acc -> b) -> acc -> Stream (Of a) m r -> Stream (Of b) m r
scan step done begin stream = Step (done begin :> loop begin stream)
  where
  loop : acc -> Stream (Of a) m r -> Stream (Of b) m r
  loop acc (Step (x :> xs)) = let acc = step acc x in Step (done acc :> loop acc xs)
  loop acc (Return r) = Return r
  loop acc (Effect m) = Effect (map (assert_total loop acc) m)
  loop acc (Build g) = loop acc (g Return effect wrap)

export
scanM : Monad m => (acc -> a -> m acc) -> (acc -> m b) -> m acc -> Stream (Of a) m r -> Stream (Of b) m r
scanM step done begin stream = Effect $ do
  begin <- begin
  x0 <- done begin
  pure $ Step (x0 :> loop begin stream)
  where
  loop : acc -> Stream (Of a) m r -> Stream (Of b) m r
  loop acc (Step (x :> xs)) = Effect $ do
    acc <- step acc x
    xn <- done acc
    pure $ Step (xn :> assert_total loop acc xs)
  loop acc (Return r) = Return r
  loop acc (Effect m) = Effect $ m >>= pure . assert_total loop acc
  loop acc (Build g) = loop acc (g pure effect wrap)
