module Streaming.Core

import Control.Monad.Error.Interface
import Control.Monad.RWS.Interface
import Control.Monad.Reader.Interface
import Control.Monad.State.Interface
import Control.Monad.Trans
import Control.Monad.Writer.Interface
import Data.Functor.Of
import Data.List
import Data.Nat

||| The `Stream` type
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

export
fold : (Functor f, Monad m) => (r -> b) -> (m b -> b) -> (f b -> b) -> Stream f m r -> b
fold return effect step (Return x) = return x
fold return effect step (Effect x) = effect (fold return effect step <$> x)
fold return effect step (Step x) = step (fold return effect step <$> x)
fold return effect step (Build g) = g return effect step

export
destroy : (Functor f, Monad m) => (f a -> a) -> (m a -> a) -> (r -> a) -> Stream f m r -> a
destroy step effect return = fold return effect step

||| Unfold a `Stream`
export
unfold : (Functor f, Monad m) => (a -> m (Either r (f a))) -> a -> Stream f m r
unfold f a = Effect $ do
  Right a' <- f a
  | Left r => pure (Return r)
  pure (Step (unfold f <$> a'))

export
inspect : (Functor f, Monad m) => Stream f m r -> m (Either r (f (Stream f m r)))
inspect = destroy (pure . (Right . map (effect {f} {m} . map (either Return wrap)))) join (pure . Left)

export
hoist : (Functor f, Monad m) => (forall a. m a -> n a) -> Stream f m r -> Stream f n r
hoist f = fold Return (\x => Effect $ f x) (\x => Step x)

export
(Functor f, Monad m) => Functor (Stream f m) where
  map f x = Build (\return, effect, step => fold (return . f) effect step x)

mutual
  export
  (Functor f, Monad m) => Applicative (Stream f m) where
    pure = Return
    x <*> y = do
      f <- x
      v <- y
      pure (f v)

  export
    (Functor f, Monad m) => Monad (Stream f m) where
      x >>= k = assert_total Build (\return, effect, step => fold (fold return effect step . k) effect step x)

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
  stream `catchError` f = fold pure (\x => Effect x `catchError` f) (\x => Step x) stream

export
yield : Monad m => a -> Stream (Of a) m ()
yield x = Step (x :> Return ())

export
run : Monad m => Stream m m r -> m r
run (Return x) = pure x
run (Effect x) = x >>= run
run (Step x) = x >>= run
run (Build g) = run (build g)

||| Turns a `Stream` into a list
export
toList : Monad m => Stream (Of a) m r -> m (List a, r)
toList = destroy (\(a :> b) => map (mapFst (a ::)) b) join (\x => pure (Nil, x))

||| `toList` but discards the result
export
toList_ : Monad m => Stream (Of a) m r -> m (List a)
toList_ = destroy (\(a :> b) => map (a ::) b) join (const (pure Nil))

||| Construct a `Stream` from a `List` with a result type
export
fromList : r -> List a -> Stream (Of a) m r
fromList r Nil = Return r
fromList r (a :: as) = Step (a :> fromList r as)

||| `fromList` but discards the result
export
fromList_ : List a -> Stream (Of a) m ()
fromList_ = fromList ()

||| Concatenate an element into a `Stream`
export
cons : a -> Stream (Of a) m r -> Stream (Of a) m r
cons x stream = Step (x :> stream)

export
next : Monad m => Stream (Of a) m r -> m (Either r (a, Stream (Of a) m r))
next stream = case !(inspect stream) of
  Left r => pure (Left r)
  Right (x :> xs) => pure (Right (x, xs))

export
mapf : (Functor f, Monad m) => (forall x. f x -> g x) -> Stream f m r -> Stream g m r
mapf f s = Build (\return, effect, step => fold return effect (step . f) s)

export
mapfM : (Monad m, Functor f) => (forall x. f x -> m (g x)) -> Stream f m r -> Stream g m r
mapfM f stream = Build (\return, effect, step => fold return effect (effect . map step . f) stream)

export
maps : Monad m => (a -> b) -> Stream (Of a) m r -> Stream (Of b) m r
maps f s = mapf (mapFst f) s

export
mapsM : Monad m => (a -> m b) -> Stream (Of a) m r -> Stream (Of b) m r
mapsM f s = mapfM (\(c :> g) => (:> g) <$> f c) s

export
traverse : (Monad m, Functor f) => (a -> Stream f m ()) -> Stream (Of a) m r -> Stream f m r
traverse f = fold pure effect (\(x :> xs) => f x >> xs)

export
for : (Monad m, Functor f) => Stream (Of a) m r -> (a -> Stream f m ()) -> Stream f m r
for = flip traverse
