module Streaming.Core

import Control.Monad.Trans
import Data.Functor.Of
import Data.List
import Data.Nat

||| The `Stream` type
export
data Stream : (f : Type -> Type) -> (m : Type -> Type) -> (r : Type) -> Type where
  Step : Inf (f (Stream f m r)) -> Stream f m r
  Effect : Inf (m (Stream f m r)) -> Stream f m r
  Return : r -> Stream f m r

export
(Functor f, Functor m) => Functor (Stream f m) where
  map f (Step x) = Step (map (map f) x)
  map f (Effect x) = Effect (map (map f) x)
  map f (Return r) = Return (f r)

||| Wrap a new layer of a `Stream`
export
wrap : f (Stream f m r) -> Stream f m r
wrap x = Step x

||| Wrap a new effect layer of a `Stream`
export
effect : m (Stream f m r) -> Stream f m r
effect x = Effect x

||| Fold a stream
export
fold : (Functor f, Functor m) => (f a -> a) -> (m a -> a) -> (r -> a) -> Stream f m r -> a
fold step effect return stream =
  case stream of
    Step x => step $ map (fold step effect return) x
    Effect x => effect $ map (fold step effect return) x
    Return r => return r

||| `fold` but different argument positions
export
build : (Functor f, Functor m) => (r -> a) -> (m a -> a) -> (f a -> a) -> Stream f m r -> a
build return effect step = fold step effect return

||| Unfold a `Stream`
export
unfold : (Functor f, Monad m) => (a -> m (Either r (f a))) -> a -> Stream f m r
unfold f a = Effect $ do
  Right a' <- f a
    | Left r => pure (Return r)
  pure (Step (unfold f <$> a'))

mutual
  export
  (Functor f, Functor m) => Applicative (Stream f m) where
    pure x = Return x
    x <*> y = do
      x' <- x
      y' <- y
      pure (x' y')

  export
  (Functor f, Functor m) => Monad (Stream f m) where
    stream >>= f =
      assert_total $ case stream of
        Step x => Step (map (>>= f) x)
        Effect x => Effect (map (>>= f) x)
        Return r => f r

export
MonadTrans (Stream f) where
  lift x = Effect (map Return x)

export
(HasIO m, Monad (Stream f m)) => HasIO (Stream f m) where
  liftIO x = lift (liftIO x)

||| Inspect a `Stream`
export
inspect : (Functor f, Monad m) => Stream f m r -> m (Either r (f (Stream f m r)))
inspect = fold (pure . (Right . map (effect {f} {m} . map (either pure wrap)))) join (pure . Left)

||| Turns a `Stream` into a list
export
toList : Monad m => Stream (Of a) m r -> m (List a, r)
toList = fold (\(a :> b) => map (mapFst (a ::)) b) join (\x => pure (Nil, x))

||| `toList` but discards the result
export
toList_ : Monad m => Stream (Of a) m r -> m (List a)
toList_ = fold (\(a :> b) => map (a ::) b) join (const (pure Nil))

||| Construct a `Stream` from a `List` with a result type
export
fromList : Monad m => r -> List a -> Stream (Of a) m r
fromList r Nil = Return r
fromList r (a :: as) = Step (a :> fromList r as)

||| `fromList` but discards the result
export
fromList_ : Monad m => List a -> Stream (Of a) m ()
fromList_ = fromList ()

||| A `Stream` of `getLine`s
export
stdinLn : HasIO m => Stream (Of String) m r
stdinLn = unfold (\_ => getLine >>= \line => pure (Right (line :> ()))) ()

||| `putStrLn` a `Stream` of `String`s
export
stdoutLn : HasIO m => Stream (Of String) m r -> m r
stdoutLn = fold (\(a :> b) => putStrLn a *> b) join pure

||| Concatenate an element into a `Stream`
export
cons : Monad m => a -> Stream (Of a) m r -> Stream (Of a) m r
cons x stream = Step (x :> stream)

||| Construct a singleton `Stream`
export
yield : Monad m => a -> Stream (Of a) m ()
yield x = Step (x :> Return ())

||| Transform the functor layer of a `Stream`
export
mapf : (Functor f, Functor m) => (forall x. f x -> g x) -> Stream f m r -> Stream g m r
mapf f stream =
  case stream of
    Return r => Return r
    Effect x => Effect (map (mapf f) x)
    Step x => Step (f (map (mapf f) x))

||| Map through a `Stream`
export
maps : Functor m => (a -> b) -> Stream (Of a) m r -> Stream (Of b) m r
maps f = mapf (mapFst f)


||| Unconcatenate an element from a `Stream`
export
next : Monad m => Stream (Of a) m r -> m (Either r (a, Stream (Of a) m r))
next (Return r)         = pure (Left r)
next (Effect m)         = m >>= next
next (Step (a :> rest)) = pure (Right (a,rest))
