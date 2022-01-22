module Streaming.IO

import Streaming

||| A `Stream` of `getLine`s
export
stdinLn : HasIO m => Stream (Of String) m r
stdinLn = unfold (\_ => getLine >>= \line => pure (Right (line :> ()))) ()

||| `putStrLn` a `Stream` of `String`s
export
stdoutLn : HasIO m => Stream (Of String) m r -> m r
stdoutLn = destroy (\(a :> b) => putStrLn a >> b) join pure
