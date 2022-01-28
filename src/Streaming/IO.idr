module Streaming.IO

import Streaming

||| A `Stream` of `getLine`s
export
stdinLn : HasIO m => Stream (Of String) m r
stdinLn = unfold (\_ => getLine >>= \line => pure (Right (line :> ()))) ()

||| `putStrLn` for each `String` in `Stream (Of String)`
export
stdoutLn : HasIO m => Stream (Of String) m r -> m r
stdoutLn = mapM_ putStrLn
