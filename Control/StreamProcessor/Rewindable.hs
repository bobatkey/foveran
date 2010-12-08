module Control.StreamProcessor.Rewindable where

import           Control.StreamProcessor (SP)
import qualified Control.StreamProcessor as SP

data RewindableSP e a b
    = Get    (Maybe a -> RewindableSP e a b)
    | Put    b (RewindableSP e a b)
    | Error  e
    | EOS
    | Mark   (RewindableSP e a b)
    | Rewind (RewindableSP e a b)

rewindableToSP :: RewindableSP e a b -> SP e a b
rewindableToSP = go Nothing []
    where
      go :: Maybe [Maybe a] -> [Maybe a] -> RewindableSP e a b -> SP e a b
      go buffer replaying EOS        = SP.EOS
      go buffer replaying (Error e)  = SP.Error e
      go buffer replaying (Put b k)  = SP.Put b (go buffer replaying k)
      go buffer replaying (Mark k)   = go (Just []) replaying k
      go buffer replaying (Rewind k) = go (Just []) (maybe [] reverse buffer ++ replaying) k
      go buffer []        (Get k)    = SP.Get $ \a -> go (fmap (a:) buffer) [] (k a)
      go buffer (a:as)    (Get k)    = go (fmap (a:) buffer) as (k a)
