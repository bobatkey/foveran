{-# LANGUAGE BangPatterns, TupleSections #-}

-- |
-- Module         : Data.MonadicStream
-- Copyright      : Robert Atkey 2012
-- License        : BSD3
--
-- Maintainer     : bob.atkey@gmail.com
-- Stability      : experimental
-- Portability    : unknown
--
-- Types for describing streams interleaved with monadic effects.

module Data.MonadicStream
    ( Stream (..), StreamStep (..)
    , nil
    , cons
    , append
    , concat
    , unfold
    , unfold'
    , replicate
    , replicateM
    , generate
    , zip
    , ofList

    , Reader (..), ReaderStep (..)
    , head
    , consumeBy
    , foldl
    , foldl'
    , toList

    , printAll
    , mapM_

    , Processor (..), ProcessorStep (..)
    , map
    , mapM
    , filter
    , iterate
    , concatMap
    , concatMapAccum
    , concatMapAccumM
    , ofStream

    , (|>|)
    , (>>|)
    , (>>>)
    , (|>>)
    )
    where

import           Prelude hiding (head, map, filter, mapM, mapM_, concat, concatMap, foldl, zip, replicate, iterate)
import qualified Data.List as L
import           Control.Applicative (liftA)
import           Control.Monad (ap)
import           Control.Monad.Trans (MonadTrans (..), MonadIO (..))

{------------------------------------------------------------------------------}
-- | A stream of elements of type 'a' that commits monadic actions in
-- the monad 'm' in order to produce elements. The stream may have an
-- end.
newtype Stream m a
    = Stream { forceStream :: m (StreamStep m a) }

data StreamStep m a
    = StreamElem a (Stream m a)
    | StreamEnd

nil :: Monad m => Stream m a
nil = Stream $ return StreamEnd

cons :: Monad m => a -> Stream m a -> Stream m a
cons a as = Stream $ return (StreamElem a as)

ofList :: Monad m => [a] -> Stream m a
ofList []     = nil
ofList (a:as) = cons a (ofList as)

append :: Monad m => Stream m a -> Stream m a -> Stream m a
append xs ys = Stream $ do
  xsStep <- forceStream xs
  case xsStep of
    StreamElem x xs' -> forceStream (cons x (xs' `append` ys))
    StreamEnd        -> forceStream ys

concat :: Monad m => [Stream m a] -> Stream m a
concat streams = L.foldl append nil streams

unfold :: Monad m => (s -> m (Maybe (s,a))) -> s -> Stream m a
unfold stepper s =
    Stream $ do
      v <- stepper s
      case v of
        Nothing     -> return StreamEnd
        Just (s',a) -> return (StreamElem a (unfold stepper s'))
{-# NOINLINE unfold #-}

unfold' :: Monad m => (s -> m (Maybe (s,[a]))) -> s -> Stream m a
unfold' stepper s =
    Stream $ do
      v <- stepper s
      case v of
        Nothing      -> return StreamEnd
        Just (s',as) -> forceStream $ loop as s'
    where
      loop []     s' = unfold' stepper s'
      loop (a:as) s' = Stream $ return (StreamElem a (loop as s'))

generate :: Monad m => m (Maybe a) -> Stream m a
generate generator = unfold f ()
    where
      {-# INLINE f #-}
      f () = do v <- generator; return (((),) <$> v)
{-# INLINE generate #-}

-- | Zips two streams together. The effects of the first stream are
-- executed before the effects of the second stream. If the streams
-- are of differing length, then the generated stream ends when the
-- shorter one ends, and the remaining effects of the other stream are
-- not executed.
zip :: Monad m => Stream m a -> Stream m b -> Stream m (a,b)
zip xs ys =
    Stream $ do
      xsStep <- forceStream xs
      ysStep <- forceStream ys
      case (xsStep, ysStep) of
        (StreamElem x xs, StreamElem y ys) -> return (StreamElem (x,y) (zip xs ys))
        (StreamEnd,       _)               -> return StreamEnd
        (_,               StreamEnd)       -> return StreamEnd

replicate :: Monad m => Int -> a -> Stream m a
replicate n a =
    unfold (\i -> return (if i == 0 then Nothing else Just (i-1,a))) n
{-# INLINE replicate #-}

replicateM :: Monad m => Int -> m a -> Stream m a
replicateM n action = unfold f n
    where f 0 = return Nothing
          f i = do a <- action; return (Just (n-1,a))

{------------------------------------------------------------------------------}
-- | `Reader e a b` represents functions that read 'a's before
-- yielding a result of type 'b', while commiting monadic actions in
-- the monad 'm'.
newtype Reader a m b
    = Reader { forceReader :: m (ReaderStep a m b) }

data ReaderStep a m b
    = Read    (Maybe a -> Reader a m b)
    | ReadEnd b

instance Monad m => Monad (Reader a m) where
    return a     = Reader $ return (ReadEnd a)
    reader >>= f = Reader $ do
      readerStep <- forceReader reader
      case readerStep of
        Read k    -> return (Read (\i -> k i >>= f))
        ReadEnd b -> forceReader (f b)

instance MonadTrans (Reader a) where
    lift action =
        Reader $ do result <- action
                    return (ReadEnd result)

instance MonadIO m => MonadIO (Reader a m) where
    liftIO action = lift $ liftIO action

instance Monad m => Applicative (Reader a m) where
    pure  = return
    (<*>) = ap

instance Monad m => Functor (Reader a m) where
    fmap = liftA

head :: Monad m => Reader a m (Maybe a)
head = Reader $ return (Read $ \i -> Reader $ return (ReadEnd i))

toList :: Monad m => Reader a m [a]
toList = reverse <$> foldl (\as a -> a:as) []

consumeBy :: Monad m => (s -> Maybe a -> m (Either s b)) -> s -> Reader a m b
consumeBy f s = do
  a <- head
  r <- lift (f s a)
  case r of
    Left s' -> consumeBy f s'
    Right b -> return b
{-# NOINLINE consumeBy #-}

{-
makeReader :: Monad m => (s -> m (Either (Maybe a -> s) b)) -> s -> Reader a m b
makeReader stepper s =
    Reader $ do
      action <- stepper s
      case action of
        Left k  -> return (Read $ \input -> makeReader stepper (k input))
        Right b -> return (ReadEnd b)
{-# NOINLINE makeReader #-}
-}

{-
data Stream' m a =
  forall s. Stream' !(s -> m (Maybe (a,s))) !s

data StreamStep s a
   = StreamEmit a s
   | StreamSkip s
   | StreamStop

data Reader' a m b =
  forall s. Reader' !(s -> m (ReaderStep s a b)) !s

data ReaderStep s a b
   = ReaderRead  (Maybe a -> s)
   | ReaderSkip  s
   | ReaderYield b

data Processor' a m b =
  forall s. Processor' !(s -> m (Step s a b)) !s

-- specialise to synchronous processors?
-- effect-free processors?
-- real-time processors?
-- asynchronous composition of processors?

data ProcessorStep s a b
   = ProcessorEmit b s
   | ProcessorRead (Maybe a -> s)
   | ProcessorSkip s
   | ProcessorStop

(|>|) :: Monad m => Stream' m a -> Reader' a m b -> m b
Stream' streamStep sS |>| Reader' readStep rS = loop sS rS
  where loop sS rS = do
          rAction <- readStep rS
          case rAction of
            ReaderRead k   -> do
              sAction <- streamStep sS
              case sAction of
                Just (a,sS') -> loop sS' (k (Just a))
                Nothing      -> loop2 (k Nothing)
            ReaderSkip rS' -> loop sS rS'
            ReaderYield b  -> return b

        loop2 rS = do
          rAction <- readStep rS
          case rAction of
            Left k  -> loop2 (k Nothing)
            Right b -> return b

(|>>) :: Monad m => Stream' m a -> Processor' a m b -> Stream' m b
Stream' streamStep sS |>> Processor' processorStep pS =
  Stream' step (Left (sS,pS))
  where step (Together sS pS) = do
          pAction <- processorStep pS
          case pAction of
            ProcessorEmit b pS' -> return (StreamEmit (b, Together sS pS'))
            ProcessorRead k     -> do
              sAction <- streamStep sS
              case sAction of
                StreamEmit a sS' -> return (StreamSkip (Together sS' (k (Just a))))
                StreamSkip sS'   -> return (StreamSkip (SinkWaiting sS' k)
                StreamEnd        -> return (StreamSkip (Alone (k Nothing)))
            ProcessorSkip pS'  -> return (StreamSkip (Together sS pS'))
            ProcessorStop      -> return StreamEnd
        step (SinkWaiting sS k) -> do
          sAction <- streamStep sS
          case sAction of
            StreamEmit a sS' -> return (StreamSkip (Together sS' (k (Just a))))
            StreamSkip sS'   -> return (StreamSkip (SinkWaiting sS' k))
            StreamEnd        -> return (StreamSkip (Alone (k Nothing)))
        step (Alone pS) = do
          pAction <- processorStep pS
          case pAction of
            ProcessorEmit b pS' -> return (StreamEmit b (Alone pS'))
            ProcessorRead k     -> return (StreamSkip (Alone (k Nothing)))
            ProcessorStop       -> return StreamEnd

(>>|) :: Monad m => Processor' a m b -> Reader' b m c -> Reader' a m c
Processor' processorStep pS >>| Reader' readerStep rS =
  Reader' step (Together pS rS)
  where step (Together pS rS) = do
          rAction <- readerStep rS
          case rAction of
            ReaderRead k -> do
              pAction <- processorStep pS
              case pAction of
                ProcessorEmit b pS' -> return (ReaderSkip (Together pS' (k (Just b))))
                ProcessorRead k'    -> return (ReaderRead (\input -> SinkWaiting (k' input) k))
                ProcessorSkip pS'   -> return (ReaderSkip (SinkWaiting pS' k))
                ProcessorStop       -> return (ReaderSkip (Alone (k Nothing)))
            ReaderYield b -> return (ReaderYield b)
        step (Alone rS) = do
          rAction <- readerStep rS
          case rAction of
            ReaderRead k   -> return (ReaderSkip (Alone (k Nothing)))
            ReaderSkip rS' -> return (ReaderSkip (Alone rS'))
            ReaderYield b  -> return (ReaderYield b)
        step (SinkWaiting pS k) = do
          pAction <- processorStep pS
          case pAction of
            ProcessorEmit b pS' -> return (ReaderSkip (Together pS' (k (Just b))))
            ProcessorRead k'    -> return (ReaderRead (\input -> ReaderWaiting (k' input) k))
            ProcessorSkip pS'   -> return (ReaderSkip (SinkWaiting pS' k))
            ProcessorStop       -> return (ReaderSkip (Alone (k Nothing)))

-- or: processors have type : Stream m a -> Stream m b
-- what is a processor then?
-- we lose the characterisation as something that consumes a finite amount, then emits, then loops


-- and: readers have type :   Stream m a -> m b
-- and everything is just done on streams

data PRState pS b rS
  = Together      pS rS
  | Alone         rS
  | SinkWaiting   pS (Maybe b -> rS)

-}

foldl :: Monad m => (b -> a -> b) -> b -> Reader a m b
foldl f b = do
  a <- head
  case a of
    Nothing -> return b
    Just a  -> foldl f (f b a)

foldl' :: Monad m => (b -> a -> b) -> b -> Reader a m b
foldl' f !b = do
  a <- head
  case a of
    Nothing -> return b
    Just a  -> foldl' f (f b a)

-- unfold f1 s1 |>| consumeBy f2 s2
-- this should be compressible to a simple loop
-- I think the inliner will already do this?

{------------------------------------------------------------------------------}
printAll :: (Show a, MonadIO m) => Reader a m ()
printAll = mapM_ (liftIO . print)
{-# INLINE printAll #-}

mapM_ :: Monad m => (a -> m ()) -> Reader a m ()
mapM_ action = consumeBy f ()
    where f () Nothing  = return (Right ())
          f () (Just a) = action a >> return (Left ())
{-# INLINE mapM_ #-}

{------------------------------------------------------------------------------}
newtype Processor a m b
    = Processor { processorReader :: Reader a m (ProcessorStep a m b) }

data ProcessorStep a m b
    = ProcessorEmit b (Processor a m b)
    | ProcessorEnd

processorEmit :: Monad m => b -> Processor a m b -> Reader a m (ProcessorStep a m b)
processorEmit b processor =
    return (ProcessorEmit b processor)

processorEnd :: Monad m => Reader a m (ProcessorStep a m b)
processorEnd =
    return ProcessorEnd

ofStream :: Monad m => Stream m b -> Processor a m b
ofStream stream =
    Processor $ do
      streamStep <- lift $ forceStream stream
      case streamStep of
        StreamElem b stream' -> processorEmit b (ofStream stream')
        StreamEnd            -> processorEnd

map :: Monad m => (a -> b) -> Processor a m b
map f = concatMapAccum h (const []) ()
    where h () a = ((), [f a])
{-# NOINLINE map #-} -- FIXME: just for now

filter :: Monad m => (a -> Maybe b) -> Processor a m b
filter f = concatMapAccum h (const []) ()
    where h () a = case f a of
                     Nothing -> ((),[])
                     Just b  -> ((),[b])

mapM :: Monad m => (a -> m b) -> Processor a m b
mapM f = concatMapAccumM h (const (return [])) ()
    where h () a = do v <- f a
                      return ((),[v])

concatMap :: Monad m => (a -> [b]) -> Processor a m b
concatMap f = concatMapAccum h (const []) ()
    where h () a = ((), f a)

-- I believe that every processor can be written in this way
iterate :: Monad m =>
           (s -> Reader a m (Maybe (s,b)))
        -> s
        -> Processor a m b
iterate h s = Processor $ f <$> h s
    where f Nothing      = ProcessorEnd
          f (Just (s,b)) = ProcessorEmit b (iterate h s)

-- | FIXME: this runs the risk of being non-productive
concatMapAccum :: Monad m =>
                  (s -> a -> (s, [b]))
               -> (s -> [b])
               -> s
               -> Processor a m b
concatMapAccum step eos s =
    Processor $ do
      a <- head
      case a of
        Nothing -> processorReader $ loop (eos s) (Processor processorEnd)
        Just a  -> let (s',bs) = step s a
                   in processorReader $ loop bs (concatMapAccum step eos s')
    where
      loop []     k = k
      loop (b:bs) k = Processor $ processorEmit b (loop bs k)
{-# NOINLINE concatMapAccum #-}

--    concatMapAccumM (\s a -> return (f s a)) (\s -> return (eos s)) s

-- | FIXME: this runs the risk of being non-productive.
concatMapAccumM :: Monad m =>
                   (s -> a -> m (s, [b])) -- ^ Monadic action to run on each input
                -> (s -> m [b])           -- ^ Monadic action to run at the end of the input
                -> s                      -- ^ The initial state
                -> Processor a m b        -- ^ Processor that iterates the step action
concatMapAccumM step eos s =
    Processor $ do
      a <- head
      case a of
        Nothing -> do bs <- lift (eos s)
                      processorReader $ loop bs (Processor processorEnd)
        Just a  -> do (s', bs) <- lift (step s a)
                      processorReader $ loop bs (concatMapAccumM step eos s')
    where
      loop []     k = k
      loop (b:bs) k = Processor $ processorEmit b (loop bs k)

{------------------------------------------------------------------------------}
-- | Compose a stream with a reader, producing a single monadic action
-- 
-- Does the reader before doing the stream
-- Other options:
-- - Make the stream dictate things
-- - Return left-over streams/readers
(|>|) :: Monad m => Stream m a -> Reader a m b -> m b
stream |>| reader = do
  readerStep <- forceReader reader
  case readerStep of
    Read k ->
        do streamStep <- forceStream stream
           case streamStep of
             StreamElem a stream' -> stream' |>| k (Just a)
             StreamEnd            -> nil     |>| k Nothing
    ReadEnd b ->
        return b
{-# NOINLINE (|>|) #-}


-- | Pre-compose a processor onto a reader. The resulting process is
-- driven by the original reader.
(>>|) :: Monad m => Processor a m b -> Reader b m c -> Reader a m c
processor >>| reader =
    Reader $ do
      readerStep <- forceReader reader
      case readerStep of
        Read k ->
            do processorStep <- forceReader $ processorReader processor
               case processorStep of
                 Read k' ->
                     return (Read $ \input -> Processor (k' input) >>| Reader (return (Read k)))
                 ReadEnd ProcessorEnd ->
                     forceReader (ofStream nil >>| k Nothing)
                 ReadEnd (ProcessorEmit b processor') ->
                     forceReader (processor' >>| k (Just b))
        ReadEnd c ->
            return (ReadEnd c)
{-# NOINLINE (>>|) #-}

-- | Demand-driven composition of processors.
(>>>) :: Monad m => Processor a m b -> Processor b m c -> Processor a m c
processor1 >>> processor2 =
    Processor $ Reader $ do
      readerStep2 <- forceReader $ processorReader processor2
      case readerStep2 of
        Read k2 ->
            do readerStep1 <- forceReader $ processorReader processor1
               case readerStep1 of
                 Read k1 ->
                     return (Read $ \input -> processorReader $ Processor (k1 input) >>> Processor (Reader (return (Read k2))))
                 ReadEnd (ProcessorEmit b processor1') ->
                     forceReader $ processorReader $ processor1' >>> Processor (k2 (Just b))
                 ReadEnd ProcessorEnd ->
                     forceReader $ processorReader $ ofStream nil >>> Processor (k2 Nothing)
        ReadEnd (ProcessorEmit c processor2') ->
            return (ReadEnd (ProcessorEmit c (processor1 >>> processor2')))
        ReadEnd ProcessorEnd ->
            return (ReadEnd ProcessorEnd)
{-# NOINLINE (>>>) #-}

-- | Post-compose a processor on to a stream. The resulting process is
-- driven by the processor.
(|>>) :: Monad m => Stream m a -> Processor a m b -> Stream m b
stream |>> processor =
  Stream $ do
    readerStep <- forceReader $ processorReader processor
    case readerStep of
      Read k ->
          do streamStep <- forceStream stream
             case streamStep of
               StreamElem a stream' ->
                   forceStream (stream' |>> Processor (k (Just a)))
               StreamEnd ->
                   forceStream (nil     |>> Processor (k Nothing))
      ReadEnd (ProcessorEmit b processor') ->
          return (StreamElem b (stream |>> processor'))
      ReadEnd ProcessorEnd ->
          return StreamEnd
{-# NOINLINE (|>>) #-}
