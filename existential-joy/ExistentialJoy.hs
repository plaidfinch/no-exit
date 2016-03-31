
{-# LANGUAGE GADTs, RecordWildCards, NamedFieldPuns, TemplateHaskell #-}

module ExistentialJoy where

import Data.List
import Data.Function
import Data.Maybe

import Test.QuickCheck

-- GADTs

data Pair a where
  Pair :: a -> a -> Pair a

-- But what if I make a typo?

data Pear a where
  Pear :: a -> b -> Pear a

--pare (Pear a b) = (a, b)  -- doesn't compile

halfPare :: Pear a -> a
halfPare (Pear a _) = a  -- works just fine

-- Curry Howard, existential types (FILL IN)

-- Some syntactic extensions

data ThreeInts where
  ThreeInts :: { first  :: Int
               , second :: Int
               , third  :: Int } -> ThreeInts

makeThirdSum :: ThreeInts -> ThreeInts

-- No special syntax sugar: very verbose!
--makeThirdSum ThreeInts{first = first, second = second, third = third} =
--   ThreeInts { first  = first
--             , second = second
--             , third  = first + second + third }

-- With NamedFieldPuns:
--makeThirdSum ThreeInts{first, second, third} =
--   ThreeInts { first
--             , second
--             , third = first + second + third }

-- With NamedFieldPuns and RecordWildCards:
makeThirdSum ThreeInts{..} =
  ThreeInts { first
            , second
            , third = first + second + third }

-- Existential types are abstract types (FILL IN)

data Queue a where
  Queue :: { _enqueue :: a -> q -> q
           , _dequeue :: q -> Maybe (a, q)
           , _insides :: q
           } -> Queue a

slowQueue :: Queue a
slowQueue = Queue tack uncons []
  where
    tack x xs = xs ++ [x]

enqueue :: a -> Queue a -> Queue a
enqueue a Queue{..} =
  Queue { _enqueue
        , _dequeue
        , _insides = _enqueue a _insides }

dequeue :: Queue a -> Maybe (a, Queue a)
dequeue Queue{..} =
  case _dequeue _insides of
    Nothing -> Nothing
    Just (a, rest) ->
      Just (a, Queue { _enqueue
                     , _dequeue
                     , _insides = rest })

queueToList :: Queue a -> [a]
queueToList = unfoldr dequeue

enqueueAll :: Queue a -> [a] -> Queue a
enqueueAll = foldr enqueue

-- Other implementations

twoListQueue :: Queue a
twoListQueue =
  Queue { _insides = ([], [])
        , _enqueue = \a (front, back) -> (front, a : back)
        , _dequeue = \(front, back) ->
                       case (front, back) of
                         ([], []) -> Nothing
                         ([], _)  ->
                           let (a : front') = reverse back in
                           Just (a, (front', []))
                         (a : front', _) ->
                           Just (a, (front', back)) }

prop_twoListQueue_spec :: [QueueOp Int] -> Property
prop_twoListQueue_spec = compareQueues slowQueue twoListQueue

-- Chris Okasaki: "Simple and Efficient Purely Functional Queues and Deques"
-- J. Functional Programming 5(4): 583–592, October 1995
okasakiQueue :: Queue a
okasakiQueue =
  Queue { _insides = ([], [], [])
        , _enqueue = \e (fs, bs, as) ->
                       makeEq (fs, e : bs, as)
        , _dequeue = \(fs, bs, as) ->
                       case fs of
                         [] -> Nothing
                         (e : es) ->
                           Just (e, makeEq (es, bs, as)) }
  where
    -- force one step of lazy rot computation or reset if finished
    makeEq (fs, bs, (_ : as')) = (fs, bs, as')
    makeEq (fs, bs, []) =
      let fs' = rot fs bs []
      in (fs', [], fs')

    -- rot fs bs as == fs ++ reverse bs ++ as
    rot      []       []  as = as
    rot      []  (b : bs) as = b : rot [] bs as
    rot (f : fs)      []  as = f : rot fs [] as
    rot (f : fs) (b : bs) as = f : rot fs bs (b : as)

prop_okasakiQueue_spec :: [QueueOp Int] -> Property
prop_okasakiQueue_spec = compareQueues slowQueue okasakiQueue

-- Modifying the implementation of an existing queue

everyOther :: Queue a -> Queue a
everyOther Queue{..} =
  Queue { _insides = (True, _insides)
        , _enqueue = \a (b, s) ->
                    if b then (not b, _enqueue a s)
                         else (not b, s)
        , _dequeue  = \(b, s) ->
                    case _dequeue s of
                      Just (a, rest) -> Just (a, (not b, rest))
                      Nothing -> Nothing }

doublePush :: Queue a -> Queue a
doublePush Queue{..} =
  Queue { _insides
        , _dequeue
        , _enqueue = \a s -> _enqueue a (_enqueue a s) }

-- Claim: doublePush . everyOther === id
prop_doublePush_everyOther_id :: [QueueOp Int] -> Property
prop_doublePush_everyOther_id =
  compareQueues okasakiQueue (doublePush (everyOther okasakiQueue))

instance (Show a) => Show (Queue a) where
  show queue =
    "<<" ++ intercalate "," (map show $ queueToList queue) ++ ">>"

-- Testing queue implementations for correctness

data QueueOp a where
  Enqueue :: a -> QueueOp a
  Dequeue :: QueueOp a
  deriving (Eq, Ord, Show)

instance Arbitrary a => Arbitrary (QueueOp a) where
  arbitrary = do
    coin <- arbitrary
    if coin
       then return Dequeue
       else do
         a <- arbitrary
         return (Enqueue a)

runQueueOps :: Queue a -> [QueueOp a] -> ([Maybe a], Queue a)
runQueueOps queue instructions =
  case instructions of
    [] -> ([], queue)
    (op : ops) ->
      let (ma, queue')   = runOp op
          (mas, queue'') = runQueueOps queue' ops
      in (ma : mas, queue'')
  where
    runOp Dequeue =
      case dequeue queue of
        Nothing          -> (Nothing, queue)
        Just (a, queue') -> (Just a, queue')
    runOp (Enqueue a) =
      (Nothing, enqueue a queue)

compareQueues :: Eq a => Queue a -> Queue a -> [QueueOp a] -> Property
compareQueues q1 q2 ops =
  let (results1, q1') = runQueueOps q1 ops
      (results2, q2') = runQueueOps q2 ops
  in
  queueToList q1  ==  queueToList q2
                  ==>
         results1 == results2
                  &&
  queueToList q1' == queueToList q2'

return []
runTests :: IO Bool
runTests = $quickCheckAll
