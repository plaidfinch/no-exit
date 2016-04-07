-- Modified from code available in Gabriel Gonzalez's Control.Foldl
-- There is a *lot* more in the actual library! Check it out:
-- <https://hackage.haskell.org/package/foldl>

{-# LANGUAGE GADTSyntax, ExistentialQuantification, ScopedTypeVariables #-}

module Foldl where

import Control.Applicative
import Data.List ( foldl' )
import Debug.Trace

-- We're going to re-implement these in this module...
import Prelude hiding
  (head, last, null, length, and, or, all, any, sum,
   product, maximum, minimum, elem, notElem, reverse)

-------------------------------------------
-- Reifying folds as an existential type --
-------------------------------------------

data Fold a b where
  Fold :: (x -> a -> x)  -- step
       -> x              -- state
       -> (x -> b)       -- done
       -> Fold a b

data Pair a b where
  Pair :: !a -> !b -> Pair a b  -- a strict 2-tuple

instance Functor (Fold a) where
  fmap f (Fold step state      done) =
          Fold step state (f . done)

instance Applicative (Fold a) where
  pure b = Fold (\() _ -> ())  -- step returns () always
                ()             -- we have no interesting state
                (\() -> b)     -- when we're done, return b

  Fold stepL stateL doneL <*>
    Fold stepR stateR doneR =
      Fold step state done
    where
      step (Pair xL xR) a =
        Pair (stepL xL a)         -- step applies the individual step functions to...
             (stepR xR a)         -- ...the corresponding piece of the paired states
      done (Pair xL xR) =         -- when done, apply (done xL :: a -> b)...
        (doneL xL) (doneR xR)     -- ...to (doneR xR :: a)
      state = Pair stateL stateR  -- our state is a pair of the original states

-- Apply a strict left 'Fold' to a list
-- We do this by using 'foldr' to build a *function* which acts as
-- a *left* fold over as.
fold :: forall a b. Fold a b -> [a] -> b
fold (Fold step state done) =
  done . foldl' step state

------------------------------------
-- A bunch of useful atomic folds --
------------------------------------

-- Instrument a list to see how it gets evaluated
instrument :: [a] -> [a]
instrument =
  foldr cons nil
  where
    cons a as = trace ":"  (a : as)
    nil       = trace "[]" []

null :: Fold a Bool
null = Fold (\_ _ -> False) True id

length :: Num b => Fold a b
length = Fold (\n _ -> n + 1) 0 id

and :: Fold Bool Bool
and = Fold (&&) True id

or :: Fold Bool Bool
or = Fold (||) False id

all :: (a -> Bool) -> Fold a Bool
all predicate = Fold (\x a -> x && predicate a) True id

any :: (a -> Bool) -> Fold a Bool
any predicate = Fold (\x a -> x || predicate a) False id

sum :: Num a => Fold a a
sum = Fold (+) 0 id

product :: Num a => Fold a a
product = Fold (*) 1 id

elem :: Eq a => a -> Fold a Bool
elem a = any (a ==)

notElem :: Eq a => a -> Fold a Bool
notElem a = all (a /=)

reverse :: Fold a [a]
reverse = Fold (\xs x -> x : xs) [] id

_Fold1 :: (a -> a -> a) -> Fold a (Maybe a)
_Fold1 step = Fold step_ Nothing id
  where
    step_ mx a = Just (case mx of
        Nothing -> a
        Just x -> step x a)

maximum :: Ord a => Fold a (Maybe a)
maximum = _Fold1 max

minimum :: Ord a => Fold a (Maybe a)
minimum = _Fold1 min

head :: Fold a (Maybe a)
head = _Fold1 const

last :: Fold a (Maybe a)
last = _Fold1 (flip const)

-- Numeric instances

instance Num b => Num (Fold a b) where
    fromInteger = pure . fromInteger
    negate      = fmap negate
    abs         = fmap abs
    signum      = fmap signum
    (+)         = liftA2 (+)
    (*)         = liftA2 (*)
    (-)         = liftA2 (-)

instance Fractional b => Fractional (Fold a b) where
    fromRational = pure . fromRational
    recip        = fmap recip
    (/)          = liftA2 (/)

instance Floating b => Floating (Fold a b) where
    pi      = pure pi
    exp     = fmap exp
    sqrt    = fmap sqrt
    log     = fmap log
    sin     = fmap sin
    tan     = fmap tan
    cos     = fmap cos
    asin    = fmap sin
    atan    = fmap atan
    acos    = fmap acos
    sinh    = fmap sinh
    tanh    = fmap tanh
    cosh    = fmap cosh
    asinh   = fmap asinh
    atanh   = fmap atanh
    acosh   = fmap acosh
    (**)    = liftA2 (**)
    logBase = liftA2 logBase
