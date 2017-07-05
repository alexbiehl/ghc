{-# LANGUAGE Trustworthy       #-}
{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE CPP               #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MagicHash         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnboxedTuples     #-}

module GHC.Event.PSQ
    (
    -- * Binding Type
      Key
    , Prio

    -- * Priority Search Queue Type
    , PSQ

    -- * Query
    , size
    , null
    , lookup

    -- * Construction
    , empty
    , singleton

    -- * Insertion
    , insert

    -- * Delete/Update
    , delete
    , adjust

    -- * Min
    , findMin
    , deleteMin
    , minView
    , atMost
    ) where

import GHC.Base hiding (Nat, empty)
import GHC.Word (Word64)
import GHC.Num (Num(..))
import GHC.Real (fromIntegral)
import GHC.Types (Int)

#include "MachDeps.h"

-- TODO (SM): get rid of bang patterns

{-
-- Use macros to define strictness of functions.
-- STRICT_x_OF_y denotes an y-ary function strict in the x-th parameter.
-- We do not use BangPatterns, because they are not in any standard and we
-- want the compilers to be compiled by as many compilers as possible.
#define STRICT_1_OF_2(fn) fn arg _ | arg `seq` False = undefined
-}


------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

type Prio = Word64

type Nat = Word

type Key = Int

-- | We store masks as the index of the bit that determines the branching.
type Mask = Int

type PSQ a = IntPSQ Prio a

-- | A priority search queue with @Int@ keys and priorities of type @p@ and
-- values of type @v@. It is strict in keys, priorities and values.
data IntPSQ p v
    = Bin {-# UNPACK #-} !Key !p !v {-# UNPACK #-} !Mask !(IntPSQ p v) !(IntPSQ p v)
    | Tip {-# UNPACK #-} !Key !p !v
    | Nil

-- bit twiddling
----------------

(.&.) :: Nat -> Nat -> Nat
(.&.) (W# w1) (W# w2) = W# (w1 `and#` w2)
{-# INLINE (.&.) #-}

xor :: Nat -> Nat -> Nat
xor (W# w1) (W# w2) = W# (w1 `xor#` w2)
{-# INLINE xor #-}

complement :: Nat -> Nat
complement (W# w) = W# (w `xor#` mb)
  where
#if WORD_SIZE_IN_BITS == 32
    mb = 0xFFFFFFFF##
#elif WORD_SIZE_IN_BITS == 64
    mb = 0xFFFFFFFFFFFFFFFF##
#else
#error Unhandled value for WORD_SIZE_IN_BITS
#endif
{-# INLINE complement #-}

{-# INLINE natFromInt #-}
natFromInt :: Key -> Nat
natFromInt = fromIntegral

{-# INLINE intFromNat #-}
intFromNat :: Nat -> Key
intFromNat = fromIntegral

{-# INLINE zero #-}
zero :: Key -> Mask -> Bool
zero i m
  = (natFromInt i) .&. (natFromInt m) == 0

{-# INLINE nomatch #-}
nomatch :: Key -> Key -> Mask -> Bool
nomatch k1 k2 m =
    natFromInt k1 .&. m' /= natFromInt k2 .&. m'
  where
    m' = maskW (natFromInt m)

{-# INLINE maskW #-}
maskW :: Nat -> Nat
maskW m = complement (m-1) `xor` m

{-# INLINE branchMask #-}
branchMask :: Key -> Key -> Mask
branchMask k1 k2 =
    intFromNat (highestBitMask (natFromInt k1 `xor` natFromInt k2))

highestBitMask :: Nat -> Nat
highestBitMask (W# x) =
  W# (uncheckedShiftL# 1## (word2Int# (WORD_SIZE_IN_BITS## `minusWord#` 1## `minusWord#` clz# x)))
{-# INLINE highestBitMask #-}

------------------------------------------------------------------------------
-- Query
------------------------------------------------------------------------------

-- | /O(1)/ True if the queue is empty.
null :: IntPSQ p v -> Bool
null Nil = True
null _   = False

-- | /O(n)/ The number of elements stored in the queue.
size :: IntPSQ p v -> Int
size Nil               = 0
size (Tip _ _ _)       = 1
size (Bin _ _ _ _ l r) = 1 + size l + size r
-- TODO (SM): benchmark this against a tail-recursive variant

-- | /O(min(n,W))/ The priority and value of a given key, or 'Nothing' if the
-- key is not bound.
lookup :: Int -> IntPSQ p v -> Maybe (p, v)
lookup k = go
  where
    go t = case t of
        Nil                -> Nothing

        Tip k' p' x'
          | k == k'        -> Just (p', x')
          | otherwise      -> Nothing

        Bin k' p' x' m l r
          | nomatch k k' m -> Nothing
          | k == k'        -> Just (p', x')
          | zero k m       -> go l
          | otherwise      -> go r

-- | /O(1)/ The element with the lowest priority.
findMin :: Ord p => IntPSQ p v -> Maybe (Int, p, v)
findMin t = case t of
    Nil             -> Nothing
    Tip k p x       -> Just (k, p, x)
    Bin k p x _ _ _ -> Just (k, p, x)


------------------------------------------------------------------------------
--- Construction
------------------------------------------------------------------------------

-- | /O(1)/ The empty queue.
empty :: IntPSQ p v
empty = Nil

-- | /O(1)/ Build a queue with one element.
singleton :: Ord p => Int -> p -> v -> IntPSQ p v
singleton = Tip


------------------------------------------------------------------------------
-- Insertion
------------------------------------------------------------------------------

-- | /O(min(n,W))/ Insert a new key, priority and value into the queue. If the key
-- is already present in the queue, the associated priority and value are
-- replaced with the supplied priority and value.
insert :: Ord p => Int -> p -> v -> IntPSQ p v -> IntPSQ p v
insert k p x t0 = unsafeInsertNew k p x (delete k t0)

-- | Internal function to insert a key that is *not* present in the priority
-- queue.
{-# INLINABLE unsafeInsertNew #-}
unsafeInsertNew :: Ord p => Key -> p -> v -> IntPSQ p v -> IntPSQ p v
unsafeInsertNew k p x = go
  where
    go t = case t of
      Nil       -> Tip k p x

      Tip k' p' x'
        | (p, k) < (p', k') -> link k  p  x  k' t           Nil
        | otherwise         -> link k' p' x' k  (Tip k p x) Nil

      Bin k' p' x' m l r
        | nomatch k k' m ->
            if (p, k) < (p', k')
              then link k  p  x  k' t           Nil
              else link k' p' x' k  (Tip k p x) (merge m l r)

        | otherwise ->
            if (p, k) < (p', k')
              then
                if zero k' m
                  then Bin k  p  x  m (unsafeInsertNew k' p' x' l) r
                  else Bin k  p  x  m l (unsafeInsertNew k' p' x' r)
              else
                if zero k m
                  then Bin k' p' x' m (unsafeInsertNew k  p  x  l) r
                  else Bin k' p' x' m l (unsafeInsertNew k  p  x  r)

-- | Link
link :: Key -> p -> v -> Key -> IntPSQ p v -> IntPSQ p v -> IntPSQ p v
link k p x k' k't otherTree
  | zero m k' = Bin k p x m k't       otherTree
  | otherwise = Bin k p x m otherTree k't
  where
    m = branchMask k k'


------------------------------------------------------------------------------
-- Delete/Alter
------------------------------------------------------------------------------

-- | /O(min(n,W))/ Delete a key and its priority and value from the queue. When
-- the key is not a member of the queue, the original queue is returned.
{-# INLINABLE delete #-}
delete :: Ord p => Int -> IntPSQ p v -> IntPSQ p v
delete k = go
  where
    go t = case t of
        Nil           -> Nil

        Tip k' _ _
          | k == k'   -> Nil
          | otherwise -> t

        Bin k' p' x' m l r
          | nomatch k k' m -> t
          | k == k'        -> merge m l r
          | zero k m       -> binShrinkL k' p' x' m (go l) r
          | otherwise      -> binShrinkR k' p' x' m l      (go r)

-- | /O(min(n,W))/ Delete the binding with the least priority, and return the
-- rest of the queue stripped of that binding. In case the queue is empty, the
-- empty queue is returned again.
{-# INLINE deleteMin #-}
deleteMin :: Ord p => IntPSQ p v -> IntPSQ p v
deleteMin t = case minView t of
    Nothing            -> t
    Just (_, _, _, t') -> t'


adjust
    :: (Prio -> Prio)
    -> Key
    -> PSQ a
    -> PSQ a
adjust f k q = case alter g k q of (_, q') -> q'
  where g (Just (p, v)) = ((), Just ((f p), v))
        g Nothing       = ((), Nothing)

{-# INLINE adjust #-}

-- | /O(min(n,W))/ The expression @alter f k queue@ alters the value @x@ at @k@,
-- or absence thereof. 'alter' can be used to insert, delete, or update a value
-- in a queue. It also allows you to calculate an additional value @b@.
{-# INLINE alter #-}
alter
    :: Ord p
    => (Maybe (p, v) -> (b, Maybe (p, v)))
    -> Key
    -> IntPSQ p v
    -> (b, IntPSQ p v)
alter f = \k t0 ->
    let (t, mbX) = case deleteView k t0 of
                            Nothing          -> (t0, Nothing)
                            Just (p, v, t0') -> (t0', Just (p, v))
    in case f mbX of
          (b, mbX') ->
            (b, maybe t (\(p, v) -> unsafeInsertNew k p v t) mbX')
    where
        maybe _ g (Just x)  = g x
        maybe def _ Nothing = def

-- | Smart constructor for a 'Bin' node whose left subtree could have become
-- 'Nil'.
{-# INLINE binShrinkL #-}
binShrinkL :: Key -> p -> v -> Mask -> IntPSQ p v -> IntPSQ p v -> IntPSQ p v
binShrinkL k p x m Nil r = case r of Nil -> Tip k p x; _ -> Bin k p x m Nil r
binShrinkL k p x m l   r = Bin k p x m l r

-- | Smart constructor for a 'Bin' node whose right subtree could have become
-- 'Nil'.
{-# INLINE binShrinkR #-}
binShrinkR :: Key -> p -> v -> Mask -> IntPSQ p v -> IntPSQ p v -> IntPSQ p v
binShrinkR k p x m l Nil = case l of Nil -> Tip k p x; _ -> Bin k p x m l Nil
binShrinkR k p x m l r   = Bin k p x m l r

------------------------------------------------------------------------------
-- Views
------------------------------------------------------------------------------

-- | /O(min(n,W))/ Delete a key and its priority and value from the queue. If
-- the key was present, the associated priority and value are returned in
-- addition to the updated queue.
{-# INLINABLE deleteView #-}
deleteView :: Ord p => Key -> IntPSQ p v -> Maybe (p, v, IntPSQ p v)
deleteView k t0 =
    case delFrom t0 of
      (# _, Nothing     #) -> Nothing
      (# t, Just (p, x) #) -> Just (p, x, t)
  where
    delFrom t = case t of
      Nil -> (# Nil, Nothing #)

      Tip k' p' x'
        | k == k'   -> (# Nil, Just (p', x') #)
        | otherwise -> (# t,   Nothing       #)

      Bin k' p' x' m l r
        | nomatch k k' m -> (# t, Nothing #)
        | k == k'   -> let t' = merge m l r
                       in  t' `seq` (# t', Just (p', x') #)

        | zero k m  -> case delFrom l of
                         (# l', mbPX #) -> let t' = binShrinkL k' p' x' m l' r
                                           in  t' `seq` (# t', mbPX #)

        | otherwise -> case delFrom r of
                         (# r', mbPX #) -> let t' = binShrinkR k' p' x' m l  r'
                                           in  t' `seq` (# t', mbPX #)

-- | /O(min(n,W))/ Retrieve the binding with the least priority, and the
-- rest of the queue stripped of that binding.
{-# INLINE minView #-}
minView :: Ord p => IntPSQ p v -> Maybe (Key, p, v, IntPSQ p v)
minView t = case t of
    Nil             -> Nothing
    Tip k p x       -> Just (k, p, x, Nil)
    Bin k p x m l r -> Just (k, p, x, merge m l r)

-- | Return a list of elements ordered by key whose priorities are at most @pt@,
-- and the rest of the queue stripped of these elements.  The returned list of
-- elements can be in any order: no guarantees there.
{-# INLINABLE atMost #-}
atMost :: Ord p => p -> IntPSQ p v -> ([(Key, p, v)], IntPSQ p v)
atMost pt t0 = go [] t0
  where
    go acc t = case t of
        Nil             -> (acc, t)
        Tip k p x
            | p > pt    -> (acc, t)
            | otherwise -> ((k, p, x) : acc, Nil)

        Bin k p x m l r
            | p > pt    -> (acc, t)
            | otherwise ->
                let (acc',  l') = go acc  l
                    (acc'', r') = go acc' r
                in  ((k, p, x) : acc'', merge m l' r')


------------------------------------------------------------------------------
-- Traversal
------------------------------------------------------------------------------

-- | Internal function that merges two *disjoint* 'IntPSQ's that share the
-- same prefix mask.
{-# INLINABLE merge #-}
merge :: Ord p => Mask -> IntPSQ p v -> IntPSQ p v -> IntPSQ p v
merge m l r = case l of
    Nil -> r

    Tip lk lp lx ->
      case r of
        Nil                     -> l
        Tip rk rp rx
          | (lp, lk) < (rp, rk) -> Bin lk lp lx m Nil r
          | otherwise           -> Bin rk rp rx m l   Nil
        Bin rk rp rx rm rl rr
          | (lp, lk) < (rp, rk) -> Bin lk lp lx m Nil r
          | otherwise           -> Bin rk rp rx m l   (merge rm rl rr)

    Bin lk lp lx lm ll lr ->
      case r of
        Nil                     -> l
        Tip rk rp rx
          | (lp, lk) < (rp, rk) -> Bin lk lp lx m (merge lm ll lr) r
          | otherwise           -> Bin rk rp rx m l                Nil
        Bin rk rp rx rm rl rr
          | (lp, lk) < (rp, rk) -> Bin lk lp lx m (merge lm ll lr) r
          | otherwise           -> Bin rk rp rx m l                (merge rm rl rr)
