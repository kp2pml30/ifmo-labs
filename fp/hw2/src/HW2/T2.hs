module HW2.T2 where

import Data.Monoid (Monoid, mempty)
import Data.Semigroup (Semigroup, (<>))
import Prelude ()

import HW2.T1

distOption      :: (Option a, Option b) -> Option (a, b)
distOption (Some a, Some b) = Some (a, b)
distOption _                = None

-- | merges pairs in form result[i] = (a[i], b[i])
distPair        :: (Pair a, Pair b) -> Pair (a, b)
distPair (P a x, P b y) = P (a, b) (x, y)

-- | merges quads in form result[i] = (a[i], b[i])
distQuad        :: (Quad a, Quad b) -> Quad (a, b)
distQuad (Q a b c d, Q x y z w) = Q (a, x) (b, y) (c, z) (d, w)

distAnnotated   :: Semigroup e => (Annotated e a, Annotated e b) -> Annotated e (a, b)
distAnnotated (a :# e1, b :# e2) =  (a, b) :# (e1 <> e2)

-- | prioritises first error
distExcept      :: (Except e a, Except e b) -> Except e (a, b)
distExcept (Success a, Success b) = Success (a, b)
distExcept (Error l, _)           = Error l
distExcept (_, Error r)           = Error r

-- record syntax by hand
unwrapPrioritised (High a)   = a
unwrapPrioritised (Medium a) = a
unwrapPrioritised (Low a)    = a

-- | create pair with highest priority out of 2
distPrioritised :: (Prioritised a, Prioritised b) -> Prioritised (a, b)
distPrioritised (High a, b)    = High (a, unwrapPrioritised b)
distPrioritised (a, High b)    = High (unwrapPrioritised a, b)
distPrioritised (Medium a, b)  = Medium (a, unwrapPrioritised b)
distPrioritised (a, Medium b)  = Medium (unwrapPrioritised a, b)
distPrioritised (Low a, Low b) = Low (a, b)

-- | merges streams in form result[i] = (a[i], b[i])
distStream      :: (Stream a, Stream b) -> Stream (a, b)
distStream (a :> x, b :> y) = (a, b) :> distStream (x, y)

-- | a >>= \ai -> [(ai, bi) | bi <- b]
distList        :: (List a, List b) -> List (a, b)
distList (Nil, b) = Nil
-- | handles (Nil, Nil) -> Nil to prevent infinite recursion
distList (a, Nil) = Nil
distList (cur :. rest, b) = prepend b
  where
    prepend Nil      = distList (rest, b)
    prepend (h :. t) = (cur, h) :. prepend t

-- | composition
distFun         :: (Fun i a, Fun i b) -> Fun i (a, b)
distFun (F f, F g) = F \i -> (f i, g i)

wrapOption      :: a -> Option a
wrapOption = Some

wrapPair        :: a -> Pair a
wrapPair a = P a a  -- join P

wrapQuad        :: a -> Quad a
wrapQuad a = Q a a a a

-- | create mempty annotation
wrapAnnotated   :: Monoid e => a -> Annotated e a
wrapAnnotated = (:# mempty)

-- | create success
wrapExcept      :: a -> Except e a
wrapExcept = Success

-- | wraps into Low priority
wrapPrioritised :: a -> Prioritised a
wrapPrioritised = Low

-- | repeat a
wrapStream      :: a -> Stream a
-- wrapStream = fix ..  (:>)
wrapStream a = a :> wrapStream a

-- | singleton list creator
wrapList        :: a -> List a
wrapList = (:. Nil)

-- | create const function (not ranked)
wrapFun         :: a -> Fun i a
-- wrapFun = F . const
wrapFun a = F \_ -> a
