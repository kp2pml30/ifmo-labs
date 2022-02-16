module HW2.T3 where

import Data.Semigroup (Semigroup, (<>))
import Prelude ()

import HW2.T1

joinOption    :: Option (Option a) -> Option a
joinOption None     = None
joinOption (Some x) = x

joinExcept    :: Except e (Except e a) -> Except e a
joinExcept (Error a)   = Error a
joinExcept (Success a) = a

-- | merges annotations as inner <> outer
joinAnnotated :: Semigroup e => Annotated e (Annotated e a) -> Annotated e a
joinAnnotated ((a :# e1) :# e2) = a :# (e2 <> e1)

-- | list concat
joinList      :: List (List a) -> List a
joinList Nil = Nil
joinList (cur :. rest) = concat cur
  where
    concat Nil      = joinList rest
    concat (h :. t) = h :. concat t

-- | applies argument twise
-- | i -> (i -> a) === i -> i -> a
joinFun       :: Fun i (Fun i a) -> Fun i a
joinFun (F f) = F \i -> let F g = f i in g i
