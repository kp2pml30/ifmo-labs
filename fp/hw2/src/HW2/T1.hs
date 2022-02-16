module HW2.T1 where

import Prelude ()

data Option a = None | Some a

data Pair a = P a a

data Quad a = Q a a a a

data Annotated e a = a :# e
infix 0 :#

data Except e a = Error e | Success a

data Prioritised a = Low a | Medium a | High a

data Stream a = a :> Stream a
infixr 5 :>

data List a = Nil | a :. List a
infixr 5 :.

newtype Fun i a = F (i -> a)

data Tree a = Leaf | Branch (Tree a) a (Tree a)

mapOption      :: (a -> b) -> Option a -> Option b
mapOption _ None     = None
mapOption f (Some a) = Some (f a)

mapPair        :: (a -> b) -> Pair a -> Pair b
mapPair f (P a b) = P (f a) (f b)

mapQuad        :: (a -> b) -> Quad a -> Quad b
mapQuad f (Q a b c d) = Q (f a) (f b) (f c) (f d)

mapAnnotated   :: (a -> b) -> Annotated e a -> Annotated e b
mapAnnotated f (a :# e) = f a :# e

mapExcept      :: (a -> b) -> Except e a -> Except e b
mapExcept f (Success a) = Success (f a)
mapExcept f (Error a)   = Error a

mapPrioritised :: (a -> b) -> Prioritised a -> Prioritised b
mapPrioritised f (Low a)    = Low (f a)
mapPrioritised f (Medium a) = Medium (f a)
mapPrioritised f (High a)   = High (f a)

mapStream      :: (a -> b) -> (Stream a -> Stream b)
mapStream f (a :> b) = f a :> mapStream f b

mapList        :: (a -> b) -> (List a -> List b)
mapList f Nil      = Nil
mapList f (h :. t) = f h :. mapList f t

mapFun         :: (a -> b) -> (Fun i a -> Fun i b)
mapFun f (F b) = F (\x -> f (b x))

mapTree        :: (a -> b) -> (Tree a -> Tree b)
mapTree f Leaf           = Leaf
mapTree f (Branch l x r) = Branch (f `mapTree` l) (f x) (f `mapTree` r)
