module HW0.T6 where

import Data.Char (isSpace)

import HW0.T1

-- (_, _)
--   ghci (seq + sprint) says that it is (Left _, Left _)...
--   either I mistaken or ghc optimized something
--   tuple constructor (,) should be "the outermost data constructor"
a = distrib (Left ("AB" ++ "CD" ++ "EF"))

-- _:_
b = map isSpace "Hello, World"

-- 'Y':_
c = if 1 > 0 || error "X" then "Y" else "Z"

-- or do we need to inline? task is unclear.........

-- distrib (Left a) = (Left a, Left a)
a_whnf = (Left $ "AB" ++ "CD" ++ "EF", Left $ "AB" ++ "CD" ++ "EF")

b_whnf = (isSpace 'H'):(map isSpace "ello, World")

-- outermost data constructor is `:`, unsure about evaluation of constant fields (Char and String)
c_whnf = "Y"
