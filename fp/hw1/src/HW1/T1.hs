module HW1.T1
  ( Day (..)
  ,  nextDay
  ,  afterDays
  , isWeekend
  , daysToParty
  ) where

import Numeric.Natural

data Day = Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday deriving (Show)

-- | Returns the day that follows the day of the week given as input.
nextDay :: Day -> Day
-- nextDay = toEnum . (\x -> (x + 1) `mod` 7) . fromEnum
-- template haskell involves ints as well, which is forbidden, so vim macroses
nextDay Monday    = Tuesday
nextDay Tuesday   = Wednesday
nextDay Wednesday = Thursday
nextDay Thursday  = Friday
nextDay Friday    = Saturday
nextDay Saturday  = Sunday
nextDay Sunday    = Monday

-- | Returns the day of the week after a given number of days has passed.
afterDays :: Natural -> Day -> Day
afterDays n d = iterate nextDay d !! ((fromIntegral $ n `mod` 7) :: Int)

-- | Checks if the day is on the weekend.
isWeekend :: Day -> Bool
isWeekend Saturday = True
isWeekend Sunday   = True
isWeekend _        = False

-- | Computes the number of days until the next Friday.
daysToParty :: Day -> Natural
daysToParty Monday    = 4
daysToParty Tuesday   = 3
daysToParty Wednesday = 2
daysToParty Thursday  = 1
daysToParty Friday    = 0
daysToParty Saturday  = 6
daysToParty Sunday    = 5

