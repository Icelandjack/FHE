module Auxiliary (nint, remainder) where

import Test.QuickCheck

-- Round to Nearest INT
nint ∷ (Integral b, RealFrac a) ⇒ a → b
nint z
  | f >= 0.5  = n + 1
  | f <= -0.5 = n - 1
  | otherwise = n 
  where
    (n, f) = properFraction z

-- Quotient
quotient ∷ Integer → Integer → Integer
quotient(0) z = error "Exception: divide by zero"
quotient(p) z = nint (fromIntegral z / fromIntegral p) 

-- Remainder
remainder ∷ Integer → Integer → Integer
remainder(p) z = z - (quotient(p) z * p)

-- 'nint z' is unique integer in the half-open interval
--     (z − 1/2 , z + 1/2]
prop_nint ∷ Double → Bool
prop_nint z = z-1/2 < rounded && rounded <= z+1/2 where
  rounded = fromInteger (nint z)

--     ASK MICHAL
-- Testing extrema in QuickCheck: 
-- * minBound, maxBound (abs (minBound ∷ Int) >= 0)
-- * 0.5 ranges 
--   (prop_nint succeeds with s/nint/round/ but it should fail for any even number + 1/2)

-- 'ceiling z' is unique integer in the half-open interval
--     [z, z+1)
prop_up ∷ Double → Bool
prop_up z = z <= rounded && rounded < z+1 where
  rounded = fromInteger (ceiling z)

-- 'floor z' is unique integer in the half-open interval
--     (z-1, z]
prop_down ∷ Double → Bool
prop_down z = z-1 < rounded && rounded <= z where
  rounded = fromInteger (floor z)
  
-- remainder(p) z ∈ (-p/2, p/2]
prop_remainder ∷ Positive Integer → Integer → Bool
prop_remainder(Positive p) z =
  -- abs z > 4 ==> 
  -- abs p > 4 ==> 
  u == 0.0 || (-fromInteger p/2 <= u && u <= fromInteger p/2)
  where u = fromInteger (remainder(p) z)

-- prop_r(Positive p) z = (abs z) > 2 && (abs p) > 2 ==> let
--   u = remainder(p) z
--   in -p`div`2 < u && u <= p`div`2

tests = do
  quickCheck prop_nint
  quickCheck prop_down
  quickCheck prop_up
  