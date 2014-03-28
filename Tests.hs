import Auxiliary 
import Test.QuickCheck

-- 'nintRoundHalfUp z' is unique integer in the half-open interval
--     (z − 1/2 , z + 1/2]
prop_nint ∷ Double → Bool
prop_nint z = z-1/2 < rounded && rounded <= z+1/2 where
  rounded = fromInteger (nintRoundHalfUp z)

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
  u == 0.0 || -fromInteger p/2 < u && u <= fromInteger p/2
  where
    u = fromInteger (remainder(p) z)

prop_r(Positive p) z = undefined where
  u = remainder(p) z
  
--                      (abs z) > 2 && (abs p) > 2 ==> let
  -- u = remainder(p) z
  -- in -p`div`2 < u && u <= p`div`2

-- NOTA BENE: Check for larger numbers.

-- q ∈ ℤ
-- a = nq + r
prop_quotRemConsistency a (NonZero n) = a == n*q + r where
  q = quotient n a
  r = remainder n a

-- q ∈ ℤ
-- a = nq + r
--   |r| < |n|
prop_remInRange a (NonZero n) = abs (remainder n a) < abs n 

tests = do
  quickCheck prop_nint
  quickCheck prop_down
  quickCheck prop_up
  quickCheck prop_remainder
  quickCheck prop_quotRemConsistency
  quickCheck prop_remInRange