module Auxiliary (nintRoundHalfUp, remainder, quotient) where

import Test.QuickCheck

-- Round to Nearest INT rounding half up
nintRoundHalfUp ∷ (Integral b, RealFrac a) ⇒ a → b
nintRoundHalfUp z = ceiling (z - 0.5) -- round z -- floor (z + 0.5)

infixl 7 `quotient`
-- Quotient
quotient ∷ Integer → Integer → Integer
quotient(0) z = error "Exception: divide by zero"
quotient(p) z = nintRoundHalfUp (fromIntegral z / fromIntegral p) 

infixl 7 `remainder`
-- Remainder
remainder ∷ Integer → Integer → Integer
remainder(0) z = error "Exception: divide by zero"
remainder(p) z = z - quotient(p) z * p
