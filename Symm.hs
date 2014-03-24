{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ViewPatterns #-}

import Test.QuickCheck
import Test.QuickCheck.Monadic
import System.Random
import Control.Monad
import Text.Printf

data Bit = O | I 
data Param = Param { getN ∷ Integer, getP ∷ Integer, getQ ∷ Integer } deriving Show

data Circuit = Val Integer
             | AND Circuit Circuit
             | MUL Circuit Circuit
             deriving Show

securityParameter λ = Param {
  getN = λ,
  getP = λ^2,
  getQ = λ^5
}

withBits ∷ Integer → (Integer, Integer)
withBits bits = (2^(bits-1), 2^bits-1)

randomBitNumber ∷ Integer → Integer
randomBitNumber bits = undefined

-- | Key is random P-bit odd integer p from the interval [ihe]
--     p ∈ [2^(P-1), 2^P) 
keygen ∷ Param → IO Integer
keygen Param{getP,getN} = do
  gen ← newStdGen
  return $ head $ filter even $ randomRs (withBits getP) gen

-- | To encrypt a bit m ∈ {0, 1}
encrypt ∷ Param → Integer → Integer → IO Integer
encrypt Param{getN,getQ} p m = do
  let nDiv2 = (2^getN) `div` 2

  -- n = 2^getN
  -- r = 2^getN
  r ← randomRIO (-nDiv2 + 1, nDiv2 - 1) -- (x)

  -- 2r < p/2 (in absolute value?)
  unless (2*r < p`div`2)
    (error "WTF")

  let m' = m + 2*r              -- B

  -- m' = m mod 2
  unless (mod m' 2 == m)
    (error "WTF2")

  let qDiv2 = (2^getQ) `div` 2
  q ← randomRIO (-qDiv2 + 1, qDiv2 - 1)
  let c = m' + p*q

  return c

-- data Param = Param { n ∷ Integer, p ∷ Integer, q ∷ Integer } deriving Show

newtype Msg = Msg Integer deriving Show

instance Arbitrary Msg where
  arbitrary = fmap Msg (choose (0, 1))

decrypt ∷ Integer → Integer → Integer
decrypt p c = (r p c) `mod` 2

-- t-input 'circuit' 
-- 
evaluated key circ  = undefined

prop_corr (Msg m) = monadicIO $ do
  let param = securityParameter 2
  key ← run (keygen param)
  c   ← run (encrypt param key m)
  assert (m == decrypt key c)

prop_add (Msg m1) (Msg m2) = monadicIO $ do
  let param = securityParameter 3
  key ← run (keygen param)
  
  c1   ← run (encrypt param key m1)
  c2   ← run (encrypt param key m2)
  assert ((m1+m2) `mod` 2 == decrypt key (c1+c2))

prop_mul (Msg m1) (Msg m2) = monadicIO $ do
  let param = securityParameter 2
  key ← run (keygen param)

  c1   ← run (encrypt param key m1)
  c2   ← run (encrypt param key m2)
  assert (m1*m2 == decrypt key (c1*c2))

-- [ihe] http://research.microsoft.com/pubs/146975/ihe.pdf

param = securityParameter 2

foobar c (Positive p) = let
  c' = c `mod` p
  in divides (c - c') p

divides a b = div a b == 0

-- Quotient of z with respect to p

-- If a, d ∶ Integer, where d ≠ 0.
--     REM is r such that a = qd + r for some (q ∶ Integer) with |r| < |d|
--     

q ∷ Integer → Integer → Integer
q(p) z = round (fromIntegral z / fromIntegral p) 

r ∷ Integer → Integer → Integer
r(p) z = z - q(p) z * p

-- r(p) z ∈ (-p/2, p/2]
prop_r(Positive p) z = (abs z) > 2 && (abs p) > 2 ==> let
  u = r(p) z
  in -p`div`2 < u && u <= p`div`2
