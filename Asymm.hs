{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE ViewPatterns    #-}
{-# LANGUAGE RecordWildCards #-}

import Test.QuickCheck
import Test.QuickCheck.Monadic
import System.Random
import Control.Monad
import Text.Printf
import Data.List

import Auxiliary (nint)

-- | http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.33.1966&rep=rep1&type=pdf
-- ¬x == 1 ⊕ x
-- 
-- MAJ(x, y, z) = ((x ⊕ y) ∧ (x ⊕ z)) ⊕ x
infixr 6 :+, :⊕
infixr 7 :*, :∧
data Circuit = Nil
             | Circuit :⊕ Circuit
             | Circuit :∧ Circuit
               deriving Show

data Circuit' = Val Integer
              | Circuit' :+ Circuit'
              | Circuit' :* Circuit'
                deriving Show

integrate ∷ Circuit → [Integer] → Circuit'
integrate c xs = let (x, []) = go c xs in x where
  go ∷ Circuit → [Integer] → (Circuit', [Integer])
  go Nil      (x:xs) = (Val x, xs)
  go (a :⊕ b) xs     = let
    (a', xs')  = go a xs
    (b', xs'') = go b xs'
    in (a' :+ b', xs'')
  go (a :∧ b) xs     = let
    (a', xs')  = go a xs
    (b', xs'') = go b xs'
    in (a' :* b', xs'')

evalCircuit ∷ Circuit' → Integer
evalCircuit (Val i)  = i
evalCircuit (a :+ b) = evalCircuit a + evalCircuit b
evalCircuit (a :* b) = evalCircuit a * evalCircuit b

data Bit = O | I deriving (Show)

fromBit ∷ Bit → Integer
fromBit O = 0
fromBit I = 1

-- | http://research.microsoft.com/pubs/146975/ihe.pdf
data Param = Param {
  γ  ∷ Integer,              -- | γ : bit-length of integers in public key
  η  ∷ Integer,              -- | η : bit-length of secret key 
  ρ  ∷ Integer,              -- | ρ : bit-length of noise
  ρ' ∷ Integer,              -- | ρ′: secondary noise parameter
  τ  ∷ Integer               -- | τ : number of integers in public key
} deriving Show

securityParameters ∷ Integer → Param
securityParameters λ = Param {
  ρ  = λ,
  ρ' = 2*λ,
  η  = λ^2,
  γ  = λ^5,
  τ  = λ^5+λ
}

-- | Defines a range for N-bit numbers
withBits ∷ Integer → (Integer, Integer)
withBits bits = (2^(bits-1), 2^bits-1)

-- Quotient
q ∷ Integer → Integer → Integer
q(p) z = nint (fromIntegral z / fromIntegral p) 

-- Remainder
remainder ∷ Integer → Integer → Integer
remainder(p) z = z - q(p) z * p

distribution ∷ Param → Integer → IO Integer
distribution Param{..} p = do
  
  -- choose q ←$- ℤ ∩ [0, 2^γ/p)
  q ← randomRIO (0, div (2^γ) p - 1)

  -- choose r ←$- ℤ ∩ (-2^ρ, 2^ρ)
  r ← randomRIO (-2^ρ + 1, 2^ρ - 1)

  return (let x = p*q + r in x)

keygen ∷ Param → IO (Integer, [Integer])
keygen param@Param{..} = do
  sk ← secretKey
  pk ← publicKey sk
  
  return (sk, pk) where

    secretKey ∷ IO Integer
    secretKey = do
      --     Secret key: odd η-bit integer
      -- p ←$- (2ℤ + 1) ∩ [2^(η-1), 2^η)
      sk ← randomRIO (withBits η)
      if odd sk
        then return sk
        else secretKey

    publicKey ∷ Integer → IO [Integer]
    publicKey p = do
      -- x_i ←$- D(p) for i = 0,…,τ
      xs ← replicateM (fromInteger τ+1) (distribution param p)
  
      -- Relabel so that x₀ is the largest
      let maxVal = maximum xs
          xs'    = maxVal : delete maxVal xs

      -- Restart unless x₀ is off and r_p(x₀) is even
      if odd maxVal && even (mod maxVal p) -- even (r(p) maxVal)
        then return xs'
        else print maxVal >> publicKey p

-- [z]_p = r(p) z

-- | Encrypt a bit m ∈ {0, 1}
encrypt ∷ Param → [Integer] → Bit → IO Integer
encrypt Param{..} (x₀:_) (fromBit → m) = do

  -- Random subset S ⊆ {1,2,…,τ}
  subsetS ← randomSubset [1..τ]

  -- Random integer r in (-2^ρ′, 2^ρ′)
  r ← randomRIO (-2^ρ' + 1, 2^ρ' - 1)

  -- Output c ← [m + 2r + 2 Σi∈S x_i]x₀
  return (let c = remainder(x₀) (m + 2 * r + 2 * sum subsetS) in c)

  where
    randomSubset ∷ [a] → IO [a]
    randomSubset = filterM (const randomIO)

decrypt ∷ Integer → Integer → Integer
decrypt sk c = (remainder sk c) `mod` 2

evaluate ∷ Circuit → [Integer] → Integer
evaluate circuit cs = evalCircuit (integrate circuit cs)

foobar = do
  let param = securityParameters 3

  (sk, pk) ← keygen param

  cs ← mapM (encrypt param pk) [O,O,I,O,I]

  let cs' = evaluate (Nil :∧ (Nil :⊕ Nil) :⊕ Nil :∧ Nil) cs

  return (decrypt sk cs')

-- prop_corr (Msg m) = monadicIO $ do
--   let param = securityParameter 2
--   key ← run (keygen param)
--   c   ← run (encrypt param key m)
--   assert (m == decrypt key c)

-- prop_add (Msg m1) (Msg m2) = monadicIO $ do
--   let param = securityParameter 3
--   key ← run (keygen param)
  
--   c1   ← run (encrypt param key m1)
--   c2   ← run (encrypt param key m2)
--   assert ((m1+m2) `mod` 2 == decrypt key (c1+c2))

-- prop_mul (Msg m1) (Msg m2) = monadicIO $ do
--   let param = securityParameter 2
--   key ← run (keygen param)

--   c1   ← run (encrypt param key m1)
--   c2   ← run (encrypt param key m2)
--   assert (m1*m2 == decrypt key (c1*c2))

-- -- [ihe] http://research.microsoft.com/pubs/146975/ihe.pdf

-- param = securityParameter 2

-- foobar c (Positive p) = let
--   c' = c `mod` p
--   in divides (c - c') p

-- divides a b = div a b == 0

-- -- Quotient of z with respect to p

-- -- If a, d ∶ Integer, where d ≠ 0.
-- --     REM is r such that a = qd + r for some (q ∶ Integer) with |r| < |d|
-- --     

-- | The first integer in the public key is the largest one.
prop_firstMax = monadicIO $ do
  (_, x0:rest) ← run $ keygen (securityParameters 2)
  
  assert $ all (x0 >) rest

-- -- r(p) z ∈ (-p/2, p/2]
prop_r(Positive p) z = (abs z) > 2 && (abs p) > 2 ==> let
  u = remainder(p) z
  in -p`div`2 < u && u <= p`div`2

-- -- (KeyGen, Encrypt, Decrypt, Evaluate) is correct for a given t-input
-- -- circuit C if, for any key-pair (sk, pk) output by KeyGen(λ), any t
-- -- plaintext bits m₁, …, m_t and any ciphertexts c = ⟨c₁, …, c_t⟩ with
-- -- c_i ← Encrypt(pk, m_i) 
-- --     Decrypt(sk, Evaluate(pk, C, c)) = C(m₁, …, mₜ)b
-- prop_correct = undefined

