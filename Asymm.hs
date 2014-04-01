{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE ViewPatterns    #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UnicodeSyntax   #-}

import System.Random
import Control.Monad
import Control.Applicative
import Text.Printf
import Data.List

import Auxiliary (remainder, quotient)

-- | http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.33.1966&rep=rep1&type=pdf
-- x, y ∈ {0, 1}
-- AND x y = xy
-- OR  x y = 1 - (1 - x)(1 - y)
-- NOT x   = 1 - x
-- ¬x      = 1 ⊕ x
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

newtype SecretKey = SecretKey Integer deriving Show
newtype PublicKey = PublicKey [Integer] deriving Show

assert ∷ Bool → String → Either String ()
assert True  _   = Right ()
assert False str = Left str

hasBitSize ∷ Integer → Integer → Bool
n `hasBitSize` bits = 2^(bits-1) <= n
                   && n          <= 2^bits

mkSecretKey ∷ Param → Integer → Either String SecretKey
mkSecretKey Param{η} n = do
  assert (n `hasBitSize` η) "n has wrong bitsize"
  assert (odd n)            "n is even"
  return (SecretKey n)

mkPublicKey ∷ Param → SecretKey → [Integer] → Either String PublicKey
mkPublicKey _         _             []      = Left "Empty private key"
mkPublicKey Param{..} (SecretKey p) (x₀:xs) = do
  -- For the public key, sample
  --     x_i ← ... for i = 0, ..., τ
  -- Relabel so that x₀ is the largest
  assert (all (x₀ >) xs) "x₀ is not the largest element!"

  -- Restart unless x₀ is odd or r_p(x₀) is even
  assert (odd x₀)
      (show x₀ ++ " must be odd")
  assert (even (remainder(p) x₀))
      ("r_" ++ show p ++ "(" ++ show x₀ ++ ") must be even")
  
  return (PublicKey (x₀:xs))

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

toBit ∷ Integer → Bit
toBit 0 = O
toBit 1 = I

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

distribution ∷ Param → Integer → IO Integer
distribution Param{γ, ρ} p = do
  unless (odd p) (error "Secret key is even!") 
  unless (p > 0) (error "Secret key is negative!") 

  -- choose q ←$- ℤ ∩ [0, 2^γ/p)
  q ← randomRIO (0, div (2^γ) p - 1)

  -- choose r ←$- ℤ ∩ (-2^ρ, 2^ρ)
  r ← randomRIO (-2^ρ + 1, 2^ρ - 1)

  return (p*q + r)

keygen ∷ Param → IO (SecretKey, PublicKey)
keygen param@Param{..} = do
  p  ← secretKey
  pk ← publicKey p
  
  return (p, pk) where

    -- The secret key is an odd η-bit integer.
    secretKey ∷ IO SecretKey
    secretKey = do

      -- p ←$- (2ℤ + 1) ∩ [2^(η-1), 2^η)
      p ← randomRIO (withBits η)
  
      case mkSecretKey param p of
        Right secretKey → {- print secretKey >> -} return secretKey
        Left  err       → {- putStrLn err    >> -} secretKey

    publicKey ∷ SecretKey → IO PublicKey
    publicKey sk@(SecretKey p) = do
      -- x_i ←$- D(p) for i = 0,…,τ
      xs ← replicateM (fromInteger τ+1) (distribution param p)
  
      -- Relabel so that x₀ is the largest
      let maxVal = maximum xs
          xs'    = maxVal : delete maxVal xs

      case mkPublicKey param sk xs' of
        Right pk → return pk
        Left err → {- putStrLn err >> -} publicKey sk

-- | Encrypt a bit m ∈ {0, 1}
encrypt ∷ Param → PublicKey → Bit → IO Integer
encrypt Param{..} (PublicKey (x₀:xs)) (fromBit → m) = do
  -- Choose a random subset S ⊆ {1,2,…,τ} and compute 
  --     Σ (i ∈ S) x_i
  -- Instead of choosing random a random subset of indices
  -- directly compute random sublist.
  -- x₀ should not be a part of the subset(?)
  subsetSum ← sum <$> randomSubset xs

  -- Random integer r in (-2^ρ′, 2^ρ′)
  r ← randomRIO (-2^ρ' + 1, 2^ρ' - 1)

  -- Output c ← [m + 2r + 2 Σi∈S x_i]x₀
  return (remainder x₀ (m + 2*r + 2*subsetSum))

  where
    randomSubset ∷ [a] → IO [a]
    randomSubset = filterM (const randomIO)

decrypt ∷ SecretKey → Integer → Bit
decrypt (SecretKey sk) c = toBit (remainder(2) (remainder(sk) c))

evaluate' ∷ Circuit → [Integer] → Integer
evaluate' circuit cs = evalCircuit (integrate circuit cs)

run = do
  let param = securityParameters 2

  (secretKey, publicKey) ← keygen param
  c ← encrypt param publicKey O
  return (decrypt secretKey c)

--   cs ← mapM (encrypt param pk) [O,O,I,O,I]

--   let cs' = evaluate' (Nil :∧ (Nil :⊕ Nil) :⊕ Nil :∧ Nil) cs

--   return (decrypt sk cs')

-- -- prop_corr (Msg m) = monadicIO $ do
-- --   let param = securityParameter 2
-- --   key ← run (keygen param)
-- --   c   ← run (encrypt param key m)
-- --   assert (m == decrypt key c)

-- -- prop_add (Msg m1) (Msg m2) = monadicIO $ do
-- --   let param = securityParameter 3
-- --   key ← run (keygen param)
  
-- --   c1   ← run (encrypt param key m1)
-- --   c2   ← run (encrypt param key m2)
-- --   assert ((m1+m2) `mod` 2 == decrypt key (c1+c2))

-- -- prop_mul (Msg m1) (Msg m2) = monadicIO $ do
-- --   let param = securityParameter 2
-- --   key ← run (keygen param)

-- --   c1   ← run (encrypt param key m1)
-- --   c2   ← run (encrypt param key m2)
-- --   assert (m1*m2 == decrypt key (c1*c2))

-- -- -- [ihe] http://research.microsoft.com/pubs/146975/ihe.pdf

p' = securityParameters 2

-- -- foobar c (Positive p) = let
-- --   c' = c `mod` p
-- --   in divides (c - c') p

-- -- divides a b = div a b == 0

-- -- -- Quotient of z with respect to p

-- -- -- If a, d ∶ Integer, where d ≠ 0.
-- -- --     REM is r such that a = qd + r for some (q ∶ Integer) with |r| < |d|
-- -- --     

-- -- | The first integer in the public key is the largest one.
-- -- prop_firstMax = monadicIO $ do
-- --   (_, x0:rest) ← run $ keygen (securityParameters 2)
  
-- --   assert $ all (x0 >) rest

-- -- -- r(p) z ∈ (-p/2, p/2]
-- -- prop_r(Positive p) z = (abs z) > 2 && (abs p) > 2 ==> let
-- --   u = remainder(p) z
-- --   in -p`div`2 < u && u <= p`div`2

-- -- -- (KeyGen, Encrypt, Decrypt, Evaluate) is correct for a given t-input
-- -- -- circuit C if, for any key-pair (sk, pk) output by KeyGen(λ), any t
-- -- -- plaintext bits m₁, …, m_t and any ciphertexts c = ⟨c₁, …, c_t⟩ with
-- -- -- c_i ← Encrypt(pk, m_i) 
-- -- --     Decrypt(sk, Evaluate(pk, C, c)) = C(m₁, …, mₜ)b
-- -- prop_correct = undefined

