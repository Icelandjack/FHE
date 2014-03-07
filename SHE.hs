{-# LANGUAGE ViewPatterns #-}

import Control.Applicative
import System.Random
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Text.Printf
import Data.Word

-- data Parameters = Param {
--   γ ∷ Integer,    -- Bit-length of integers in public key
--   η ∷ Integer,    -- Bit-length of secret key
--   ρ ∷ Integer,    -- Bit-length of noise
--   τ ∷ Integer     -- Number of integers in public key
--   }

-- type SecurityParam = Integer

-- mkParameters ∷ SecurityParam → Integer → Integer → Integer → Integer → Parameters
-- mkParameters λ = undefined

-- Odd number
newtype SharedSecretKey = SharedSecretKey { getShared :: Integer } deriving (Eq, Show)

instance Arbitrary SharedSecretKey where
  arbitrary = do

    η ∷ Integer ← succ . abs <$> arbitrary
  
    let range ∷ (Integer, Integer)
        range = (2^(η-1), 2^η - 1)
    
    key ← choose range

    if odd key 
      then return (SharedSecretKey key)
      else arbitrary

data Bit = O | I deriving (Eq, Show)

instance Arbitrary Bit where
  arbitrary = do
    bool ← arbitrary
    return (if bool then I else O)

toInt ∷ Bit → Integer
toInt O = 0
toInt I = 1

fromInt ∷ Integer → Bit 
fromInt 0 = O
fromInt 1 = I

p ∷ SharedSecretKey
p = SharedSecretKey 13

keygen ∷ Integer → IO SharedSecretKey
keygen η = do

  let range ∷ (Integer, Integer)
      range = (2^(η-1), 2^η - 1)

  gen ← newStdGen
  
  return $ SharedSecretKey $ (+3) $ head $ filter odd $ randomRs range gen

encrypt ∷ Integer → SharedSecretKey → Bit → IO Integer
encrypt η (SharedSecretKey p) (toInt → m) = do

  let rExponent ∷ Integer
      rExponent = ceiling (sqrt (fromIntegral η))
  
  let rRange ∷ (Integer, Integer)
      rRange = (2^(rExponent-1), 2^(rExponent+1))
  
  -- random small R
  r ← randomRIO rRange
  -- printf "r: %d\n" r
  
  let qExponent ∷ Integer
      qExponent = round (fromIntegral (η ^ 3))
  
  let qRange ∷ (Integer, Integer)
      qRange = (2^(qExponent-1), 2^(qExponent+1))

  -- random large Q
  q ← randomRIO qRange
  
  -- printf "q: %d\n" q

  
  
  return $ (p*q + 2*r + m ∷ Integer)

decrypt ∷ SharedSecretKey → Integer → Bit
decrypt (SharedSecretKey p) c = fromInt (c `mod` p `mod` 2)

prop_encdec ∷ Word8 → Bit → Property
prop_encdec seed bit = monadicIO $ do
  -- run (putStrLn "new")

  let seed' = succ (fromIntegral (seed `mod` 40))
  key ← run (keygen seed')

  run (printf "key: %d\n" (getShared key) :: IO ())
  cipher ← run (encrypt seed' key bit)

  let bit' = decrypt key cipher
  -- run (putChar '\n')
  assert (bit == bit')

foo ∷ Int → Bit → IO Bit
foo η msg = do
  key ← keygen (fromIntegral η)

  c     ← encrypt (fromIntegral η) key msg
  let d = decrypt key c
  
  return d

