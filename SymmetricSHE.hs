{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UnicodeSyntax              #-}

import System.Random
import Test.QuickCheck
import Test.QuickCheck.Modifiers
import Numeric
import Data.Char
import Data.List

data SecurityParam = Param {
  getλ ∷ Integer,
  getN ∷ Integer,
  getP ∷ Integer,
  getQ ∷ Integer
  }

data Bit = O | I deriving (Enum, Show)

fromBit ∷ Message → Integer
fromBit O = 0
fromBit I = 1

-- toBit (Ciphertext 0) = O
-- toBit (Ciphertext 1) = I
-- toBit _              = error "toBit: invalid value"

type SecretKey  = Integer
type Message    = Bit
type Ciphertext = Integer

suchThatR ∷ (RandomGen g, Random a) ⇒ (a, a) → (a → Bool) → g → (a, g)
suchThatR range pred gen₀ = if pred val
                                  then (val, gen₁)
                                  else suchThatR range pred gen₁
  where
    (val, gen₁) = randomR range gen₀

mkSecurityParam ∷ Integer → SecurityParam
mkSecurityParam λ = Param {
  getλ = λ,
  getN = λ,
  getP = λ^2,
  getQ = λ^5
}

evaluate = undefined

recrypt gen param pk d ski msg = let
  (cipher, g) = encrypt gen param pk msg

  output = evaluate pk d (cipher, pk)
  in output

-- full gen₀ λ msg = let
--   securityParam = mkSecurityParam λ

--   (secretKey, gen₁) = keyGen gen₀ securityParam

--   c = encrypt gen₁ securityParam secretKey msg
--   in undefined

keyGen ∷ RandomGen g ⇒ g → SecurityParam → (SecretKey, g)
keyGen gen Param{getP = p} = suchThatR (bitRange p) even gen

encrypt ∷ RandomGen g ⇒ g → SecurityParam → SecretKey → Message → (Ciphertext, g)
encrypt gen₀ Param{getQ, getN} p (fromBit → m) = (c, gen₂)
  where
    (q, gen₁)   = randomR (bitRange getQ) gen₀
    (m'', gen₂) = randomR (bitRange getN) gen₁
    m'          = undefined
    c           = undefined (undefined + p*q)
  
decrypt ∷ SecretKey → Ciphertext → Message
decrypt key c = undefined where
  _ = undefined

-- prop_foobar ∷ Integer → Property
-- prop_foobar exp = forAll arbitraryBitsize $ \n → genericLength (toBin n) == exp'
--   where
--     exp' ∷ Integer
--     exp' = (abs exp + 1) `mod` 250

--     arbitraryBitsize ∷ Gen Integer
--     arbitraryBitsize = choose (bitRange exp')

bitRange ∷ Integral a ⇒ a → (a, a)
bitRange exp = (2^(exp-1), 2^exp-1)
  
-- toBin n = showIntAtBase 2 intToDigit n ""
