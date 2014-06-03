{-# LANGUAGE RebindableSyntax, GADTs, TypeFamilies, UnicodeSyntax, PatternSynonyms, LambdaCase, ViewPatterns, InstanceSigs, LiberalTypeSynonyms #-}

module AES where

import EDSL
import Pretty

import Prelude
import Data.List
import qualified Data.Text as T
import Data.Word
import Data.Maybe
import Data.Bits
import Data.Monoid
import Data.List.Split
import Test.QuickCheck
import Control.Applicative
import Numeric
import Data.Char
import Control.Monad.State

bits n = showIntAtBase 2 intToDigit n ""

-- block = 128
-- key = 128
-- encryption = 10 rounds of processing
-- rounds are identical except last

data Matrix a = M [[a]] deriving (Show, Eq)

instance Functor Matrix where
  fmap f (M ass) = M (fmap (fmap f) ass)

instance Embed (Matrix (Exp Word8)) where
  type Repr (Matrix (Exp Word8)) = [Word8]

  sugar   = sugarMatrix
  desugar = desugarMatrix


sugarMatrix ∷ Exp [Word8] → Matrix (Exp Word8)
sugarMatrix (Arr 16 ixf) = M (chunksOf 4 (map (ixf . Lit) [0..15]))
sugarMatrix Arr{}        = error "length mismatch"

desugarMatrix ∷ Matrix (Exp Word8) → Exp [Word8]
desugarMatrix (M mss)
    | length (concat mss) == 16 = Table (concat mss)
    | otherwise                 = error "desugar: length mismatch"

-- AES
-- SubBytes()
-- ShiftRows()
-- MixColumns()
-- AddRoundKey()

plusOne ∷ Matrix (Exp Word8) → Matrix (Exp Word8)
plusOne = fmap (+1)

subBytes' ∷ [Word8] → Matrix Word8 → Matrix Word8
subBytes' (fromList → sbox) = undefined

-- subBytes ∷ Exp [Word8] → a
subBytes = Lambda undefined

-- subBytes ∷ [Word8] → Matrix Word8 → Matrix Word8
-- subBytes (fromList → sbox) (M mms) = M mms where
  
--   sBoxLookup ∷ Exp Word8 → Exp Word8
--   sBoxLookup key = sbox ! Conv key

-- makeLookup ∷ [Word8] → Exp [Word8]
-- makeLookup box = Lookup (Lit (length box)) undefined where
--   foo ∷ Word8 → Word8
--   foo i = fromJust (lookup i (zip [0..] sBox))

sBox ∷ [Word8]
sBox = [0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76, 0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0, 0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15, 0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75, 0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84, 0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF, 0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8, 0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2, 0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73, 0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB, 0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79, 0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08, 0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A, 0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E, 0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF, 0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16]

shiftRows ∷ Matrix a → Matrix a
shiftRows (M [a,b,c,d]) = M [c1, c2, c3, c4] where
  c1 = cycle' a 0
  c2 = cycle' b 1
  c3 = cycle' c 2
  c4 = cycle' d 3

cycle' ∷ [a] → Int→ [a]
cycle' [] _                       = []
cycle' xs 0                       = xs
cycle' xs ((`mod` length xs) → n) = drop n xs ++ take n xs

prop_cycle ∷ Eq a ⇒ [a] → Bool
prop_cycle xs = cycle' xs (length xs) == xs

example ∷ Matrix (Exp Word8)
example = M [ [0, 1, 2, 3]
            , [4, 5, 6, 7]
            , [8, 9, 10, 11]
            , [12, 13, 14, 15]
            ]

-- | Shifting by powers of 24 is idempotent
prop_shiftRows ∷ Eq a ⇒ Matrix a → Int → Bool
prop_shiftRows matrix (abs → n) =
  iterate shiftRows matrix !! (2*3*4*n)
  ==
  matrix

mixColumns (M (transpose → mms)) = M undefined where
  foo = undefined

-- shiftRows ∷ Matrix44 → Matrix44
-- shiftRows (M44 ixf) = M44 (modify ixf) where
--   modify ∷ (Exp Int → Exp Word8) → (Exp Int → Exp Word8)

--   -- Second row (1,5,9,13) is shifted by one to the left
--   modify ixf 1  = ixf 5
--   modify ixf 5  = ixf 9
--   modify ixf 9  = ixf 13
--   modify ixf 13 = ixf 1

--   -- Third row (1,5,9,13) is shifted by two to the left
--   modify ixf 2  = ixf 10
--   modify ixf 6  = ixf 14
--   modify ixf 10 = ixf 2
--   modify ixf 14 = ixf 6

--   -- Fourth row (1,5,9,13) is shifted by three to the left
--   modify ixf 3  = ixf 15
--   modify ixf 7  = ixf 3
--   modify ixf 11 = ixf 7
--   modify ixf 15 = ixf 11

--   -- First row (0, 4, 8, 12) is unchanged
--   modify ixf n = ixf n

addRoundKey = undefined

-- aes ∷ Matrix Word8 → Matrix Word8 → Matrix Word8
-- aes inBlock key = for 10 inBlock step where

--   step _ = shiftRows . subBytes sBox 

-- addRoundKey ∷ Matrix Word8 → Matrix Word8 
-- addRoundKey = undefined

-- -- trans b = foldr (\i acc → case fooo b i == Fa of
-- --                     True  → acc
-- --                     False → setBit acc i) zeroBits [0..7]

-- -- bb ∷ Word8 → Word8
-- -- bb b = (set 7 . set 6 . set 5 . set 4 . set 3 . set 2 . set 1 . set 0) 0 where
-- --   set i b' = case fooo b i of
-- --     True  → setBit b' i
-- --     False → b'

instance Arbitrary a ⇒ Arbitrary (Matrix a) where
  arbitrary = M <$> vectorOf 4 (vector 4) 

data Querying k v a = Querying [k] ([(k, v)] → a)

