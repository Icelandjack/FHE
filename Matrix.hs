{-# LANGUAGE DeriveFunctor, ViewPatterns, PatternSynonyms #-}

module Matrix (
  Matrix,

  -- Patterns
  pattern Matrix,
  pattern Rows,
  pattern Columns,

  -- Smart constructors
  fromList,
  fromList',
  fromLists,
  fromLists',
  fromColumns,

  -- Functions
  overColumns
  ) where

import Data.List
import Data.List.Split
import Data.Maybe
import Data.Proxy
import Data.Word
import GHC.TypeLits
import qualified EDSL as E
import EDSL hiding (fromList)

-- | A matrix is just nested lists, inner-most lists are rows.
--   i-th elements of each list constitute columns. 
--   We don't export M.
data Matrix a = M { getMatrix ∷ [[a]] } deriving (Eq)

-- | Patterns for matching rows, 
pattern Matrix  rows    ← M rows
pattern Rows    a b c d ← M (id        → [a, b, c, d])
pattern Columns a b c d ← M (transpose → [a, b, c, d])

-- | Matrix instances
instance Show a ⇒ Show (Matrix a) where
  show (Rows a b c d) = intercalate ",\n" [
    "[" ++ show a,
    " " ++ show b,
    " " ++ show c,
    " " ++ show d ++ "]"
    ]

instance Functor Matrix where
  fmap f (M mats) = fromLists' (map (map f) mats)

instance Embed (Matrix (Exp Word8)) where
  type Repr (Matrix (Exp Word8)) = LenVec 16 Word8

  sugar = aux
    where
      aux ∷ Exp (LenVec 16 Word8) → Matrix (Exp Word8)
      aux (Arr2 (Len 16) ixf) = fromList' (map ixf [0..15])
  
  desugar = aux
    where
      aux ∷ Matrix (Exp Word8) → Exp (LenVec 16 Word8) 
      aux (M ms) = fromJust (E.fromList (concat ms))

-- Smart matrix constructors
fromList ∷ [a] → Maybe (Matrix a)      
fromList xs
  | 16 ← length xs
  = return (M (chunksOf 4 xs))
  | otherwise
  = Nothing

fromList' ∷ [a] → Matrix a
fromList' = fromJust . fromList

fromLists ∷ [[a]] → Maybe (Matrix a)
fromLists xs
  | [4,4,4,4] ← map length xs
  = return (M xs)
  | otherwise
  = Nothing

fromLists' ∷ [[a]] → Matrix a
fromLists' = fromJust . fromLists

fromColumns ∷ [[a]] → Matrix a
fromColumns = fromLists' . transpose

-- | Functions
overColumns ∷ ([t] → [a]) → Matrix t → Matrix a
overColumns f (Columns c₀ c₁ c₂ c₃) = fromColumns (map f [c₀, c₁, c₂, c₃])

-- | Utilities
pattern Len n ← (natVal → n)