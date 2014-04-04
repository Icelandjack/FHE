{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

import Data.Array
import Data.Bits

class Syntactic a where
  type Internal a
  toFunC :: a → E (Internal a)
  fromFunC :: E (Internal a) → a

data E a where
  LitI :: Int -> E Int
  Arr  :: E Int -> (E Int -> E a) -> E [a]
  ArrLen :: E [a] → E Int
  ArrIx :: E [a] → E Int → E a
  Random :: E Int -> E [a]

instance Syntactic (E a) where
  type Internal (E a) = a
  toFunC ast = ast
  fromFunC ast = ast

-- instance (Syntactic a, Syntactic b) ⇒ Syntactic (a, b) where
--   type Internal (a, b) = (Internal a, Internal b)
--   toFunC (a, b) = Pair (toFunC a) (toFunC b)
--   fromFunC p = (fromFunC (Fst p), fromFunC (Snd p))

instance (n ~ Int) ⇒ Num (E n) where
  fromInteger = LitI . fromIntegral

len :: E [a] -> E Int
len = ArrLen

(<!>) :: Syntactic a => E [Internal a] -> E Int -> a
arr <!> ix = fromFunC (ArrIx arr ix)

data Vector a where
  Indexed :: E Int -> (E Int -> a) -> Vector a

instance Syntactic a => Syntactic (Vector a) where
  type Internal (Vector a) = [Internal a]
  toFunC (Indexed l ixf) = Arr l (toFunC . ixf)
  fromFunC arr = Indexed (len arr) (\ix -> arr <!> ix)

zipWithVec :: (Syntactic a, Syntactic b) => (a → b → c) → Vector a → Vector b → Vector c
zipWithVec f (Indexed l1 ixf1) (Indexed l2 ixf2)  =
  Indexed undefined (\ix → f (ixf1 ix) (ixf2 ix))

instance Functor Vector where
  fmap f (Indexed l ixf) = Indexed l (f . ixf)

instance n ~ Int ⇒ Bits (E n) where