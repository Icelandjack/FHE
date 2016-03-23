{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Vect where

import Control.Lens hiding (Indexed)
import Data.Int
import Formatting
import Formatting.ShortFormatters

import Variable
import Exp
import Repr
import Types

data Vector a where
  Indexed ∷ Exp Int8 → (Exp Int8 → a) → Vector a
  deriving Functor

instance FunctorWithIndex (Exp Int8) Vector where
  imap ∷ (Exp Int8 → a → b) → (Vector a → Vector b)
  imap f (Indexed ℓ ixf) = 
    Indexed ℓ (\i → f i (ixf i))

-- instance Show (Vector (Exp a)) where
--   show (Indexed l ixf) = let x = Variable "x" 0 
--     in 

--     formatToString ("(for "%sh%" ≔ 0…"%sh%", "%sh%")")
--       x l (ixf (Var (VAR x))

-- map₂ ∷ (a → b → c) → Vector a → Vector b → Vector c
-- map₂ f (Indexed len₁ ixf₁) (Indexed len₂ ixf₂) = 
--   Indexed (min' len₁ len₂) (\index → f (ixf₁ index)
--                                        (ixf₂ index))

-- map₂'' ∷ (Exp a → Exp b → Exp c) → Vector (Exp a) → Vector (Exp b) → Vector (Exp c)
-- map₂'' f (Indexed len₁ ixf₁) (Indexed len₂ ixf₂) = 
--   Indexed (min' len₁ len₂) (\index → f (ixf₁ index)
--                                        (ixf₂ index))

-- map₂' ∷ (Type a, Type b, Type c) 
--       ⇒ (Exp a → Exp b → Exp c) 
--       → Exp [a] → Exp [b] → Exp [c]
-- map₂' f xs ys = toExp (map₂'' f (fromExp xs) (fromExp ys))

-- instance TRepr a ⇒ Repr (Vector a) where
--   type ReprType (Vector a) = [ReprType a]

--   toExp (Indexed l ixf) = arr l (toExp . ixf)

--   fromExp arr = Indexed (len arr) (\ix → arr <!> ix) 

-- len ∷ Type a ⇒ Exp [a] → Exp Int
-- len = Len

-- (<!>) ∷ TRepr exp ⇒ Exp [ReprType exp] → Exp Int → exp
-- arr <!> ix = fromExp (ArrIx arr ix)

-- -- mem₁ ∷ Exp [Int]
-- -- mem₁ = Arr 10 (Var "mem1" `ArrIx`)

-- -- mem₂ ∷ Exp [Int]
-- -- mem₂ = Arr 10 (Var "mem2" `ArrIx`)

-- infixl 5 …

(…) ∷ Int8 → Exp Int8 → Vector (Exp Int8)
0…n = Indexed n id
1…n = Indexed n (+1)

-- -- -- sumFn ∷ Num a ⇒ Vector a → a
-- -- -- sumFn (Indexed l ixf) = for 0 (l-1) (\i s → s + ixf i)

-- -- -- countUp ∷ Exp → Vector Exp
-- -- -- countUp n = 0…n-1

-- -- -- countUp₁ ∷ Exp → Vector Exp
-- -- -- countUp₁ n = (+1) <$> 0…n
