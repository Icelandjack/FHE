module Vect where

import Exp
import Repr
import Types

-- instance Show (Vector (Exp a)) where
--   show (Indexed l ixf) = "(for x ≔ 0…" ++ show l ++ ", " ++ show (ixf (Var "x")) ++ ")"

-- data Vector a where
--   Indexed ∷ Exp Int → (Exp Int → a) → Vector a
--   deriving Functor

-- map₂ ∷ (a → b → c) → Vector a → Vector b → Vector c
-- map₂ f (Indexed len₁ ixf₁) (Indexed len₂ ixf₂) = 
--   Indexed (len₁ ⊔ len₂) (\index → f (ixf₁ index)
--                                     (ixf₂ index))

-- instance TRepr a ⇒ Repr (Vector a) where
--   type ReprType (Vector a) = [ReprType a]

--   toExp ∷ Vector a → Exp [ReprType a]
--   toExp (Indexed l ixf) = Arr l (toExp . ixf)

--   fromExp ∷ Exp [ReprType a] → Vector a
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

-- (…) ∷ Int → Exp Int → Vector (Exp Int)
-- 0…n = Indexed n id
-- 1…n = Indexed n (+1)

-- -- -- sumFn ∷ Num a ⇒ Vector a → a
-- -- -- sumFn (Indexed l ixf) = for 0 (l-1) (\i s → s + ixf i)

-- -- -- for ∷ Integer → Exp → (Exp → a → a) → a
-- -- -- for = undefined

-- -- -- countUp ∷ Exp → Vector Exp
-- -- -- countUp n = 0…n-1

-- -- -- countUp₁ ∷ Exp → Vector Exp
-- -- -- countUp₁ n = (+1) <$> 0…n
