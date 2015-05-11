module Vect where

import Expr

data Vector a = Indexed Exp (Exp → a) deriving Functor

-- instance Repr a ⇒ Repr (Vector a) where
--   from ∷ Vector a → Exp
--   from (Indexed len ixf) = Arr len (fmap from ixf)

--   to ∷ Exp → Vector a 
--   to (Arr len ixf) = Indexed len (fmap to ixf)

-- map₂ ∷ (a → b → c) → (Vector a → Vector b → Vector c)
-- map₂ f (Indexed len₁ ixf₁) (Indexed len₂ ixf₂) = 
--   Indexed (len₁ ⊔ len₂) (\index → f (ixf₁ index)
--                                     (ixf₂ index))

map₂ ∷ (Exp → Exp → Exp) → (Exp → Exp → Exp)
map₂ f (Arr len₁ ixf₁) (Arr len₂ ixf₂) = 
  Arr (len₁ ⊔ len₂) (\index → f (ixf₁ index)
                                (ixf₂ index))

mem₁ ∷ Exp
mem₁ = Arr 10 (Var "mem1" `ArrIx`)

mem₂ ∷ Exp
mem₂ = Arr 10 (Var "mem2" `ArrIx`)

instance Show (Vector Exp) where
  show (Indexed l ixf) = "(for x ≔ 0…" ++ show l ++ ", " ++ show (ixf (Var "x")) ++ ")"

infixl 5 …

(…) ∷ Int → Exp → Vector Exp
0…n = Indexed n id
1…n = Indexed n (+1)

-- sumFn ∷ Num a ⇒ Vector a → a
-- sumFn (Indexed l ixf) = for 0 (l-1) (\i s → s + ixf i)

-- for ∷ Integer → Exp → (Exp → a → a) → a
-- for = undefined

-- countUp ∷ Exp → Vector Exp
-- countUp n = 0…n-1

-- countUp₁ ∷ Exp → Vector Exp
-- countUp₁ n = (+1) <$> 0…n
