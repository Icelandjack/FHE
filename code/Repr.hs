module Repr where

import Exp

class Repr exp where
  type Type exp

  toExp   ∷ exp → Exp (Type exp)
  fromExp ∷ Exp (Type exp) → exp

instance Repr (Exp a) where
  type Type (Exp a) = a

  fromExp ∷ Exp a → Exp a
  fromExp = id

  toExp ∷ Exp a → Exp a
  toExp = id

ifThenElse ∷ Repr a ⇒ Exp Bool → a → a → a
ifThenElse c t e = fromExp (If c (toExp t) (toExp e))

while ∷ Repr st ⇒ (st → Exp Bool) → (st → st) → st → st
while c b i = fromExp (While (c . fromExp) (toExp . b . fromExp) (toExp i))

