module Expr where

data Exp 
  = I Integer
  | Add Exp Exp 
  | Mul Exp Exp
  | IfThenElse Exp Exp Exp 
  | Var String
  | Fn String Exp [Exp]
  | Lam String Exp
  deriving Show

instance Num Exp where
  (+) ∷ Exp → Exp → Exp
  a + b = Add a b

  (*) ∷ Exp → Exp → Exp
  a * b = Mul a b

  fromInteger ∷ Integer → Exp
  fromInteger i = I (fromInteger i)

pattern Fn₁ str x     = Fn str x []
pattern Fn₂ str x y   = Fn str x [y]
pattern Fn₃ str x y z = Fn str x [y, z]

ifThenElse ∷ Exp → Exp → Exp → Exp
ifThenElse = IfThenElse


putInt ∷ Exp → Exp
putInt = Fn₁ "putint" 

plusOne ∷ Exp → Exp
plusOne = Fn₁ "plusone"

add ∷ Exp → Exp → Exp
add = Fn₂ "add"
