module Expr where

import Text.Printf
import Control.Applicative
import Data.Functor.Identity
import Data.Bits
import GHC.Generics hiding (from, to)

pattern Fn₁ str x     = Fn str x []
pattern Fn₂ str x y   = Fn str x [y]
pattern Fn₃ str x y z = Fn str x [y, z]

pattern Add x y = Fn₂ "+" x y
pattern Mul x y = Fn₂ "*" x y
pattern Xor x y = Fn₂ "⊕" x y
pattern And x y = Fn₂ "∧" x y
pattern x :≤: y = Fn₂ "≤" x y

pattern x :+: y = Add x y
pattern x :×: y = Mul x y 

(⊔) ∷ Exp → Exp → Exp
a ⊔ b = If (a :≤: b) a b

data Foo a = MkFoo a deriving (Generic, Generic1)

pattern T = B True
pattern F = B False

data Exp 
  = I Integer
  | B Bool
  | If Exp Exp Exp 
  | Var String
  | Fn String Exp [Exp]
  | Lam String Exp
  -- |     s     Bool  s     s     s 
  | While (Exp → Exp) (Exp → Exp) Exp

  | Arr   Exp (Exp → Exp)
  | Len   Exp
  | ArrIx Exp Exp
    deriving (Generic)

class Repr exp where
  to   ∷ exp → Exp
  from ∷ Exp → exp

instance Repr Exp where
  from ∷ Exp → Exp
  from = id

  to ∷ Exp → Exp
  to = id

while ∷ Repr st ⇒ (st → Exp) → (st → st) → st → st
while c b i = from (While (c . from) (to . b . from) (to i))

instance Show Exp where
  show = \case
    I i            → show i
    B b            → show b
    If c t e       → printf "(if %s %s %s)" (show c) (show t) (show e)
    Var str        → str
    Fn₁ str x      → printf "%s(%s)" str (show x)
    -- Add     x y → printf "(%s + %s)" (show x) (show y)
    -- Mul     x y → printf "(%s * %s)" (show x) (show y)
    -- Xor     x y → printf "(%s ⊕ %s)" (show x) (show y)
    Fn₂ str x y    → printf "(%s %s %s)" (show x) str (show y)
    Fn₃ str x y z  → printf "%s(%s, %s, %s)" str (show x) (show y) (show z)
    Arr l ixf      → printf "(%s for i in 0…%s)" (show (ixf (Var "i"))) (show l)
    Len x          → printf "len(%s)" (show x)
    While a b i    → printf "(st = %s;\n" (show i)
                  ++ printf "  while (%s) {\n" (show (a (Var "st")))
                  ++ printf "    st = %s;\n" (show (b (Var "st")))
                  ++ printf "})\n"
    ArrIx arr i    → printf "%s[%s]" (show arr) (show i)
    Lam{}          → error "LAM"
    

comp' ∷ Applicative f ⇒ (Exp → f Exp) → (Exp → f Exp)
comp' f = \case
  I i             → pure    $  I i
  Var a           → pure    $  Var a
  -- Add a b         → Add    <$> f a   <*> f b
  -- Mul a b         → Mul    <$> f a   <*> f b
  If a b c        → If     <$> f a   <*> f b             <*> f c
  Fn str exp exps → Fn str <$> f exp <*> traverse f exps
  Lam a b         → Lam a  <$> f b

compI ∷ (Exp → Exp) → (Exp → Exp)
compI f x = runIdentity (comp' (Identity . f) x)

appVar ∷ Exp → Exp
appVar (Var x) = Var ("_" ++ x)
appVar e       = compI appVar e

instance Num Exp where
  (+) ∷ Exp → Exp → Exp
  (+) = Add
  -- a + b = Fn₂ "add" a b

  (*) ∷ Exp → Exp → Exp
  (*) = Mul
  -- a * b = Mul a b

  negate ∷ Exp → Exp
  negate (I n) = I (-n)

  fromInteger ∷ Integer → Exp
  fromInteger i = I (fromInteger i)

ifThenElse ∷ Exp → Exp → Exp → Exp
ifThenElse = If

putInt ∷ Exp → Exp
putInt = Fn₁ "putint" 

plusOne ∷ Exp → Exp
plusOne = Fn₁ "plusone"

(⊕) = Xor
(∧) = And
