module Exp where

import Text.Printf
import Control.Applicative
import Data.Functor.Identity
import Data.Bits
import GHC.Generics hiding (from, to)

import Bound
  
import Types

-- https://hackage.haskell.org/package/feldspar-language-0.7/docs/src/Feldspar-Core-Types.html

-- data Name 
--   = Index Int
--   | VarName String
--   deriving Show

type Name = Int

data Exp τ where
  LitI ∷ Int  → Exp Int
  LitB ∷ Bool → Exp Bool

  If  ∷ Exp Bool → Exp τ → Exp τ → Exp τ

  Fn₁ ∷ String 
      → TypeRep (a → b)
      → (a → b)
      → (Exp a → Exp b)

  Fn₂ ∷ String 
      → TypeRep (a → b → c)
      → (a → b → c) 
      → (Exp a → Exp b → Exp c)

  -- While ∷ (Exp s → Exp Bool) → (Exp s → Exp s) → Exp s → Exp s
  While ∷ Name → Exp Bool → Exp s → Exp s → Exp s

  -- Arr   ∷ Type a ⇒ Exp Int → (Exp Int → Exp a) → Exp [a]
  Arr   ∷ Exp Int → Name → Exp a → Exp [a]
  Len   ∷ Type a ⇒ Exp [a] → Exp Int
  ArrIx ∷ Type a ⇒ Exp [a] → Exp Int → Exp a

  Pair  ∷ (Type a, Type b) ⇒ Exp a → Exp b → Exp (a, b)
  Fst   ∷ Exp (a, b) → Exp a
  Snd   ∷ Exp (a, b) → Exp b

  Var ∷ Name → Exp τ
  Lam ∷ Name → Exp b → Exp (a → b)
  App ∷ Exp (a → b) → Exp a → Exp b

while ∷ (Exp s → Exp Bool) → (Exp s → Exp s) → Exp s → Exp s
while cond loop init = While n condBody loopBody init where
  n        = 1 + max (maxLam condBody) (maxLam loopBody)
  condBody = cond (Var n)
  loopBody = loop (Var n)

arr ∷ Exp Int → (Exp Int → Exp a) → Exp [a]
arr len ixf = Arr len n body where
  n    = 1 + maxLam body
  body = ixf (Var n)

λ ∷ (Exp a → Exp b) → Exp (a → b)
λ f = Lam n body where
  n    = 1 + maxLam body
  body = f (Var n)

λ₂ ∷ (Exp a → Exp b → Exp c) → Exp (a → b → c)
λ₂ f = λ $ \x → 
       λ $ \y → f x y 

λ₃ ∷ (Exp a → Exp b → Exp c → Exp d) → Exp (a → b → c → d)
λ₃ f = λ $ \x → 
       λ $ \y → 
       λ $ \z → f x y z

(·) = App

maxLam ∷ Exp a → Name
maxLam = \case
  Var{}         → 0
  LitI{}        → 0
  App a b       → maxLam a `max` maxLam b
  Fn₁ _ _ _ a   → maxLam a
  Fn₂ _ _ _ a b → maxLam a `max` maxLam b

  -- Binding constructs
  Lam   n _     → n
  While n _ _ _ → n

  a             → error $ "maxLam: " ++ show a

instance Show (Exp a) where
  show ∷ Exp a → String
  show = \case
    LitI i          → show i
    LitB False      → "fls"
    LitB True       → "tru"
    If c t e        → printf "(if %s %s %s)" (show c) (show t) (show e)
    Fn₁ str _   _ x → printf "%s(%s)" str (show x)
    Fn₂ str _ _ x y → printf "(%s %s %s)" (show x) str (show y)
    Arr l n ixf     → printf "(%s for v%s in 0…%s)" (show ixf) (show n) (show l)
    Len x           → printf "len(%s)" (show x)
    ArrIx arr i     → printf "%s[%s]" (show arr) (show i)
    Pair x y        → printf "⟨%s, %s⟩" (show x) (show y)
    Fst pair        → printf "fst(%s)" (show pair)
    Snd pair        → printf "snd(%s)" (show pair)

    Var n           → "v" ++ show n
    App a b         → printf "%s · %s" (show a) (show b)
    Lam n body      → printf "(v%d ↦ %s)" n (show body)
    
    While n c b i   → printf "while [v%d = %s] (%s) { %s }" n (show i) (show c) (show b)
    _               → undefined 

instance Num (Exp Int) where
  (+) ∷ Exp Int → Exp Int → Exp Int
  (+) = Add

  (*) ∷ Exp Int → Exp Int → Exp Int
  (*) = Mul

  negate ∷ Exp Int → Exp Int
  negate = Negate

  fromInteger ∷ Integer → Exp Int
  fromInteger i = LitI (fromInteger i)

-- The types of the following type synonyms aren't
--   pattern Tru ∷ Exp Bool
--   pattern Add ∷ Exp Int → Exp Int → Exp Int
-- because of https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/syntax-extns.html#idp23521760
-- See trac issue #10405.
pattern Add ∷ (a → b → c) ~ (Int → Int → Int) ⇒ Exp a → Exp b → Exp c
pattern Add a        b        ← Fn₂ "+" Ints₂ _   a b where
        Add (LitI a) (LitI b) = LitI (a + b)
        Add a        b        = Fn₂ "+" Ints₂ (+) a b

pattern Mul ∷ (a → b → c) ~ (Int → Int → Int) ⇒ Exp a → Exp b → Exp c
pattern Mul a b               ← Fn₂ "*" Ints₂ _   a b where
        Mul (LitI a) (LitI b) = LitI (a * b)
        Mul a b               = Fn₂ "*" Ints₂ (*) a b

pattern Negate ∷ (a → b) ~ (Int → Int) ⇒ Exp a → Exp b
pattern Negate a        ← Fn₁ "negate" Ints₁ _      a where
        Negate (LitI b) = LitI (negate b)
        Negate a        = Fn₁ "negate" Ints₁ negate a

pattern Xor ∷ (a → b → c) ~ (Int → Int → Int) ⇒ Exp a → Exp b → Exp c
pattern Xor a        b        ← Fn₂ "xor" Ints₂ _   a b where
        Xor (LitI a) (LitI b) = LitI (xor a b)
        Xor a        b        = Fn₂ "xor" Ints₂ xor a b

pattern Not ∷ (a → b) ~ (Bool → Bool) ⇒ Exp a → Exp b
pattern Not b ← Fn₁ "not" Bools₁ _   b where
        Not Tru     = Fls
        Not Fls     = Tru
        Not (Not a) = a
        Not b       = Fn₁ "not" Bools₁ not b

pattern And ∷ (a → b → c) ~ (Bool → Bool → Bool) ⇒ Exp a → Exp b → Exp c
pattern And a        b        ← Fn₂ "and" Bools₂ _    a b where
        And (LitB a) (LitB b) = LitB (a && b)
        And a        b        = Fn₂ "and" Bools₂ (&&) a b

pattern (:≤:) ∷ (a → b → c) ~ (Int → Int → Bool) ⇒ Exp a → Exp b → Exp c
pattern a      :≤: b      ← Fn₂ "≤" (TInt :→: TInt :→: TBool) _    a b where
        LitI a :≤: LitI b = LitB (a <= b)
        a      :≤: b      = Fn₂ "≤" (TInt :→: TInt :→: TBool) (<=) a b

pattern (:<:) ∷ (a → b → c) ~ (Int → Int → Bool) ⇒ Exp a → Exp b → Exp c
pattern a      :<: b      ← Fn₂ "<" (TInt :→: TInt :→: TBool) _    a b where
        LitI a :<: LitI b = LitB (a < b)
        a      :<: b      = Fn₂ "<" (TInt :→: TInt :→: TBool) (<) a b

pattern (:=:) ∷ (a → b → c) ~ (Int → Int → Bool) ⇒ Exp a → Exp b → Exp c
pattern a      :=: b      ← Fn₂ "=" (TInt :→: TInt :→: TBool) _    a b where
        LitI a :=: LitI b = LitB (a == b)
        a      :=: b      = Fn₂ "=" (TInt :→: TInt :→: TBool) (==) a b

-- pattern Fst ∷ (a → b) ~ ((Int, Int) → Int) ⇒ Exp a → Exp b
-- pattern Fst x ← Fn₁ "fst" (TPair TInt TInt :→: TInt) _   x where
--         Fst x = Fn₁ "fst" (TPair TInt TInt :→: TInt) fst x where

-- pattern Snd ∷ (a → b) ~ ((Int, Int) → Int) ⇒ Exp a → Exp b
-- pattern Snd x ← Fn₁ "snd" (TPair TInt TInt :→: TInt) _   x where
--         Snd x = Fn₁ "snd" (TPair TInt TInt :→: TInt) snd x where

pattern Tru ∷ b ~ Bool ⇒ Exp b
pattern Tru = LitB True

pattern Fls ∷ b ~ Bool ⇒ Exp b
pattern Fls = LitB False

(⊔) ∷ Exp Int → Exp Int → Exp Int
a ⊔ b = If (a :≤: b) a b

swap ∷ Exp (Int, Int) → Exp (Int, Int)
swap xs = Pair (Snd xs) (Fst xs)

-- --     While a b i    → printf "(st = %s;\n" (show i)
-- --                   ++ printf "  while (%s) {\n" (show (a (Var "st")))
-- --                   ++ printf "    st = %s;\n" (show (b (Var "st")))
-- --                   ++ printf "})\n"
-- --     Lam{}          → error "LAM"
    
(⊕) = Xor
(∧) = And

showTy ∷ Exp a → String
showTy = showTypeRep . getTy

getTy ∷ Exp a → TypeRep a
getTy = \case
  LitI{}          → typeRep
  LitB{}          → typeRep
  If _ e _        → getTy e
  Var{}           → error "Can't conjure up a type."
  Fn₁ _ res _ _   → resType res
  Fn₂ _ res _ _ _ → resType (resType res)
  Len{}           → TInt
  ArrIx arr _     → case getTy arr of
    TArr a        → a
  Pair a b        → TPair (getTy a) (getTy b)
  Fst a           → case getTy a of
    TPair a b → a
  Snd a           → case getTy a of
    TPair a b → b
  While _ _ a b → getTy a
  -- Arr _ ixf       → typeRep

-- comp' ∷ Applicative f ⇒ (Exp → f Exp) → (Exp → f Exp)
-- comp' f = \case
--   I i             → pure    $  I i
--   Var a           → pure    $  Var a
--   -- Add a b         → Add    <$> f a   <*> f b
--   -- Mul a b         → Mul    <$> f a   <*> f b
--   If a b c        → If     <$> f a   <*> f b             <*> f c
--   Fn str exp exps → Fn str <$> f exp <*> traverse f exps
--   Lam a b         → Lam a  <$> f b

-- compI ∷ (Exp → Exp) → (Exp → Exp)
-- compI f x = runIdentity (comp' (Identity . f) x)

-- appVar ∷ Exp → Exp
-- appVar (Var x) = Var ("_" ++ x)
-- appVar e       = compI appVar e

eval ∷ Exp a → a
eval = \case
  LitI a   → a
  LitB b   → b
  Not b    → not (eval b)
  Pair a b → (eval a, eval b)
  Fst a    → fst (eval a)
  Snd a    → snd (eval a)
  Add a b  → eval a + eval b
  a :≤: b  → eval a <= eval b
  And a b  → eval a && eval b
  Mul a b  → eval a * eval b
  Xor a b  → xor (eval a) (eval b)
  If c a b 
    | eval c    → eval a
    | otherwise → eval b
  -- Arr len ixf → let
  --   ℓ  = eval len
  --   is = [0..ℓ-1]
  --   in [ eval (ixf (LitI x)) | x ← is ]
  a → error ("ERROR: " ++ show a)

