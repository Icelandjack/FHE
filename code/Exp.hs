-- https://hackage.haskell.org/package/feldspar-language-0.7/docs/src/Feldspar-Core-Types.html

module Exp where

import Text.Printf
import Control.Applicative
import Data.Functor.Identity
import Data.Bits
import GHC.Generics hiding (from, to)
import Numeric.Natural
import Data.Bifunctor

import Unsafe.Coerce

import Data.Bifoldable
import Control.Lens
import Bound
  
import Types
import Variable

-- Constants
pattern Tru ∷ b ~ Bool ⇒ Exp b
pattern Tru = LitB True

pattern Fls ∷ b ~ Bool ⇒ Exp b
pattern Fls = LitB False

-- Unary Operators
data UnOp a b where
  OpNot ∷ UnOp Bool Bool
  OpNeg ∷ UnOp Int  Int 

deriving instance Eq   (UnOp a b)
deriving instance Ord  (UnOp a b)
deriving instance Show (UnOp a b)

pattern Not ∷ (a → b) ~ (Bool → Bool) ⇒ Exp a → Exp b
pattern Not b       ← UnOp OpNot not TBool b where
        -- Not Tru     = Fls
        -- Not Fls     = Tru
        -- Not (Not a) = a
        Not b       = UnOp OpNot not TBool b

pattern Negate ∷ (a → b) ~ (Int → Int) ⇒ Exp a → Exp b
pattern Negate a        ← UnOp OpNeg negate TInt a where
        -- Negate (LitI b) = LitI (negate b)
        Negate a        = UnOp OpNeg negate TInt a

-- Binary Operators
data BinOp a b c where
  -- Arithmetic
  OpAdd ∷ BinOp Int Int Int 
  OpSub ∷ BinOp Int Int Int
  OpMul ∷ BinOp Int Int Int 

  -- Relational
  OpEqual         ∷ BinOp Int Int Bool
  OpNotEqual      ∷ BinOp Int Int Bool
  OpLessThan      ∷ BinOp Int Int Bool
  OpLessThanEq    ∷ BinOp Int Int Bool
  OpGreaterThan   ∷ BinOp Int Int Bool
  OpGreaterThanEq ∷ BinOp Int Int Bool

  -- Logical
  OpAnd ∷ BinOp Bool Bool Bool
  OpOr  ∷ BinOp Bool Bool Bool
  OpXor ∷ BinOp Int  Int  Int

deriving instance Eq   (BinOp a b c)
deriving instance Ord  (BinOp a b c)
deriving instance Show (BinOp a b c)

pattern Add ∷ (a → b → c) ~ (Int → Int → Int) ⇒ Exp a → Exp b → Exp c
pattern Add a        b        ← BinOp OpAdd (+) TInt a b where
        -- Add (LitI a) (LitI b) = LitI (a + b)
        Add a        b        = BinOp OpAdd (+) TInt a b

pattern Sub ∷ (a → b → c) ~ (Int → Int → Int) ⇒ Exp a → Exp b → Exp c
pattern Sub a        b        ← BinOp OpSub (-) TInt a b where
        -- Sub (LitI a) (LitI b) = LitI (a - b)
        Sub a        b        = BinOp OpSub (-) TInt a b

pattern Mul ∷ (a → b → c) ~ (Int → Int → Int) ⇒ Exp a → Exp b → Exp c
pattern Mul a b               ← BinOp OpMul (*) TInt a b where
        -- Mul (LitI a) (LitI b) = LitI (a * b)
        Mul a b               = BinOp OpMul (*) TInt a b

pattern Equal ∷ (a → b → c) ~ (Int → Int → Bool) ⇒ Exp a → Exp b → Exp c
pattern Equal a        b        ← BinOp OpEqual (==) TBool a b where
        -- Equal (LitI a) (LitI b) = LitB (a == b)
        Equal a        b        = BinOp OpEqual (==) TBool a b

pattern NotEqual ∷ (a → b → c) ~ (Int → Int → Bool) ⇒ Exp a → Exp b → Exp c
pattern NotEqual a        b        ← BinOp OpNotEqual (/=) TBool a b where
        -- NotEqual (LitI a) (LitI b) = LitB (a /= b)
        NotEqual a        b        = BinOp OpNotEqual (/=) TBool a b

pattern LessThan ∷ (a → b → c) ~ (Int → Int → Bool) ⇒ Exp a → Exp b → Exp c
pattern LessThan a        b        ← BinOp OpLessThan (<) TBool a b where
        -- LessThan (LitI a) (LitI b) = LitB (a < b)
        LessThan a        b        = BinOp OpLessThan (<) TBool a b

pattern LessThanEq ∷ (a → b → c) ~ (Int → Int → Bool) ⇒ Exp a → Exp b → Exp c
pattern LessThanEq a        b        ← BinOp OpLessThanEq (<=) TBool a b where
        -- LessThanEq (LitI a) (LitI b) = LitB (a <= b)
        LessThanEq a        b        = BinOp OpLessThanEq (<=) TBool a b

pattern GreaterThan ∷ (a → b → c) ~ (Int → Int → Bool) ⇒ Exp a → Exp b → Exp c
pattern GreaterThan a        b        ← BinOp OpGreaterThan (>) TBool a b where
        -- GreaterThan (LitI a) (LitI b) = LitB (a > b)
        GreaterThan a        b        = BinOp OpGreaterThan (>) TBool a b

pattern GreaterThanEq ∷ (a → b → c) ~ (Int → Int → Bool) ⇒ Exp a → Exp b → Exp c
pattern GreaterThanEq a        b        ← BinOp OpGreaterThanEq (>=) TBool a b where
        -- GreaterThanEq (LitI a) (LitI b) = LitB (a >= b)
        GreaterThanEq a        b        = BinOp OpGreaterThanEq (>=) TBool a b

pattern And ∷ (a → b → c) ~ (Bool → Bool → Bool) ⇒ Exp a → Exp b → Exp c
pattern And a        b        ← BinOp OpAnd (&&) TBool a b where
        -- And (LitB a) (LitB b) = LitB (a && b)
        And a        b        = BinOp OpAnd (&&) TBool a b

pattern Or ∷ (a → b → c) ~ (Bool → Bool → Bool) ⇒ Exp a → Exp b → Exp c
pattern Or a        b        ← BinOp OpOr (||) TBool a b where
        -- Or (LitB a) (LitB b) = LitB (a || b)
        Or a        b        = BinOp OpOr (||) TBool a b

pattern Xor ∷ (a → b → c) ~ (Int → Int → Int) ⇒ Exp a → Exp b → Exp c
pattern Xor a        b        ← BinOp OpXor xor TInt a b where
        -- Xor (LitI a) (LitI b) = LitI (xor a b)
        Xor a        b        = BinOp OpXor xor TInt a b

-- 

data Exp τ where
  LitI ∷ Int  → Exp Int
  LitB ∷ Bool → Exp Bool

  If  ∷ Exp Bool → Exp τ → Exp τ → Exp τ

  -- Operators
  UnOp  ∷ UnOp  a b   → (a → b)     → TypeRep b → (Exp a → Exp b)
  BinOp ∷ BinOp a b c → (a → b → c) → TypeRep c → (Exp a → Exp b → Exp c)

  -- While ∷ (Exp s → Exp Bool) → (Exp s → Exp s) → Exp s → Exp s
  While ∷ Name → Exp Bool → Exp s → Exp s → Exp s

  -- Arr   ∷ Type a ⇒ Exp Int → (Exp Int → Exp a) → Exp [a]
  Arr   ∷ Type a ⇒ Exp Int → Name → Exp a → Exp [a]
  Len   ∷ Type a ⇒ Exp [a] → Exp Int
  ArrIx ∷ Type a ⇒ Exp [a] → Exp Int → Exp a

  Pair  ∷ (Type a, Type b) ⇒ Exp a → Exp b → Exp (a, b)
  Fst   ∷ Exp (a, b) → Exp a
  Snd   ∷ Exp (a, b) → Exp b

  Var ∷ Name → Exp τ
  Lam ∷ Name → Exp b → Exp (a → b)
  App ∷ Exp (a → b) → Exp a → Exp b

while ∷ (Exp s → Exp Bool) → (Exp s → Exp s) → Exp s → Exp s
while cond loop init = While (Lambda n) condBody loopBody init where
  n        = 1 + max (maxLam condBody) (maxLam loopBody)
  condBody = cond (Var (Lambda n))
  loopBody = loop (Var (Lambda n))

arr ∷ Type a ⇒ Exp Int → (Exp Int → Exp a) → Exp [a]
arr len ixf = Arr len (Lambda n) body where
  n    = 1 + maxLam body
  body = ixf (Var (Lambda n))

maxLam ∷ Exp a → Natural
maxLam = \case
  Var{}                 → 0
  LitI{}                → 0
  App a b               → maxLam a `max` maxLam b
  UnOp  _ _ _ a         → maxLam a
  BinOp _ _ _ a b       → maxLam a `max` maxLam b

  -- Binding constructs
  Lam   (VarId n) _     → n 
  While (VarId n) _ _ _ → n 

  Pair a b              → maxLam a `max` maxLam b
  Fst a                 → maxLam a
  Snd a                 → maxLam a

  a                     → error ("maxLam: " ++ show a)

instance Show (Exp a) where
  show ∷ Exp a → String
  show = \case
    LitI i           → show i
    LitB False       → "fls"
    LitB True        → "tru"
    If c t e         → printf "(if %s %s %s)" (show c) (show t) (show e)

    UnOp  op _ _ x   → printf "%s(%s)" (show op) (show x)
    BinOp op _ _ x y → printf "(%s %s %s)" (show x) (show op) (show y)

    Arr l n ixf      → printf "(%s for v%s in 0…%s)" (show ixf) (show n) (show l)
    Len x            → printf "len(%s)" (show x)
    ArrIx arr i      → printf "%s[%s]" (show arr) (show i)
    Pair x y         → printf "⟨%s, %s⟩" (show x) (show y)
    Fst pair         → printf "fst(%s)" (show pair)
    Snd pair         → printf "snd(%s)" (show pair)

    Var n            → show n
    App a b          → printf "%s · %s" (show a) (show b)
    Lam n body       → printf "(%s ↦ %s)" (show n) (show body)
    
    While n c b i   → printf "while [%s = %s] (%s) { %s }" (show n) (show i) (show c) (show b)
    _               → undefined 

instance Num (Exp Int) where
  (+) ∷ Exp Int → Exp Int → Exp Int
  (+) = Add

  (-) ∷ Exp Int → Exp Int → Exp Int
  (-) = Sub

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

-- -- pattern Fst ∷ (a → b) ~ ((Int, Int) → Int) ⇒ Exp a → Exp b
-- -- pattern Fst x ← Fn₁ "fst" (TPair TInt TInt :→: TInt) _   x where
-- --         Fst x = Fn₁ "fst" (TPair TInt TInt :→: TInt) fst x where

-- -- pattern Snd ∷ (a → b) ~ ((Int, Int) → Int) ⇒ Exp a → Exp b
-- -- pattern Snd x ← Fn₁ "snd" (TPair TInt TInt :→: TInt) _   x where
-- --         Snd x = Fn₁ "snd" (TPair TInt TInt :→: TInt) snd x where

-- (⊔) ∷ Exp Int → Exp Int → Exp Int
-- a ⊔ b = If (a :≤: b) a b

-- swap ∷ Exp (Int, Int) → Exp (Int, Int)
-- swap (Pair a b) = Pair b a
-- swap xs         = Pair (Snd xs) (Fst xs)

-- -- (⊕) = Xor
-- -- (∧) = And

showTy ∷ Exp a → String
showTy = showTypeRep . getTy

getTy ∷ Exp a → TypeRep a
getTy = \case
  LitI{}             → typeRep
  LitB{}             → typeRep
  If _ e _           → getTy e
  Var{}              → error "Can't conjure up a type."
  UnOp op _ res _    → res
  BinOp op _ res _ _ → res
  Len{}              → TInt
  ArrIx arr _        → case getTy arr of
    TArr a → a
  Pair a b           → TPair (getTy a) (getTy b)
  Fst a              → case getTy a of
    TPair a b → a
  Snd a              → case getTy a of
    TPair a b → b
  While _ _ a b      → getTy a
  Arr _ _ ixf        → typeRep

-- -- renameVar ∷ Name → Name → 

-- eval ∷ Exp a → a
-- eval = \case
--   LitI a   → a
--   LitB b   → b
--   Not b    → not (eval b)
--   Pair a b → (eval a, eval b)
--   Fst a    → fst (eval a)
--   Snd a    → snd (eval a)
--   Add a b  → eval a + eval b
--   a :≤: b  → eval a <= eval b
--   And a b  → eval a && eval b
--   Mul a b  → eval a * eval b
--   Xor a b  → xor (eval a) (eval b)
--   If c a b 
--     | eval c    → eval a
--     | otherwise → eval b
--   -- Arr len ixf → let
--   --   ℓ  = eval len
--   --   is = [0..ℓ-1]
--   --   in [ eval (ixf (LitI x)) | x ← is ]
--   a → error ("ERROR: " ++ show a)

-- {-
-- λ ∷ (Exp a → Exp b) → Exp (a → b)
-- λ f = Lam (Lambda n) body where
--   n    = 1 + maxLam body
--   body = f (Var (Lambda n))

-- λ₂ ∷ (Exp a → Exp b → Exp c) → Exp (a → b → c)
-- λ₂ f = λ $ \x → 
--        λ $ \y → f x y 

-- λ₃ ∷ (Exp a → Exp b → Exp c → Exp d) → Exp (a → b → c → d)
-- λ₃ f = λ $ \x → 
--        λ $ \y → 
--        λ $ \z → f x y z

-- (·) = App
-- -}

instance HasVars (Exp a) (Exp a) Natural Natural where
  var ∷ Traversal (Exp a) (Exp a) Natural Natural
  var f = \case
    Var v  → Var <$> var f v

    LitI i → pure (LitI i)
    LitB b → pure (LitB b)

    If a b c → If <$> traverseOf var f a <*> traverseOf var f b <*> traverseOf var f c
