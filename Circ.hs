module Circ where

import Data.Bits
import Control.Monad.State
import Control.Applicative
import Test.QuickCheck

data N = Z | S N

data CIRC a where
  Var ∷ a → CIRC a
  Xor ∷ CIRC a → CIRC a → CIRC a
  And ∷ CIRC a → CIRC a → CIRC a
  -- Neg ∷ CIRC a → CIRC a
  -- Or  ∷ CIRC a → CIRC a → CIRC a
  Let ∷ (a → CIRC a) → CIRC a

newtype Circ = Circ (∀a. CIRC a)

-- infixr 2 ∨
-- (∨) = Or

infixr 3 ∧
(∧) = And

infixr 3 ⊕
(⊕) = Xor

-- (¬) = Neg

let₁ ∷ (CIRC a → CIRC a) → CIRC a
let₁ fx = Let (\x → fx (Var x))

let₂ ∷ (CIRC a → CIRC a → CIRC a) → CIRC a
let₂ fx = Let (\x → Let (\y → fx (Var x) (Var y)))

let₃ ∷ (CIRC a → CIRC a → CIRC a → CIRC a) → CIRC a
let₃ fx = Let (\x → Let (\y → Let (\z → fx (Var x) (Var y) (Var z))))

-- xor ∷ Circ 
-- xor = Circ $ let₂ (\x y → x ∧ (y¬) ∨ (x¬) ∧ y)

-- maj ∷ Circ
-- maj = Circ $ let₃ $ \x y z →
--   x∧y ∨ y∧z ∧ x∨z

instance Show Circ where
  show (Circ c) = evalState (foo c) [ [ch] | ch ← ['a'..] ]


pop ∷ MonadState [a] m => m a
pop = do
  x ← gets head
  modify tail
  return x

foo ∷ CIRC String → State [String] String
foo = \case
  Var a   → return $ a
  And a b → do
    a' ← foo a
    b' ← foo b
    return $ "(" ++ a' ++ "∧" ++ b' ++ ")"
  Xor a b → do
    a' ← foo a
    b' ← foo b
    return $ "(" ++ a' ++ "⊕" ++ b' ++ ")"
  Let f → do
    ident ← pop
    foo (f ident)
  -- Neg a   → do
  --   a' ← foo a
  --   return $ "(¬" ++ a' ++ ")"
  -- Or a b → do
  --   a' ← foo a
  --   b' ← foo b
  --   return $ "(" ++ a' ++ "∨" ++ b' ++ ")"

(†) ∷ Num n ⇒ Circ → [n] → n
(†) (Circ circuit) cs = evalState (blah circuit) cs

blah ∷ Num n ⇒ CIRC n → State [n] n
blah = \case
  Var a   → return a
  Xor a b → (+) <$> blah a <*> blah b
  And a b → (*) <$> blah a <*> blah b
  Let f   → do
    var ← pop
    blah (f var)

instance Arbitrary Circ where
  arbitrary = do
    op ← arbitrary
    return $ Circ $ let₂ (if op then (∧) else (⊕))

bar ∷ CIRC a → CIRC a → CIRC a
bar = (∧)

a = Circ (let₂ bar)

-- b = do
--   undefined