{-# LANGUAGE DeriveDataTypeable #-}

import EDSL

import Prelude hiding ((.), id)
import Control.Category
import Control.Monad
import GHC.TypeLits
import Data.Data
import Generics.SYB.Text
import Control.Applicative

newtype Vec (n ∷ Nat) a = Vec [Expr a]

data Expr a where
  LIT ∷ Int → Expr Int
  ADD ∷ Expr Int → Expr Int → Expr Int
  ARR ∷ KnownNat n ⇒ Proxy n → (Int → Expr a) → Expr (Vec n a)

arr ∷ Expr (Vec 10 Int)
arr = ARR (Proxy ∷ Proxy 10) (join ADD . LIT)

-- ARR ∷ KnownNat n ⇒ Proxy n → (Expr Int → Expr a) → Expr (Vec n a)
-- ARR ∷ KnownNat n ⇒ Proxy n → (Expr Int → Expr a) → Expr (Vec n a)

evall ∷ ∀a. Expr a → a
evall = \case
  LIT i                     → i
  ADD e₁ e₂                 → evall e₁ + evall e₂
  ARR proxy ixf → let indices = [0..fromIntegral (natVal proxy) - 1 ∷ Int]
                   in Vec [ ixf (index) | index ← indices ]

foobar ∷ KnownNat n ⇒ Proxy n → SomeNat → Maybe (Proxy n)
foobar proxy₁ (SomeNat proxy₂) = proxy₁ <$ proxy₁ `sameNat` proxy₂

newtype f ↝ g = Nat { nu ∷ forall a. f a → g a }

instance Category ((↝) ∷ (★ → ★) → (★ → ★) → ★) where
  id = Nat id
  Nat f . Nat g = Nat (f . g)
