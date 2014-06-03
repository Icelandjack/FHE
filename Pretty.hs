{-# LANGUAGE PatternSynonyms, LambdaCase, DeriveDataTypeable, PolyKinds, ConstraintKinds, DefaultSignatures #-}

import EDSL
import Text.Printf
import GHC.Exts

data Dict ctx where
  Dict ∷ ctx ⇒ Dict ctx
  
data a ⊢ b where
  Sub ∷ (a ⇒ Dict b) → a ⊢ b

class Instance h where
  type Context h ∷ Constraint
  type Context h = ()

  inst ∷ Context h ⊢ h

instance Instance (Eq (a, b))  where
  type Context (Eq (a, b)) = (Eq a, Eq b)
  inst = Sub Dict

instance Instance (Show (a, b))  where
  type Context (Show (a, b)) = (Show a, Show b)
  -- inst ∷ Context h        ⊢ h
  -- inst ∷ (Show a, Show b) ⊢ Show (a, b)
  inst = Sub Dict

ppr ∷ Exp a → String
ppr = \case
  Var x         → show x
  Value val     → show val
  If cond e t   → printf "(If %s %s %s)" (ppr cond) (ppr e) (ppr t)
  Lit num       → undefined -- show num
  LitB bool     → show bool
  Pair e₁ e₂    → printf "(Pair %s %s)" (ppr e₁) (ppr e₂)
  Fst pair      → printf "(Fst %s)" (ppr pair)
  Snd pair      → printf "(Snd %s)" (ppr pair)
  Prim1 f _ a   → f ++ " (" ++ ppr a ++ ")"
  Prim2 f _ a b → f ++ " (" ++ ppr a ++ ") (" ++ ppr b ++ ")"
  Conv word     → printf "(Conv %s)" (ppr word)
  
--   Conv :: (Exp GHC.Word.Word8) -> Exp Int
--   (:<) :: Ord a => (Exp a) -> (Exp a) -> Exp Bool
--   (:<=) :: Ord a => (Exp a) -> (Exp a) -> Exp Bool
--   (:>=) :: Ord a => (Exp a) -> (Exp a) -> Exp Bool
--   (:==) :: (Show a, Eq a) => (Exp a) -> (Exp a) -> Exp Bool
--   (:-) :: Num a => (Exp a) -> (Exp a) -> Exp a
--   (:+) :: Num a => (Exp a) -> (Exp a) -> Exp a
--   (:*) :: Num a => (Exp a) -> (Exp a) -> Exp a
--   (:||) :: (Exp Bool) -> (Exp Bool) -> Exp Bool
--   Arr :: (Exp Int) -> (Exp Int -> Exp a) -> Exp [a]
--   ArrLen :: (Exp [a]) -> Exp Int
--   ArrIx :: (Exp [a]) -> (Exp Int) -> Exp a
--   Table :: [Exp GHC.Word.Word8] -> Exp [GHC.Word.Word8]
--   Undef :: Exp a
--   GetBit :: (Exp GHC.Word.Word8) -> (Exp Int) -> Exp GHC.Word.Word8
--   	-- Defined at EDSL.hs:54:1
-- instance (Eq a, Num a) => Eq (Exp a) -- Defined at EDSL.hs:230:10
-- instance Num a => Num (Exp a) -- Defined at EDSL.hs:173:10
-- instance Show a => Show (Exp a) -- Defined at EDSL.hs:97:10
-- instance Embed (Exp a) -- Defined at EDSL.hs:113:10
-- type Repr (Exp a) -- Defined at EDSL.hs:114:3
-- ghci> 
--   Lambda :: (Exp a -> Exp b) -> (Exp a) -> Exp b
--   (:·) :: (Exp (a -> b)) -> (Exp a) -> Exp b
--   Let :: String -> Exp (a -> (a -> b) -> b)
--   While :: (Exp s -> Exp Bool) -> (Exp s -> Exp s) -> (Exp s) -> Exp

pprIO ∷ Show a ⇒ Exp a → IO ()
pprIO = putStrLn . ppr

