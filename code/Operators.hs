module Operators where

import Types
import Variable (Name)
import Data.Int (Int8, Int32)

------------------------------------------------------------------------
-- Unary operators                                                    --
------------------------------------------------------------------------

-- Contains everything needed to work with operators, neatly
-- separating the type, Haskell function, operation × show instance.

-- To form the negation operator, in Haskell
-- 
--     not ∷ Bool → Bool
-- 
-- we use the symbolic 
-- 
--     OpNot ∷ UnOp Bool Bool
-- 
-- we can show the operator
-- 
--     >>> OpNot
--     ¬
-- 
-- Using 'Un' we associate it with its Haskell function
-- 
--     Un OpNot not ∷ Unary Bool Bool
-- 
-- Some representations are overloaded, 'OpNeg' works on any numeric
-- type:
--   
--     OpNeg ∷ NumberType a → UnOp a a
-- 
-- So we have
-- 
--     OpNeg (NumberType INT8)  ∷ UnOp Int8 Int8
--     OpNeg (NumberType INT32) ∷ UnOp Int8 Int32
-- 
-- We can hijack Haskell's ad-hoc polymorphism using
-- 
--     OpNeg getNumber ∷ GetNumber a ⇒ UnOp a a
-- 
-- 
data Construct a where
  Con ∷ GetType a ⇒ ConOp a → a → Construct a

data ConOp a where
  VarOp ∷ Name → ConOp a

data Unary a b where
  Un ∷ (GetType a, GetType b) ⇒ UnOp a b → (a → b) → Unary a b

data UnOp a b where
  OpNot ∷ UnOp Bool Bool
  OpNeg ∷ NumberType a → UnOp a    a

  OpFst ∷ UnOp (a, b) a
  OpSnd ∷ UnOp (a, b) b

  OpLen ∷ UnOp [a] Int32

instance Show (Unary a b) where
  show (Un op _function) = show op

instance Show (UnOp a b) where
  show = \case
    OpNot   → "¬"
    OpNeg _ → "-"

    OpFst   → "fst"
    OpSnd   → "snd"

    OpLen   → "len"

------------------------------------------------------------------------
-- Binary operators                                                   --
------------------------------------------------------------------------
data Binary a b c where
  Bin ∷ (GetType a, GetType b, GetType c) 
      ⇒ BinOp a b c 
      → (a → b → c) 
      → Binary a b c

data BinOp a b c where
  -- Arithmetic
  OpAdd ∷ NumberType a → BinOp a a a
  OpSub ∷ NumberType a → BinOp a a a
  OpMul ∷ NumberType a → BinOp a a a

  -- Relational
  OpEqual         ∷ ScalarType a → BinOp a a Bool
  OpNotEqual      ∷ ScalarType a → BinOp a a Bool
  OpLessThan      ∷ ScalarType a → BinOp a a Bool
  OpLessThanEq    ∷ ScalarType a → BinOp a a Bool
  OpGreaterThan   ∷ ScalarType a → BinOp a a Bool
  OpGreaterThanEq ∷ ScalarType a → BinOp a a Bool

  -- Logical
  OpAnd ∷ BinOp Bool Bool Bool
  OpOr  ∷ BinOp Bool Bool Bool
  OpXor ∷ BinOp Int8 Int8 Int8

  OpPair  ∷ BinOp a b (a, b)
  OpArr   ∷ Name → BinOp Int32 a [a]
  OpArrIx ∷ BinOp [a] Int32 a

instance Show (Binary a b c) where
  show (Bin op _function) = show op

instance Show (BinOp a b c) where
  show = \case
    OpAdd num         → "+" ++ showNumTypeSubscript num
    OpSub num         → "-" ++ showNumTypeSubscript num
    OpMul num         → "*" ++ showNumTypeSubscript num
    OpEqual{}         → "="
    OpNotEqual{}      → "≠"
    OpLessThan{}      → "<"
    OpLessThanEq{}    → "≤"
    OpGreaterThan{}   → ">"
    OpGreaterThanEq{} → "≥"
    OpAnd             → "∧"
    OpOr              → "∨"
    OpXor             → "⊕"
    OpPair            → "×"
    OpArr name        → "array_" ++ show name
    OpArrIx           → "‼"

------------------------------------------------------------------------
-- Ternary operators                                                  --
------------------------------------------------------------------------
data Ternary a b c d where
  Ter ∷ (GetType a, GetType b, GetType c, GetType d)
      ⇒ TernOp a b c d 
      → (a → b → c → d) 
      → Ternary a b c d

data TernOp a b c d where
  OpIf    ∷ TernOp Bool a a a
  OpWhile ∷ Name → TernOp Bool s s s

instance Show (Ternary a b c d) where
  show (Ter op _function) = show op

instance Show (TernOp a b c d) where
  show = \case
    OpIf{}    → "if"
    OpWhile{} → "while"

-- unOpType ∷ UnOp a b → Type b
-- unOpType = \case
--   OpNot                 → getType
--   OpNeg (NumberType ty) → Type ty
--   OpFst  → getType
  
--   _ → undefined 
