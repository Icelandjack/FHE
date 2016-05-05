{-# LANGUAGE UndecidableInstances #-} -- TODO Remove later

module Operators where

import Variable
import Types

import Data.Int
import Numeric.Natural

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
--     OpNeg ∷ GetNum ty _num -> UnOp a a
-- 
-- So we have
-- 
--     OpNeg ∷ UnOp Int8 Int8
--     OpNeg ∷ UnOp Int  Int
-- 
-- We can hijack Haskell's ad-hoc polymorphism using
-- 
--     OpNeg getNumber ∷ GetNumber a ⇒ UnOp a a
-- 
-- 
-- data Construct a where
--   Con ∷ GetType a ⇒ ConOp a → Construct a

-- data ConOp a where
--   VarOp ∷  VAR' a → ConOp a

-- class    GetTy ty (ToTYPE ty) => GETTY ty where getTy_ :: Ty ty
-- instance GetTy ty (ToTYPE ty) => GETTY ty where getTy_ = getTy

-- class GETTY ty                                               => GETSCA ty where getSca_ :: Ty ty
-- instance (ToTYPE ty ~ MKSCALAR rep, GetTy ty (MKSCALAR rep)) => GETSCA ty where getSca_ = getSca

-- class    (Num ty, GETSCA ty)                                                         => GETNUM ty where getNum_ :: Ty ty
-- instance (Num ty, ToTYPE ty ~ MKSCALAR (MKNUM rep), GetTy ty (MKSCALAR (MKNUM rep))) => GETNUM ty where getNum_ = getNum

data Unary a b where
  Un ∷ (GetTy a, GetTy b) 
     ⇒ UnOp a b 
     → (a → b) 
     → Unary a b

data UnOp a b where
  OpNot ∷ UnOp Bool Bool
  OpNeg ∷ GetNum a => UnOp a a

  OpFst ∷ (GetTy p1, GetTy p2) => UnOp (p1, p2) p1
  OpSnd ∷ (GetTy p1, GetTy p2) => UnOp (p1, p2) p2

  OpLen ∷ GetTy a => UnOp [a] Int

instance Show (Unary a b) where
  show (Un op _function) = show op

instance Show (UnOp a b) where
  show = \case
    OpNot → "¬"
    OpNeg → "-"

    OpFst → "fst"
    OpSnd → "snd"

    OpLen → "len"

------------------------------------------------------------------------
-- Binary operators                                                   --
------------------------------------------------------------------------
data Binary a b c where
  Bin ∷ (GetTy a, GetTy b, GetTy c) 
      ⇒ BinOp a b c 
      → (a → b → c) 
      → Binary a b c

data BinOp a b c where
  -- Arithmetic
  OpAdd ∷ GetNum a => BinOp a a a
  OpSub ∷ GetNum a => BinOp a a a
  OpMul ∷ GetNum a => BinOp a a a

  -- Relational
  OpEqual         ∷ GetSca a => BinOp a a Bool
  OpNotEqual      ∷ GetSca a => BinOp a a Bool
  OpLessThan      ∷ GetSca a => BinOp a a Bool
  OpLessThanEq    ∷ GetSca a => BinOp a a Bool
  OpGreaterThan   ∷ GetSca a => BinOp a a Bool
  OpGreaterThanEq ∷ GetSca a => BinOp a a Bool

  -- Logical
  OpAnd ∷ BinOp Bool Bool Bool
  OpOr  ∷ BinOp Bool Bool Bool
  -- OpXor ∷ GetNum a => BinOp a a a
  OpXor ∷ GetTy a => BinOp a a a

  OpPair  ∷ (GetTy p1, GetTy p2) => BinOp p1 p2 (p1, p2)
  OpArr   ∷ Id → BinOp Int a [a]
  OpArrIx ∷ GetTy a => BinOp [a] Int a

instance Show (Binary a b c) where
  show (Bin op _function) = show op

instance Show (BinOp a b c) where
  show = \case
    OpAdd             → "+" ++ subscript (getNum @a)
    OpSub             → "-" ++ subscript (getNum @a)
    OpMul             → "*" ++ subscript (getNum @a)
    OpEqual{}         → "="
    OpNotEqual{}      → "≠"
    OpLessThan{}      → "<"
    OpLessThanEq{}    → "≤"
    OpGreaterThan{}   → ">"
    OpGreaterThanEq{} → "≥"
    OpAnd             → "∧"
    OpOr              → "∨"
    OpXor             → "⊕" -- ++ subscript (getNum @a)
    OpPair            → "×"
    OpArr name        → "array_" ++ show name
    OpArrIx           → "‼"

------------------------------------------------------------------------
-- Ternary operators                                                  --
------------------------------------------------------------------------
data Ternary a b c d where
  Ter ∷ (GetTy a, GetTy b, GetTy c, GetTy d)
      ⇒ TernOp a b c d 
      → (a → b → c → d) 
      → Ternary a b c d

data TernOp a b c d where
  OpIf    ∷ TernOp Bool a a a
  OpWhile ∷ Id → TernOp Bool s s s

instance Show (Ternary a b c d) where
  show (Ter op _function) = show op

instance Show (TernOp a b c d) where
  show = \case
    OpIf{}    → "if"
    OpWhile{} → "while"
