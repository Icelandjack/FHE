{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures, TypeApplications, DataKinds, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE UnicodeSyntax, RankNTypes, LambdaCase #-}
{-# LANGUAGE UndecidableInstances, AllowAmbiguousTypes #-}

{-# LANGUAGE FlexibleInstances, TypeFamilyDependencies, ConstraintKinds, BangPatterns, DataKinds, DeriveDataTypeable, DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable #-}
{-# LANGUAGE DefaultSignatures, DisambiguateRecordFields, EmptyCase, FunctionalDependencies, GADTs, GeneralizedNewtypeDeriving, InstanceSigs, ImplicitParams #-}
{-# LANGUAGE ImpredicativeTypes, LambdaCase, LiberalTypeSynonyms, MagicHash, MultiParamTypeClasses, MultiWayIf, MonadComprehensions, NamedFieldPuns #-}
{-# LANGUAGE NamedWildCards, NumDecimals, NoMonomorphismRestriction, ParallelListComp, PartialTypeSignatures, PatternSynonyms, PolyKinds, PostfixOperators #-}
{-# LANGUAGE RankNTypes, RecordWildCards, RecursiveDo, RoleAnnotations, ScopedTypeVariables, StandaloneDeriving, TemplateHaskell, TupleSections #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UnboxedTuples, UnicodeSyntax, ViewPatterns, QuasiQuotes, TypeInType, ApplicativeDo #-}
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
     → (ToType a → ToType b) 
     → Unary a b

data UnOp a b where
  OpNot ∷ UnOp TBool TBool
  OpNeg ∷ GetNum a => UnOp (Sca (Number a)) (Sca (Number a))

  OpFst ∷ (GetSca p1, GetSca p2) => UnOp (Pair p1 p2) (Sca p1)
  OpSnd ∷ (GetSca p1, GetSca p2) => UnOp (Pair p1 p2) (Sca p2)

  OpLen ∷ GetSca a => Sc a -> UnOp (Arr a) TInt32

instance Show (Unary a b) where
  show (Un op _function) = show op

instance Show (UnOp a b) where
  show = \case
    OpNot → "¬"
    OpNeg → "-"
    OpFst → "fst"
    OpSnd → "snd"
    OpLen _ → "len"

------------------------------------------------------------------------
-- Binary operators                                                   --
------------------------------------------------------------------------
data Binary a b c where
  Bin ∷ (GetTy a, GetTy b, GetTy c) 
      ⇒ BinOp a b c 
      → (ToType a → ToType b → ToType c) 
      → Binary a b c

data BinOp a b c where
  -- Arithmetic
  OpAdd ∷ GetNum a => BinOp (Sca (Number a)) (Sca (Number a)) (Sca (Number a))
  OpSub ∷ GetNum a => BinOp (Sca (Number a)) (Sca (Number a)) (Sca (Number a))
  OpMul ∷ GetNum a => BinOp (Sca (Number a)) (Sca (Number a)) (Sca (Number a))
  OpDiv ∷ GetFra a => BinOp (Sca (Number (Fra a))) (Sca (Number (Fra a))) (Sca (Number (Fra a)))

  -- Relational
  OpEqual         ∷ GetSca a => BinOp (Sca a) (Sca a) TBool
  OpNotEqual      ∷ GetSca a => BinOp (Sca a) (Sca a) TBool
  OpLessThan      ∷ GetSca a => BinOp (Sca a) (Sca a) TBool
  OpLessThanEq    ∷ GetSca a => BinOp (Sca a) (Sca a) TBool
  OpGreaterThan   ∷ GetSca a => BinOp (Sca a) (Sca a) TBool
  OpGreaterThanEq ∷ GetSca a => BinOp (Sca a) (Sca a) TBool

  -- Logical
  OpAnd ∷ BinOp TBool TBool TBool
  OpOr  ∷ BinOp TBool TBool TBool
  -- OpXor ∷ GetNum a => BinOp a a a
  OpXor ∷ GetTy a => BinOp a a a

  OpPair  ∷ (GetSca p1, GetSca p2) => BinOp (Sca p1) (Sca p2) (Pair p1 p2)
  OpArr   ∷ GetSca a => Id -> BinOp TInt32 (Sca a) (Arr a)
  OpArrIx ∷ GetSca a => BinOp (Arr a) TInt32 (Sca a)

instance Show (Binary a b c) where
  show (Bin op _function) = show op

instance Show (BinOp a b c) where
  show = \case
    OpAdd             → "+" ++ subscript' @a
    OpSub             → "-" ++ subscript' @a
    OpMul             → "*" ++ subscript' @a
    OpDiv             → "/" ++ subscript' @a
    OpEqual{}         → "="
    OpNotEqual{}      → "≠"
    OpLessThan{}      → "<"
    OpLessThanEq{}    → "≤"
    OpGreaterThan{}   → ">"
    OpGreaterThanEq{} → "≥"
    OpAnd             → "∧"
    OpOr              → "∨"
    OpXor             → "⊕" ++ subscript' @a
    OpPair            → "×"
    OpArr name        → "array_" ++ show name
    OpArrIx           → "‼"

------------------------------------------------------------------------
-- Ternary operators                                                  --
------------------------------------------------------------------------
data Ternary a b c d where
  Ter ∷ (GetTy a, GetTy b, GetTy c, GetTy d)
      ⇒ TernOp a b c d 
      → (ToType a → ToType b → ToType c → ToType d) 
      → Ternary a b c d

data TernOp a b c d where
  OpIf    ∷ TernOp TBool a a a
  OpWhile ∷ Id → TernOp TBool s s s

instance Show (Ternary a b c d) where
  show (Ter op _function) = show op

instance Show (TernOp a b c d) where
  show = \case
    OpIf{}    → "if"
    OpWhile{} → "while"
