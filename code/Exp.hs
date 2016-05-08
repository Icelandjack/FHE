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

-- * Imports
-- https://hackage.haskell.org/package/feldspar-language-0.7/docs/src/Feldspar-Core-Types.html

module Exp where

import Data.Bits
import Text.Printf
import Numeric.Natural
import Data.Int
import Types
import Variable
import Operators
import Data.Bits (xor)
import Data.Kind (type (*))
import Control.Lens (Traversal', maximumOf)
import Data.List (genericLength)

import Control.Lens

import Util

import Data.Kind
import Data.Type.Equality
import Data.Constraint

-- * AST
data Exp a where
  Constant :: GetSca a => Ty (Sca a) → ScaToType a → Exp (Sca a)
  MkVar    :: V a -> Exp a

  Pi   :: Fr a -> Exp (Sca (Number (Fra a)))

  -- Operators
  UnOp  ∷ Unary   a b     → (Exp a → Exp b)
  BinOp ∷ Binary  a b c   → (Exp a → Exp b → Exp c)
  TerOp ∷ Ternary a b c d → (Exp a → Exp b → Exp c → Exp d)

  -- Lam ∷ Name → Exp b → Exp (a → b)
  -- App ∷ Exp (a → b) → Exp a → Exp b

-- * Pattern Synonyms
-- ** Helper functions for operators 
unaryOp ∷ (GetTy a, GetTy b) 
        ⇒ UnOp a b 
        → (ToType a → ToType b) 
        → (Exp a → Exp b)
unaryOp op (¬) = UnOp (Un op (¬))
                              
binaryOp ∷ (GetTy a, GetTy b, GetTy c) 
         ⇒ BinOp a b c 
         → (ToType a → ToType b → ToType c) 
         → (Exp a → Exp b → Exp c)
binaryOp op (•) = BinOp (Bin op (•))

-- Construct AND deconstruct a numeric value, introducing a local
-- 'Num' assumption, this took a lot of effort and design but now I
-- can write:
--   ANum 0 + b      = b
--   a      + ANum 0 = a
-- 
-- TODO:
--   eval :: Exp a → a
--   eval = \case
--     Tru → True
--     Fls → True
--   
--     ANum i → i
-- this should be able to work(?) but requires "GetNum" constraint.
-- 
-- Should it *only* be allowed with GetNum's, in which case it's a
-- irrefutable pattern, or should we allow it on '∀x. Exp x' where it
-- fails on 'Fls' or what ever.
-- 
-- Interesting question, answer when sober.
-- pattern ANum :: (GetNum num, a ~ Sca (Number num)) => Num (NumToType num) => NumToType num -> Exp a
-- pattern ANum :: a`NumberHas`num => Num (NumToType num) => NumToType num -> Exp a
pattern ANum :: () => t `ScaHas` a => ScaToType a -> Exp t
pattern ANum n ← Constant _     n
  where ANum n = Constant getTy n

-- pattern Var :: GetTy t => () => Id → Exp t
-- pattern Var id ← MkVar (id ::: _    ) 
--   where Var id = MkVar (id ::: getTy)

pattern MkInt8 :: () => TInt8 ~ a => ToType a -> Exp a
pattern MkInt8 i₈ = Constant (ScaRep (NumRep I8Rep)) i₈

pattern MkInt32 :: () => TInt32 ~ a => ToType a -> Exp a
pattern MkInt32 i₃₂ = Constant (ScaRep (NumRep I32Rep)) i₃₂

pattern MkFloat :: () => TFloat ~ a => ToType a -> Exp a
pattern MkFloat fl = Constant (ScaRep (NumRep (FraRep F32Rep))) fl

pattern MkDouble :: () => TDouble ~ a => ToType a -> Exp a
pattern MkDouble fl = Constant (ScaRep (NumRep (FraRep F64Rep))) fl

pattern MkBool :: () => TBool ~ a => ToType a -> Exp a
pattern MkBool bool = Constant (ScaRep (NotRep BoolRep)) bool

-- -- http://ghc.haskell.org/trac/ghc/ticket/12017
-- --   pattern Tru = MkBool True
pattern Tru :: () => TBool ~ a => Exp a
pattern Tru = Constant (ScaRep (NotRep BoolRep)) True

pattern Fls :: () => TBool ~ a => Exp a
pattern Fls = Constant (ScaRep (NotRep BoolRep)) False

-- -- TODO: Change to multi-equation form for next GHC version.
pattern Not ∷ () ⇒ TBool ~ a ⇒ Exp a → Exp a
pattern Not b ← UnOp (Un OpNot _) b 
  where Not Tru       = Fls
        Not (Not Fls) = Tru
        Not (Not b)   = b
        Not b         = unaryOp OpNot not b

pattern Xor :: (GetTy c, Bits (ToType c)) => Exp c -> Exp c -> Exp c
pattern Xor x y <- BinOp (Bin OpXor _) x y
  where Xor x y =  binaryOp OpXor xor x y
        
pattern Equal :: forall z. () => forall a. (GetSca a, TBool ~ z) => Exp (Sca a) -> Exp (Sca a) -> Exp z
pattern Equal x y <- BinOp (Bin OpEqual _) x y 
  where Equal x y = binaryOp OpEqual (==) x y

pattern NotEqual :: () => (GetSca a, TBool ~ z) => Exp (Sca a) -> Exp (Sca a) -> Exp z
pattern NotEqual x y <- BinOp (Bin OpNotEqual _) x y 
  where NotEqual x y = binaryOp OpNotEqual (/=) x y

pattern LessThan :: () => (GetSca a, TBool ~ z) => Exp (Sca a) -> Exp (Sca a) -> Exp z
pattern LessThan x y <- BinOp (Bin OpLessThan _) x y 
  where LessThan x y = binaryOp OpLessThan (<) x y

pattern LessThanEq :: () => (GetSca a, TBool ~ z) => Exp (Sca a) -> Exp (Sca a) -> Exp z
pattern LessThanEq x y <- BinOp (Bin OpLessThanEq _) x y 
  where LessThanEq x y = binaryOp OpLessThanEq (<=) x y

pattern GreaterThan :: () => (GetSca a, TBool ~ z) => Exp (Sca a) -> Exp (Sca a) -> Exp z
pattern GreaterThan x y <- BinOp (Bin OpGreaterThan _) x y 
  where GreaterThan x y = binaryOp OpGreaterThan (>) x y

pattern GreaterThanEq :: () => (GetSca a, TBool ~ z) => Exp (Sca a) -> Exp (Sca a) -> Exp z
pattern GreaterThanEq x y <- BinOp (Bin OpGreaterThanEq _) x y
  where GreaterThanEq x y = binaryOp OpGreaterThanEq (>=) x y

pattern If ∷ () ⇒ GetTy a ⇒ Exp TBool → Exp a → Exp a → Exp a
pattern If cond t e ← TerOp (Ter OpIf _                            ) cond t e 
  where If cond t e = TerOp (Ter OpIf $ \b x y → if b then x else y) cond t e

pattern MkPair :: () => (GetSca p1, GetSca p2, t ~ Pair p1 p2) => Exp (Sca p1) -> Exp (Sca p2) -> Exp t
pattern MkPair a b ← BinOp (Bin OpPair _)   a b 
  where MkPair a b = BinOp (Bin OpPair (,)) a b

pattern Fst :: () => (a `ScaHas` sca₁, GetSca sca₂) => Exp (Pair sca₁ sca₂) -> Exp a
pattern Fst pair ← UnOp (Un OpFst _)   pair 
  where Fst pair = UnOp (Un OpFst fst) pair

pattern Fst :: () => (GetSca sca₁, a `ScaHas` sca₂) => Exp (Pair sca₁ sca₂) -> Exp a
pattern Snd pair ← UnOp (Un OpSnd _  ) pair 
  where Snd pair = UnOp (Un OpSnd snd) pair

pattern While ∷ () ⇒ GetTy s ⇒ Id → Exp TBool → Exp s → Exp s → Exp s
pattern While name cond init body ← TerOp (Ter (OpWhile name) _) cond init body 
  where While name                = TerOp (Ter (OpWhile name) (error "while"))

pattern Len :: () => (GetSca a, t ~ TInt32) => Exp (Arr a) -> Exp t
pattern Len xs <- UnOp (Un OpLen{} _)                    xs 
  where Len xs =  UnOp (Un (OpLen getSca) genericLength) xs

pattern MkArr :: () => a `ArrHas` sca => Exp TInt32 -> Id -> Exp (Sca sca) -> Exp a
pattern MkArr len name body ← BinOp (Bin (OpArr name) _)             len body 
  where MkArr len name body = BinOp (Bin (OpArr name) (error "arr")) len body

(!) :: GetSca a => Exp (Arr a) -> Exp TInt32 -> Exp (Sca a)
(!) = ArrIx

-- TRAC:
--   What are this pattern synonym's parameters
--
-- ArrIx          :: forall {a :: TSca}. GetSca a => Exp (Arr a) -> Exp TInt32 -> Exp (Sca a)
-- ArrIx @(Sca _) :: forall {a :: TSca}. GetSca a => Exp ('Arr a) -> Exp TInt32 -> Exp ('Sca a)
--   HERE @(Sca _) IS FORCED, IT INSTANTIATES a1 AND a1 MUST EQUAL Sca a
-- ArrIx @(Sca (Number _)) :: forall {t :: TNum}. 
--   GetNum t => Exp (Arr (Number t)) 
--            -> Exp TInt32 
--            -> Exp (Sca (Number t))
--   NOW THE NEXT PARAMETER MUST BE (Number _)
-- ArrIx @(Sca (Number _a)) @(Number _a) :: forall {t :: TNum}.
--   GetNum t => Exp (Arr (Number t)) 
--            -> Exp TInt32 
--            -> Exp (Sca (Number t))
--
-- This is weird... I want 'a1' to appear LAST, 'a' is what matters
--   TODO add this to trac please, simplified
pattern ArrIx ∷ ∀a. () ⇒ ∀sca. a `ScaHas` sca ⇒ Exp (Arr sca) → Exp TInt32 → Exp a
pattern ArrIx xs index ← BinOp (Bin OpArrIx _)                            xs index 
  where ArrIx xs index = BinOp (Bin OpArrIx (\xs i → xs!!fromIntegral i)) xs index

-- * Instances
-- ** Show (Exp a)
instance Show (Exp a) where
  show ∷ Exp a → String
  show = \case
    Tru →
      "tru"
    Fls →
      "fls"

    While n c b i → 
      printf "while [%s = %s] (%s) { %s }" (show n) (show i) (show c) (show b)

    MkArr l n ixf → 
      printf "(%s for %s in 0…%s)" (show ixf) (show n) (show l)

    -- Constant 42 of type "Int8"  should be displayed: 42₈
    -- Constant 42 of type "Int32" should be displayed: 42₃₂

    --[TODO] For some reason this no longer works in 8.1, wait I don't
    -- even understand what I was doing since I changed so much stuff, meh
    -- Constant (ScalarType ty @ IsShow) exp → 
    -- 
    -- > Wait, are you Sure?? You used type application in a pattern? No this must be an as-pattern.
    -- > Hurm, okay.
    Constant ty exp → 
      show exp ++ subscript ty

    UnOp op x → 
      printf "%s(%s)" (show op) (show x)

    BinOp op x y → 
      printf "(%s %s %s)" (show x) (show op) (show y)

    TerOp op x y z →
      printf "(%s %s %s %s)" (show op) (show x) (show y) (show z)

    ArrIx arr i → 
      printf "%s[%s]" (show arr) (show i)

    MkVar var → show var

    -- App a b          → printf "%s · %s" (show a) (show b)
    -- Lam n body       → printf "(%s ↦ %s)" (show n) (show body)

    Pi a -> "π_" ++ subscript (ScaRep (NumRep (FraRep a)))
    -- _ -> error "instance Show (Exp a)"

-- ** Num (Exp a)
instance a `NumberHas` num => Num (Exp a) where
  (+) :: Exp a -> Exp a -> Exp a
  ANum 0 + y      = y
  x      + ANum 0 = x
  ANum a + ANum b = ANum (a + b)
  x      + y      = binaryOp OpSub (-) x y

  (-) :: Exp a -> Exp a -> Exp a
  a      - b      = binaryOp OpSub (-) a b
  --
  x      - ANum 0 = x
  ANum 0 - y      = negate y
  ANum a - ANum b = ANum (a - b)

  (*) ∷ Exp a → Exp a → Exp a
  a      * b      = binaryOp OpMul (*) a b
  -- 
  ANum 0 * _      = 0
  ANum 1 * y      = y
  _      * ANum 0 = 0
  x      * ANum 1 = x
  ANum a * ANum b = ANum (a * b)

  negate :: Exp a → Exp a
  negate (ANum i) = ANum (negate i)
  negate i        = unaryOp OpNeg negate i

  fromInteger :: Integer → Exp a
  fromInteger = ANum . fromInteger

  abs    = error "Num: no 'abs' method for 'Exp num'"

  signum = error "Num: no 'signum' method for 'Exp num'"

-- ** Fractional/Floating (Exp a)
instance a `FractionalHas` fra => Fractional (Exp a) where
  (/) :: Exp a -> Exp a -> Exp a
  (/) = binaryOp OpDiv (/)

instance a `FractionalHas` fra => Floating (Exp a) where
  pi :: Exp a
  pi = Pi getFra

-- * Higher-Order Interface
while ∷ GetTy s ⇒ (Exp s → Exp TBool) → (Exp s → Exp s) → Exp s → Exp s
while cond loop init = While (Lambda n) condBody loopBody init where
  n        = 1 + max (maxLam condBody) (maxLam loopBody)
  condBody = cond (MkVar (Lambda2 n))
  loopBody = loop (MkVar (Lambda2 n))

arr :: GetSca a => Exp TInt32 -> (Exp TInt32 -> Exp (Sca a)) -> Exp (Arr a)
arr len ixf = MkArr len (Lambda n) body where
  n    = 1 + maxLam body
  body = ixf (MkVar (Lambda2 n))

maxLam ∷ Exp a → Natural
maxLam = \case
  -- Binding constructs, variables and constants 
  -- Lam   (VarId n) _     → n 
  While (VarId n) _ _ _ → n 
  MkArr _ (VarId n) _   → n
  MkVar{}               → 0
  Constant{}            → 0

  -- Functions
  UnOp  _ a             → maxLam a
  BinOp _ a b           → maxLam a `max` maxLam b
  TerOp _ a b c         → maxLam a `max` maxLam b `max` maxLam c 

  -- App a b            → maxLam a `max` maxLam b
  -- Arrays
  ArrIx arr ix          → maxLam arr `max` maxLam ix

  _                     → error ("maxLam: ")

-- * Predefined functions
min' :: GetSca a => Exp (Sca a) -> Exp (Sca a) -> Exp (Sca a)
min' a b = If (LessThan a b) a b

fromList :: ∀a. GetSca a => [Exp (Sca a)] -> Exp (Arr a)
fromList [] = arr 0 (\_ -> undefined)
fromList xs = arr (genericLength xs) (foo 0 xs) where

  foo :: GetNum num => Exp (Sca (Number num)) -> [Exp (Sca a)] -> Exp (Sca (Number num)) -> Exp (Sca a)
  foo n = \case
    [x] → const x
    x:xs → \ix → 
      If (n `Equal` ix) 
        x
        (foo (n+1) xs ix)

getType' ∷ Exp ty → Ty ty
getType' = \case
  Constant ty _ -> 
    ty

  MkVar (_ ::: ty) -> 
    ty

  UnOp  Un{}  _     → getTy
  BinOp Bin{} _ _   → getTy
  TerOp Ter{} _ _ _ → getTy

showExpType ∷ Exp ty → String
showExpType = toLLVMType . getType'

-- * GetArgs
-- getArgs ::                           (Exp ret)                   -> ARGS '[] ret
-- getArgs :: (GetTy a)            => (Exp a -> Exp ret)          -> ARGS '[a] ret
-- getArgs :: (GetTy a, GetTy b) => (Exp a -> Exp b -> Exp ret) -> ARGS '[a,b] ret
-- 
-- >>> getArgs ((+) @(Exp I8))
-- (%arg_1 : i8), (%arg_0 : i8), (NOARGS (%arg_1 +₈ %arg_0))
-- 
-- TODO: Reverse indices.
class GetArgs a where
  getArgs :: a -> (Ex Exp, [Ex V])

instance GetArgs (Exp a) where
  getArgs :: Exp a -> (Ex Exp, [Ex V])
  getArgs ex = (Ex ex, [])

instance (GetTy a, GetArgs rest) => GetArgs (Exp a -> rest) where
  getArgs :: (Exp a -> rest) -> (Ex Exp, [Ex V])
  getArgs exp_fn = let
    i = case maximumOf (traverse . to (ex (view (getId.idNat)))) restArgs of
          Nothing -> 0
          Just n  -> 1 + n

    argument :: V a
    argument = Id "arg" i ::: getTy

    rest :: rest
    rest = exp_fn (MkVar argument)

    exp      :: Ex Exp
    restArgs :: [Ex V]
    (exp, restArgs) = getArgs rest

    in (exp, Ex argument : restArgs)
