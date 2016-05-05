{-# LANGUAGE UndecidableInstances #-}

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

-- | AST
data Exp a where
  Constant ∷ GetSca a => Ty a → a → Exp a

  MkVar ∷ V a → Exp a

  -- Operators
  -- ConOp ∷ Construct a     → Exp a
  UnOp  ∷ Unary   a b     → (Exp a → Exp b)
  BinOp ∷ Binary  a b c   → (Exp a → Exp b → Exp c)
  TerOp ∷ Ternary a b c d → (Exp a → Exp b → Exp c → Exp d)

  -- Lam ∷ Name → Exp b → Exp (a → b)
  -- App ∷ Exp (a → b) → Exp a → Exp b

------------------------------------------------------------------------
-- Pattern Synonym Sugar
------------------------------------------------------------------------

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
pattern ANum   ∷ GetNum a => Num a => a -> Exp a
pattern ANum n = Constant CheckNum n

pattern Var :: GetTy t => () => Id → Exp t
pattern Var id ← MkVar (id ::: _    ) 
  where Var id = MkVar (id ::: getTy)

-- Shorthands for operators
unaryOp ∷ (GetTy a, GetTy b) 
        ⇒ UnOp a b 
        → (a → b) 
        → (Exp a → Exp b)
unaryOp op (¬) = UnOp (Un op (¬))
                              
binaryOp ∷ (GetTy a, GetTy b, GetTy c) 
         ⇒ BinOp a b c 
         → (a → b → c) 
         → (Exp a → Exp b → Exp c)
binaryOp op (•) = BinOp (Bin op (•))

pattern MkInt8 :: () => (GetNum t, Int8 ~ t) => t -> Exp t
pattern MkInt8 i₈ = Constant I8 i₈

pattern MkInt32 :: () => (GetNum t, Int ~ t) => t -> Exp t
pattern MkInt32 i₃₂ = Constant I i₃₂

pattern MkFloat :: () => (GetNum t, Float ~ t) => t -> Exp t
pattern MkFloat fl = Constant F fl

pattern MkDouble :: () => (GetNum t, Double ~ t) => t -> Exp t
pattern MkDouble fl = Constant D fl

pattern MkBool :: () => (GetSca t, Bool ~ t) => t -> Exp t
pattern MkBool bool = Constant B bool

pattern MkChar :: () => (GetSca t, Char ~ t) => t -> Exp t
pattern MkChar ch = Constant C ch

-- http://ghc.haskell.org/trac/ghc/ticket/12017
--   pattern Tru = MkBool True
pattern Tru :: () => (Bool ~ t) => Exp t
pattern Tru = Constant B True

pattern Fls :: () => (Bool ~ t) => Exp t
pattern Fls = Constant B False

-- TODO: Change to multi-equation form for next GHC version.
pattern Not ∷ () ⇒ (Bool ~ a) ⇒ Exp a → Exp Bool
pattern Not b ← UnOp (Un OpNot _) b 
  where Not Tru       = Fls
        Not (Not Fls) = Tru
        Not (Not b)   = b
        Not b         = unaryOp OpNot not b

pattern Xor :: (GetTy c, Bits c) => Exp c -> Exp c -> Exp c
pattern Xor x y <- BinOp (Bin OpXor _) x y
  where Xor x y =  binaryOp OpXor xor x y
        
pattern Equal :: forall z. () => forall a. (GetSca a, Bool ~ z) => Exp a -> Exp a -> Exp z
pattern Equal x y <- BinOp (Bin OpEqual _) x y 
  where Equal x y = binaryOp OpEqual (==) x y

pattern NotEqual :: () => (GetSca a, Bool ~ z) => Exp a -> Exp a -> Exp z
pattern NotEqual x y <- BinOp (Bin OpNotEqual _) x y where
        NotEqual x y = binaryOp OpNotEqual (/=) x y

pattern LessThan :: () => (GetSca a, Bool ~ z) => Exp a -> Exp a -> Exp z
pattern LessThan x y <- BinOp (Bin OpLessThan _) x y 
  where LessThan x y = binaryOp OpLessThan (<) x y

pattern LessThanEq :: () => (GetSca a, Bool ~ z) => Exp a -> Exp a -> Exp z
pattern LessThanEq x y <- BinOp (Bin OpLessThanEq _) x y 
  where LessThanEq x y = binaryOp OpLessThanEq (<=) x y

pattern GreaterThan :: () => (GetSca a, Bool ~ z) => Exp a -> Exp a -> Exp z
pattern GreaterThan x y <- BinOp (Bin OpGreaterThan _) x y 
  where GreaterThan x y = binaryOp OpGreaterThan (>) x y

pattern GreaterThanEq :: () => (GetSca a, Bool ~ z) => Exp a -> Exp a -> Exp z
pattern GreaterThanEq x y <- BinOp (Bin OpGreaterThanEq _) x y
  where GreaterThanEq x y = binaryOp OpGreaterThanEq (>=) x y

pattern If ∷ () ⇒ GetTy a ⇒ Exp Bool → Exp a → Exp a → Exp a
pattern If cond t e ← TerOp (Ter OpIf _                            ) cond t e 
  where If cond t e = TerOp (Ter OpIf $ \b x y → if b then x else y) cond t e

pattern Pair :: () => (GetTy p1, GetTy p2, t ~ (p1, p2)) => Exp p1 -> Exp p2 -> Exp t
pattern Pair a b ← BinOp (Bin OpPair _)   a b 
  where Pair a b = BinOp (Bin OpPair (,)) a b

pattern Fst :: () => (GetTy a, GetTy b) => Exp (a, b) -> Exp a
pattern Fst pair ← UnOp (Un OpFst _)   pair 
  where Fst pair = UnOp (Un OpFst fst) pair

pattern Snd :: () => (GetTy a, GetTy b) => Exp (a, b) -> Exp b
pattern Snd pair ← UnOp (Un OpSnd _  ) pair 
  where Snd pair = UnOp (Un OpSnd snd) pair

pattern While ∷ () ⇒ GetTy s ⇒ Id → Exp Bool → Exp s → Exp s → Exp s
pattern While name cond init body ← TerOp (Ter (OpWhile name) _) cond init body 
  where While name                = TerOp (Ter (OpWhile name) (error "while"))

pattern Len :: () => (GetTy a, GetTy t, t ~ Int) => Exp [a] -> Exp t
pattern Len xs <- UnOp (Un OpLen _)             xs 
  where Len xs =  UnOp (Un OpLen genericLength) xs

-- Arr ∷ GetTy a ⇒ Exp Int32 → Name → Exp a → Exp [a]
pattern Arr ∷ () ⇒ (GetTy a, as ~ [a]) ⇒ Exp Int → Id → Exp a → Exp as
pattern Arr len name body ← BinOp (Bin (OpArr name) _)             len body 
  where Arr len name body = BinOp (Bin (OpArr name) (error "arr")) len body

-- ArrIx ∷ GetTy a ⇒ Exp [a] → Exp Int32 → Exp a
(!) :: GetTy a => Exp [a] -> Exp Int -> Exp a
(!) = ArrIx

pattern ArrIx ∷ () ⇒ GetTy a ⇒ Exp [a] → Exp Int → Exp a
pattern ArrIx xs index ← BinOp (Bin OpArrIx _)                            xs index 
  where ArrIx xs index = BinOp (Bin OpArrIx (\xs i → xs!!fromIntegral i)) xs index

---------------------------------------------------------------------undefined ---
-- Instances                                                          --
------------------------------------------------------------------------
instance Show (Exp a) where
  show ∷ Exp a → String
  show = \case
    Tru →
      "tru"
    Fls →
      "fls"

    While n c b i → 
      printf "while [%s = %s] (%s) { %s }" (show n) (show i) (show c) (show b)
    Arr l n ixf → 
      printf "(%s for %s in 0…%s)" (show ixf) (show n) (show l)

    -- Constant 42 of type "Int8"  should be displayed: 42₈
    -- Constant 42 of type "Int32" should be displayed: 42₃₂

    --[TODO] For some reason this no longer works in 8.1, wait I don't
    -- even understand what I was doing since I changed so much stuff, meh
    -- Constant (ScalarType ty @ IsShow) exp → 
    Constant ty exp → 
      show exp ++ subscript ty

    UnOp op x → 
      printf "%s(%s)" (show op) (show x)

    BinOp op x y → 
      printf "(%s %s %s)" (show x) (show op) (show y)

    TerOp op x y z →
      printf "(%s %s %s %s)" (show op) (show x) (show y) (show z)

    ArrIx arr i      → printf "%s[%s]" (show arr) (show i)

    MkVar var → show var

    -- App a b          → printf "%s · %s" (show a) (show b)
    -- Lam n body       → printf "(%s ↦ %s)" (show n) (show body)
    
    _               → error "instance Show (Exp a)"

instance GetNum n => Num (Exp n) where
  (+) :: Exp n -> Exp n -> Exp n
  x      + y      = binaryOp OpAdd (+) x y
  --
  ANum 0 + y      = y
  x      + ANum 0 = x
  ANum a + ANum b = ANum (a + b)

  (-) ∷ Exp n → Exp n → Exp n
  a      - b      = binaryOp OpSub (-) a b
  --
  x      - ANum 0 = x
  ANum 0 - y      = negate y
  ANum a - ANum b = ANum (a - b)

  (*) ∷ Exp n → Exp n → Exp n
  a      * b      = binaryOp OpMul (*) a b
  -- 
  ANum 0 * _      = 0
  ANum 1 * y      = y
  _      * ANum 0 = 0
  x      * ANum 1 = x
  ANum a * ANum b = ANum (a * b)

  negate ∷ Exp n → Exp n
  -- negate (ANum i) = ANum (negate i)
  negate i        = unaryOp OpNeg negate i

  fromInteger ∷ Integer → Exp n
  fromInteger = ANum . fromInteger

  abs    = error "Num: no 'abs' method for 'Exp num'"

  signum = error "Num: no 'signum' method for 'Exp num'"

------------------------------------------------------------------------
-- Higher-Order Interface                                             --
------------------------------------------------------------------------

while ∷ GetTy s ⇒ (Exp s → Exp Bool) → (Exp s → Exp s) → Exp s → Exp s
while cond loop init = While (Lambda n) condBody loopBody init where
  n        = 1 + max (maxLam condBody) (maxLam loopBody)
  condBody = cond (MkVar (Lambda2 n))
  loopBody = loop (MkVar (Lambda2 n))

arr ∷ GetTy a ⇒ Exp Int → (Exp Int → Exp a) → Exp [a]
arr len ixf = Arr len (Lambda n) body where
  n    = 1 + maxLam body
  body = ixf (MkVar (Lambda2 n))

maxLam ∷ Exp a → Natural
maxLam = \case
  -- Binding constructs, variables and constants 
  -- Lam   (VarId n) _     → n 
  While (VarId n) _ _ _ → n 
  Arr _ (VarId n) _     → n
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

-- Predefined functions
min' :: GetSca a => Exp a -> Exp a -> Exp a
min' a b = If (LessThan a b) a b

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

-- -- -- -- -- getExpression :: ARGS types retTy -> Exp retTy
-- -- -- -- -- getExpression = \case
-- -- -- -- --   NOARGS exp     -> exp
-- -- -- -- --   ADDARGS _ rest -> getExpression rest

-- -- -- -- -- ex :: (forall x. f x -> r) -> (Ex f -> r)
-- -- -- -- -- ex g (Ex fx) = g fx

-- -- -- -- -- -- argsNAME :: Traversal' (ARGS types retTy) Id
-- -- -- -- -- -- argsNAME f = \case
-- -- -- -- -- --   NOARGS exp -> 
-- -- -- -- -- --     pure (NOARGS exp)

-- -- -- -- -- --   ADDARGS (Id varName i ::: varTy) rest ->  -- do

-- -- -- -- --     -- let u :: Ex V
-- -- -- -- --     --     u = Ex (N varName i ::: varTy)

-- -- -- -- --     -- -- ex :: Ex V <- f u

-- -- -- -- --     -- return (ADDARGS ) -- ADDARGS <$> (VAR ty <$> f name) <*> argsName f rest

-- -- -- -- -- getFormattedArgs :: ARGS types retTy -> [String]
-- -- -- -- -- getFormattedArgs = \case
-- -- -- -- --   NOARGS  exp -> 
-- -- -- -- --     []

-- -- -- -- --   ADDARGS (id ::: ty) rest -> 
-- -- -- -- --     (showTy ty ++ " " ++ show id) : getFormattedArgs rest

-- -- -- -- -- argsId :: Traversal' (ARGS types retTy) Id
-- -- -- -- -- argsId f = \case
-- -- -- -- --   NOARGS exp -> 
-- -- -- -- --     pure (NOARGS exp)

-- -- -- -- --   ADDARGS (id ::: ty) rest ->
-- -- -- -- --     ADDARGS 
-- -- -- -- --       <$> (f id <&> \id' -> id' ::: ty)
-- -- -- -- --       <*> argsId f rest

-- -- -- -- -- instance Show (ARGS types retTy) where
-- -- -- -- --   show (NOARGS exp) = 
-- -- -- -- --     "(NOARGS " -- ++ show exp ++ ")"

-- -- -- -- --   -- show (ADDARGS name ty rest) = 
-- -- -- -- --   --   "(" ++ show name ++ " : " ++ showTy ty ++ ")" ++ ", " ++ show rest

-- -- -- -- -- allargs :: ARGS '[I8, I8, I8, I8, I8] I8
-- -- -- -- -- allargs = 
-- -- -- -- --   getArgs ((\a b c d e -> a+b+c+d+e) :: Exp I8 -> Exp I8 -> Exp I8 -> Exp I8 -> Exp I8 -> Exp I8)

-- -- -- -- -- type EI8  = Exp Int8

fromList :: GetSca a => [Exp a] -> Exp [a]
fromList [] = arr 0 (\_ -> undefined)
fromList xs = arr (genericLength xs) (foo 0 xs) where

  foo :: (GetSca a, GetNum b) => Exp b -> [Exp a] -> Exp b -> Exp a
  foo n = \case
    [x] → const x
    x:xs → \ix → 
      If (n `Equal` ix) 
        x
        (foo (n+1) xs ix)

