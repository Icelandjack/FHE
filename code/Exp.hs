{-# LANGUAGE UndecidableInstances #-}

-- https://hackage.haskell.org/package/feldspar-language-0.7/docs/src/Feldspar-Core-Types.html

module Exp where

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

-- | AST
data Exp a where
  Constant ∷ GetSca a _sca => Ty a → a → Exp a

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
pattern ANum   ∷ GetNum a _num => Num a => a -> Exp a
pattern ANum n = Constant CheckNum n

pattern Var :: GetTy t rep => GetTy t rep => Id → Exp t
pattern Var id ← MkVar (id ::: _    ) where
        Var id = MkVar (id ::: getTy)

-- -- Shorthands for operators
unaryOp ∷ (GetTy a a_rep, GetTy b b_rep) 
        ⇒ UnOp a b 
        → (a → b) 
        → (Exp a → Exp b)
unaryOp op (¬) = UnOp (Un op (¬))
                              
binaryOp ∷ (GetTy a a_rep, GetTy b b_rep, GetTy c c_rep) 
         ⇒ BinOp a b c 
         → (a → b → c) 
         → (Exp a → Exp b → Exp c)
binaryOp op (•) = BinOp (Bin op (•))

pattern MkInt8 :: () => (GetNum t MKINT, Int8 ~ t) => t -> Exp t
pattern MkInt8 i₈ = Constant I8 i₈

pattern MkInt32 :: () => (GetNum t MKINT, Int32 ~ t) => t -> Exp t
pattern MkInt32 i₃₂ = Constant I32 i₃₂

pattern MkFloat :: () => (GetNum t MKFRAC, Float ~ t) => t -> Exp t
pattern MkFloat fl = Constant F fl

pattern MkDouble :: () => (GetNum t MKFRAC, Double ~ t) => t -> Exp t
pattern MkDouble fl = Constant D fl

pattern MkBool :: () => (GetSca t MKNOT, Bool ~ t) => t -> Exp t
pattern MkBool bool = Constant B bool

pattern MkChar :: () => (GetSca t MKNOT, Char ~ t) => t -> Exp t
pattern MkChar ch = Constant C ch

pattern Tru :: () => (Bool ~ t) => Exp t
pattern Tru = MkBool True

pattern Fls :: () => (Bool ~ t) => Exp t
pattern Fls = MkBool False

-- -- TODO: Change to multi-equation form for next GHC version.
pattern Not ∷ () ⇒ (Bool ~ a) ⇒ Exp a → Exp Bool
pattern Not b ← UnOp (Un OpNot _) b where
        Not b = unaryOp OpNot not b
          -- Tru         → Fls
          -- Not Fls     → Tru
          -- Not (Not b) → Fls
          -- Not b       → unaryOp OpNot not b
        
equal ∷ GetSca a _sca ⇒ Exp a → Exp a → Exp Bool
equal = binaryOp OpEqual (==)

notEqual ∷ GetSca a _sca ⇒ Exp a → Exp a → Exp Bool
notEqual = binaryOp OpNotEqual (/=)

lessThan ∷ GetSca a _sca ⇒ Exp a → Exp a → Exp Bool
lessThan = binaryOp OpLessThan (<)

lessThanEq ∷ GetSca a _sca ⇒ Exp a → Exp a → Exp Bool
lessThanEq = binaryOp OpLessThanEq (<=)

greaterThan ∷ GetSca a _sca ⇒ Exp a → Exp a → Exp Bool
greaterThan = binaryOp OpGreaterThan (>)

greaterThanEq ∷ GetSca a _sca ⇒ Exp a → Exp a → Exp Bool
greaterThanEq = binaryOp OpGreaterThanEq (>=)

ite :: GetTy d d_rep => Exp Bool -> Exp d -> Exp d -> Exp d
ite = TerOp (Ter OpIf (\b x y -> if b then x else y)) 

-- pattern If ∷ () ⇒ GetTy a a_rep ⇒ Exp Bool → Exp a → Exp a → Exp a
-- pattern If cond t e ← TerOp (Ter OpIf _                            ) cond t e where
--         If cond t e = TerOp (Ter OpIf $ \b x y → if b then x else y) cond t e

-- pattern Pair :: () => (GetTy p1 p1_rep, GetTy p2 p2_rep, t ~ (p1, p2)) => Exp p1 -> Exp p2 -> Exp t
-- pattern Pair a b ← BinOp (Bin OpPair _)   a b where
--         Pair a b = BinOp (Bin OpPair (,)) a b

-- pattern Fst :: () => (GetTy a a_rep, GetTy b b_rep) => Exp (a, b) -> Exp a
-- pattern
--   Fst pair ← UnOp (Un OpFst _)   pair where
--   Fst pair = UnOp (Un OpFst fst) pair

-- pattern Snd :: () => (GetTy a a_rep, GetTy b b_rep) => Exp (a, b) -> Exp b
-- pattern 
--   Snd pair ← UnOp (Un OpSnd _  ) pair where
--   Snd pair = UnOp (Un OpSnd snd) pair

-- pattern While ∷ () ⇒ GetTy s s_rep ⇒ Id → Exp Bool → Exp s → Exp s → Exp s
-- pattern
--   While name cond init body ← TerOp (Ter (OpWhile name) _) cond init body where
--   While name                = TerOp (Ter (OpWhile name) (error "while"))

-- pattern Len :: () => (GetTy a1 a', GetTy a (MKARR a'), GetTy t INT, a ~ [a1], t ~ Int32) => Exp a -> Exp t
-- pattern Len xs <- UnOp (Un OpLen _) xs where
--         Len xs =  UnOp (Un OpLen genericLength) xs

-- Arr ∷ GetTy a ⇒ Exp Int32 → Name → Exp a → Exp [a]
-- pattern 
--   Arr ∷ () 
--       ⇒ (GetTy a a_rep, as ~ [a])
--       ⇒ Exp Int32 → Id → Exp a → Exp as
-- pattern 
--   Arr len name body ← BinOp (Bin (OpArr name) _) len body where
--   Arr len name body = BinOp (Bin (OpArr name) (error "arr")) len body

-- ArrIx ∷ GetTy a ⇒ Exp [a] → Exp Int32 → Exp a
-- (!) :: GetTy a _rep => Exp [a] -> Exp Int32 -> Exp a
-- (!) = ArrIx

-- pattern 
--   ArrIx ∷ () ⇒ GetTy a _rep
--         ⇒ Exp [a] → Exp Int32 → Exp a
-- pattern 
--   ArrIx xs index ← BinOp (Bin OpArrIx _) xs index where
--   ArrIx xs index = BinOp (Bin OpArrIx (\xs i → xs !! fromIntegral i)) xs index

-- ------------------------------------------------------------------------
-- -- Instances                                                          --
-- ------------------------------------------------------------------------
-- instance Show (Exp a) where
--   show ∷ Exp a → String
--   show = \case
--     Tru →
--       "tru"
--     Fls →
--       "fls"

--     While n c b i → 
--       printf "while [%s = %s] (%s) { %s }" (show n) (show i) (show c) (show b)
--     Arr l n ixf → 
--       printf "(%s for %s in 0…%s)" (show ixf) (show n) (show l)

--     -- Constant 42 of type "Int8"  should be displayed: 42₈
--     -- Constant 42 of type "Int32" should be displayed: 42₃₂

--     --[TODO] For some reason this no longer works in 8.1, wait I don't
--     -- even understand what I was doing since I changed so much stuff, meh
--     -- Constant (ScalarType ty @ IsShow) exp → 
--     Constant ty exp → 
--       show exp ++ subscript ty

--     UnOp op x → 
--       printf "%s(%s)" (show op) (show x)

--     BinOp op x y → 
--       printf "(%s %s %s)" (show x) (show op) (show y)

--     TerOp op x y z →
--       printf "(%s %s %s %s)" (show op) (show x) (show y) (show z)

-- --     -- ArrIx arr i      → printf "%s[%s]" (show arr) (show i)

--     -- Var var → show var

-- -- -- --     -- App a b          → printf "%s · %s" (show a) (show b)
-- -- -- --     -- Lam n body       → printf "(%s ↦ %s)" (show n) (show body)
    
-- -- --     _               → error "instance Show (Exp a)"

-- instance GetNum n _num => Num (Exp n) where
--   (+) :: Exp n -> Exp n -> Exp n
--   ANum 0 + y      = y
--   x      + ANum 0 = x
--   ANum a + ANum b = ANum (a + b)
--   x      + y      = binaryOp OpAdd (+) x y

--   (-) ∷ Exp n → Exp n → Exp n
--   x      - ANum 0 = x
--   ANum 0 - y      = negate y
--   ANum a - ANum b = ANum (a - b)
--   a      - b      = binaryOp OpSub (-) a b

--   (*) ∷ Exp n → Exp n → Exp n
--   ANum 0 * _      = 0
--   ANum 1 * y      = y
--   _      * ANum 0 = 0
--   x      * ANum 1 = x
--   ANum a * ANum b = ANum (a * b)
--   a      * b      = binaryOp OpMul (*) a b

--   negate ∷ Exp n → Exp n
--   negate (ANum i) = ANum (negate i)
--   negate i        = unaryOp OpNeg negate i

--   fromInteger ∷ Integer → Exp n
--   fromInteger = ANum . fromInteger

--   abs    = error "Num: no 'abs' method for 'Exp num'"

--   signum = error "Num: no 'signum' method for 'Exp num'"

-- ------------------------------------------------------------------------
-- -- Higher-Order Interface                                             --
-- ------------------------------------------------------------------------

-- -- while' ∷ GetTy s _rep ⇒ (Exp s → Exp Bool) → (Exp s → Exp s) → Exp s → Exp s
-- -- while' cond loop init = While (Lambda n) condBody loopBody init where
-- --   n        = 1 + max (maxLam condBody) (maxLam loopBody)
-- --   condBody = cond (MkVar (Lambda2 n))
-- --   loopBody = loop (MkVar (Lambda2 n))

-- -- -- arr ∷ GetTy a _rep ⇒ Exp Int32 → (Exp Int32 → Exp a) → Exp [a]
-- -- -- arr len ixf = Arr len (Lambda n) body where
-- -- --   n    = 1 + maxLam body
-- -- --   body = ixf (MkVar (Lambda2 n))

-- -- maxLam ∷ Exp a → Natural
-- -- maxLam = undefined 
-- -- -- maxLam = \case
-- -- --   -- Binding constructs, variables and constants 
-- -- --   -- Lam   (VarId n) _     → n 
-- -- --   While (VarId n) _ _ _ → n 
-- -- --   Arr _ (VarId n) _     → n
-- -- --   -- Var{}                 → 0
-- -- --   Constant{}            → 0

-- -- --   -- Functions
-- -- --   UnOp  _ a             → maxLam a
-- -- --   BinOp _ a b           → maxLam a `max` maxLam b
-- -- --   TerOp _ a b c         → maxLam a `max` maxLam b `max` maxLam c 

-- -- --   -- App a b            → maxLam a `max` maxLam b

-- -- --   -- Arrays
-- -- --   -- ArrIx arr ix          → maxLam arr `max` maxLam ix

-- -- --   _                     → error ("maxLam: ")

-- -- Predefined functions
-- min' :: GetSca a _sca => Exp a -> Exp a -> Exp a
-- min' a b = If (lessThan a b) a b

-- getType' ∷ Exp ty → Ty ty
-- getType' = \case
--   Constant ty _ -> 
--     ty

--   MkVar (_ ::: ty) -> 
--     ty

--   UnOp  Un{}  _     → getTy
--   BinOp Bin{} _ _   → getTy
--   TerOp Ter{} _ _ _ → getTy

-- -- -- showExpType ∷ Exp ty → String
-- -- -- showExpType = showTy . getType'

-- -- -- opXor :: Exp Int8 -> Exp Int8 -> Exp Int8
-- -- -- opXor = binaryOp OpXor xor

-- -- data ARGS' f types retTy where
-- --   NOARGS  :: Exp retTy                 -> ARGS' f '[]    retTy
-- --   ADDARGS :: V x -> ARGS' f xs retTy -> ARGS' f (x:xs) retTy
-- -- -- -- getExpression :: ARGS types retTy -> Exp retTy
-- -- -- -- argsNAME :: Traversal' (ARGS types retTy) (Ex VAR)
-- -- -- -- foo :: Traversal' (ARGS types retTy) (Ex VAR)
-- -- -- -- getArgs' :: ARGS types retTy -> [Ex Type]
-- -- -- -- argsName :: Traversal' (ARGS types retTy) Name

-- -- -- -- getArgs ::                           (Exp ret)                   -> ARGS '[] ret
-- -- -- -- getArgs :: (GetTy a)            => (Exp a -> Exp ret)          -> ARGS '[a] ret
-- -- -- -- getArgs :: (GetTy a, GetTy b) => (Exp a -> Exp b -> Exp ret) -> ARGS '[a,b] ret
-- -- -- -- 
-- -- -- -- >>> getArgs ((+) @(Exp I8))
-- -- -- -- (%arg_1 : i8), (%arg_0 : i8), (NOARGS (%arg_1 +₈ %arg_0))
-- -- -- -- 
-- -- -- -- TODO: Reverse indices.
-- -- -- class GetArgs a where
-- -- --   type family Args a :: [*]
-- -- --   type family Ret  a :: *

-- -- --   getArgs :: a -> ARGS (Args a) (Ret a)

-- -- -- instance GetArgs (Exp a) where
-- -- --   type Args (Exp _) = '[]
-- -- --   type Ret  (Exp a) = a

-- -- --   getArgs :: Exp a -> ARGS '[] a
-- -- --   getArgs = NOARGS

-- -- -- instance (GetTy a, GetArgs rest) => GetArgs (Exp a -> rest) where
-- -- --   type Args (Exp a -> rest) = a : Args rest
-- -- --   type Ret  (Exp _ -> rest) = Ret rest

-- -- --   getArgs :: (Exp a -> rest) -> ARGS (a : Args rest) (Ret rest)
-- -- --   getArgs exp_fn = let
-- -- --     i = case maximumOf (argsId.idNat) restArgs of
-- -- --           Nothing -> 0
-- -- --           Just n  -> 1 + n

-- -- --     argument :: V a
-- -- --     argument = Id "arg" i ::: getType

-- -- --     rest :: rest
-- -- --     rest = exp_fn (Var argument)

-- -- --     restArgs :: ARGS (Args rest) (Ret rest)
-- -- --     restArgs = getArgs rest
    
-- -- --     in ADDARGS argument restArgs

-- -- -- getExpression :: ARGS types retTy -> Exp retTy
-- -- -- getExpression = \case
-- -- --   NOARGS exp     -> exp
-- -- --   ADDARGS _ rest -> getExpression rest

-- -- -- ex :: (forall x. f x -> r) -> (Ex f -> r)
-- -- -- ex g (Ex fx) = g fx

-- -- -- -- argsNAME :: Traversal' (ARGS types retTy) Id
-- -- -- -- argsNAME f = \case
-- -- -- --   NOARGS exp -> 
-- -- -- --     pure (NOARGS exp)

-- -- -- --   ADDARGS (Id varName i ::: varTy) rest ->  -- do

-- -- --     -- let u :: Ex V
-- -- --     --     u = Ex (N varName i ::: varTy)

-- -- --     -- -- ex :: Ex V <- f u

-- -- --     -- return (ADDARGS ) -- ADDARGS <$> (VAR ty <$> f name) <*> argsName f rest

-- -- -- getFormattedArgs :: ARGS types retTy -> [String]
-- -- -- getFormattedArgs = \case
-- -- --   NOARGS  exp -> 
-- -- --     []

-- -- --   ADDARGS (id ::: ty) rest -> 
-- -- --     (showTy ty ++ " " ++ show id) : getFormattedArgs rest

-- -- -- argsId :: Traversal' (ARGS types retTy) Id
-- -- -- argsId f = \case
-- -- --   NOARGS exp -> 
-- -- --     pure (NOARGS exp)

-- -- --   ADDARGS (id ::: ty) rest ->
-- -- --     ADDARGS 
-- -- --       <$> (f id <&> \id' -> id' ::: ty)
-- -- --       <*> argsId f rest

-- -- -- instance Show (ARGS types retTy) where
-- -- --   show (NOARGS exp) = 
-- -- --     "(NOARGS " -- ++ show exp ++ ")"

-- -- --   -- show (ADDARGS name ty rest) = 
-- -- --   --   "(" ++ show name ++ " : " ++ showTy ty ++ ")" ++ ", " ++ show rest

-- -- -- allargs :: ARGS '[I8, I8, I8, I8, I8] I8
-- -- -- allargs = 
-- -- --   getArgs ((\a b c d e -> a+b+c+d+e) :: Exp I8 -> Exp I8 -> Exp I8 -> Exp I8 -> Exp I8 -> Exp I8)

-- -- -- type EI8  = Exp Int8
