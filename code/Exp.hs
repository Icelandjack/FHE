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

import Control.Lens

-- | AST
data Exp a where
  Constant ∷ ScalarType a → a → Exp a

  Var ∷ V a → Exp a

  -- Operators
  -- ConOp ∷ Construct a     → Exp a
  UnOp  ∷ Unary   a b     → (Exp a → Exp b)
  BinOp ∷ Binary  a b c   → (Exp a → Exp b → Exp c)
  TerOp ∷ Ternary a b c d → (Exp a → Exp b → Exp c → Exp d)

  -- Var ∷ GetType a ⇒ Name → Exp a
  -- Lam ∷ Name → Exp b → Exp (a → b)
  -- App ∷ Exp (a → b) → Exp a → Exp b

------------------------------------------------------------------------
-- Pattern Synonym Sugar
------------------------------------------------------------------------

-- pattern Var ∷ () ⇒ GetType t ⇒ Name → Exp t
-- pattern Var name ← ConOp (Con (VarOp (VAR name)) _) where
--         Var name = ConOp (Con (VarOp (VAR name)) )

-- var :: GetType a => a -> Exp a
-- var a = ConOp (Con (VarOp (V' @_ getType "args" 42)) a)

-- pattern Var :: () => GetType t => VAR t -> Exp t
-- pattern Var :: VAR' t -> Exp t
-- pattern Var name ← ConOp (Con (VarOp name) _) where
--         Var name = 
-- --         Var name = ConOp (Con (VarOp name) )

-- Shorthands for operators
unaryOp ∷ (GetType a, GetType b) 
        ⇒ UnOp a b 
        → (a → b) 
        → (Exp a → Exp b)
unaryOp op (¬) = UnOp (Un op (¬))
                              
binaryOp ∷ (GetType a, GetType b, GetType c) 
         ⇒ BinOp a b c 
         → (a → b → c) 
         → (Exp a → Exp b → Exp c)
binaryOp op (•) = BinOp (Bin op (•))

-- -- I'm not sure what the fuck is going on right now.
pattern ANum ∷ GetNumber t ⇒ Num t ⇒ t → Exp t
pattern ANum i ← Constant HasNum i where
        ANum i = Constant getScalarAsNumber i

pattern ConstInt8 ∷ () ⇒ (a ~ Int8) ⇒ a → Exp a
pattern ConstInt8 i₈ = Constant (ScalarType (TScalar (TNumber TInt8))) i₈

pattern ConstInt32 ∷ () ⇒ (a ~ Int32) ⇒ a → Exp a
pattern ConstInt32 i₃₂ = Constant (ScalarType (TScalar (TNumber TInt32))) i₃₂

pattern ConstBool ∷ () ⇒ (a ~ Bool) ⇒ a → Exp a
pattern ConstBool bool = Constant (ScalarType (TScalar (TNotNum TBool))) bool

pattern ConstChar ∷ () ⇒ (a ~ Char) ⇒ a → Exp a
pattern ConstChar ch = Constant (ScalarType (TScalar (TNotNum TChar))) ch

pattern Tru ∷ () ⇒ (a ~ Bool) ⇒ Exp a
pattern Tru = Constant (ScalarType (TScalar (TNotNum TBool))) True

pattern Fls ∷ () ⇒ (a ~ Bool) ⇒ Exp a
pattern Fls = Constant (ScalarType (TScalar (TNotNum TBool))) False

pattern Not ∷ () ⇒ (a ~ Bool) ⇒ Exp a → Exp Bool
pattern Not b       ← UnOp (Un OpNot _) b where
        Not = \case
          Tru         → Fls
          Not Fls     → Tru
          Not (Not b) → Fls
          Not b       → unaryOp OpNot not b
        
equal ∷ GetScalar a ⇒ Exp a → Exp a → Exp Bool
equal = binaryOp (OpEqual getScalar) (==)

notEqual ∷ GetScalar a ⇒ Exp a → Exp a → Exp Bool
notEqual = binaryOp (OpNotEqual getScalar) (/=)

lessThan ∷ GetScalar a ⇒ Exp a → Exp a → Exp Bool
lessThan = binaryOp (OpLessThan getScalar) (<)

lessThanEq ∷ GetScalar a ⇒ Exp a → Exp a → Exp Bool
lessThanEq = binaryOp (OpLessThanEq getScalar) (<=)

greaterThan ∷ GetScalar a ⇒ Exp a → Exp a → Exp Bool
greaterThan = binaryOp (OpGreaterThan getScalar) (>)

greaterThanEq ∷ GetScalar a ⇒ Exp a → Exp a → Exp Bool
greaterThanEq = binaryOp (OpGreaterThanEq getScalar) (>=)

pattern If ∷ () ⇒ GetType a ⇒ Exp Bool → Exp a → Exp a → Exp a
pattern If cond t e ← TerOp (Ter OpIf _) cond t e where
        If = TerOp (Ter OpIf (\b x y → if b then x else y)) 

-- pattern (:×:) ∷ () ⇒ (GetType a, GetType b, GetType t, t ~ (a, b)) ⇒ Exp a → Exp b → Exp t
pattern a :×: b ← BinOp (Bin OpPair _)   a b where
        a :×: b = BinOp (Bin OpPair (,)) a b

-- pattern Fst ∷ (GetScalar x, GetScalar y) ⇒ (GetType x, GetType y, pair ~ (x, y)) ⇒ Exp pair → Exp x
pattern 
  Fst pair ← UnOp (Un OpFst _)   pair where
  Fst pair = UnOp (Un OpFst fst) pair

-- pattern Snd ∷ () ⇒ (pair ~ (x, y)) ⇒ Exp pair → Exp y
pattern 
  Snd pair ← UnOp (Un OpSnd _)   pair where
  Snd pair = UnOp (Un OpSnd snd) pair

-- While ∷ GetType s ⇒ Name → Exp Bool → Exp s → Exp s → Exp s
pattern
  While ∷ () 
        ⇒ (GetType s, bool ~ Bool) 
        ⇒ Id → Exp bool → Exp s → Exp s → Exp s
pattern
  While name cond init body ← TerOp (Ter (OpWhile name) _) cond init body where
  While name                = TerOp (Ter (OpWhile name) (error "while"))

-- -- Len ∷ GetType a ⇒ Exp [a] → Exp Int32
pattern 
  Len ∷ () ⇒ (GetType [a], as ~ [a], t ~ Int32) 
      ⇒ Exp as → Exp t
pattern 
  Len xs ← UnOp (Un OpLen _)                     xs where
  Len xs = UnOp (Un OpLen (fromIntegral.length)) xs

-- Arr ∷ GetType a ⇒ Exp Int32 → Name → Exp a → Exp [a]
pattern 
  Arr ∷ () 
      ⇒ (GetType a, as ~ [a])
      ⇒ Exp Int32 → Id → Exp a → Exp as
pattern 
  Arr len name body ← BinOp (Bin (OpArr name) _) len body where
  Arr len name body = BinOp (Bin (OpArr name) (error "arr")) len body

-- ArrIx ∷ GetType a ⇒ Exp [a] → Exp Int32 → Exp a
(!) :: GetType a => Exp [a] -> Exp Int32 -> Exp a
(!) = ArrIx

pattern 
  ArrIx ∷ () ⇒ GetType a
        ⇒ Exp [a] → Exp Int32 → Exp a
pattern 
  ArrIx xs index ← BinOp (Bin OpArrIx _) xs index where
  ArrIx xs index = BinOp (Bin OpArrIx (\xs i → xs !! fromIntegral i)) xs index

------------------------------------------------------------------------
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
    Constant (ScalarType ty) exp → 
      show exp ++ subscript ty

    UnOp op x → 
      printf "%s(%s)" (show op) (show x)

    BinOp op x y → 
      printf "(%s %s %s)" (show x) (show op) (show y)

    TerOp op x y z →
      printf "(%s %s %s %s)" (show op) (show x) (show y) (show z)

--     -- ArrIx arr i      → printf "%s[%s]" (show arr) (show i)

    Var var → show var
    -- var@(ConOp (Con (VarOp a) b)) -> show a ++ show (getType @a)
--     -- App a b          → printf "%s · %s" (show a) (show b)
--     -- Lam n body       → printf "(%s ↦ %s)" (show n) (show body)
    
    _               → error "instance Show (Exp a)"

instance GetNumber num ⇒ Num (Exp num) where
  (+) ∷ Exp num → Exp num → Exp num
  ANum 0 + y      = y
  x      + ANum 0 = x
  -- ANum a + ANum b = ANum (a + b)
  x      + y      = binaryOp (OpAdd getNumber) (+) x y

  (-) ∷ Exp num → Exp num → Exp num
  x      - ANum 0 = x
  ANum 0 - y      = negate y
  ANum a - ANum b = ANum (a - b)
  a      - b      = binaryOp (OpSub getNumber) (-) a b

  (*) ∷ Exp num → Exp num → Exp num
  ANum 0 * _      = 0
  ANum 1 * y      = y
  _      * ANum 0 = 0
  x      * ANum 1 = x
  ANum a * ANum b = ANum (a * b)
  a      * b      = binaryOp (OpMul getNumber) (*) a b

  negate ∷ Exp num → Exp num
  negate (ANum i) = ANum (negate i)
  negate i        = unaryOp (OpNeg getNumber) negate i

  fromInteger ∷ Integer → Exp num
  fromInteger = ANum . fromInteger

  abs = error "abs"
  signum = error "signum"

------------------------------------------------------------------------
-- Higher-Order Interface                                             --
------------------------------------------------------------------------

while' ∷ GetType s ⇒ (Exp s → Exp Bool) → (Exp s → Exp s) → Exp s → Exp s
while' cond loop init = While (Lambda n) condBody loopBody init where
  n        = 1 + max (maxLam condBody) (maxLam loopBody)
  condBody = cond (Var (Lambda2 n))
  loopBody = loop (Var (Lambda2 n))

arr ∷ GetType a ⇒ Exp Int32 → (Exp Int32 → Exp a) → Exp [a]
arr len ixf = Arr len (Lambda n) body where
  n    = 1 + maxLam body
  body = ixf (Var (Lambda2 n))

maxLam ∷ Exp a → Natural
maxLam = \case
  -- Binding constructs, variables and constants 
  -- Lam   (VarId n) _     → n 
  While (VarId n) _ _ _ → n 
  Arr _ (VarId n) _     → n
  -- Var{}                 → 0
  Constant{}            → 0

  -- Functions
  UnOp  _ a             → maxLam a
  BinOp _ a b           → maxLam a `max` maxLam b
  TerOp _ a b c         → maxLam a `max` maxLam b `max` maxLam c 

  -- App a b            → maxLam a `max` maxLam b

  -- Arrays
  -- ArrIx arr ix          → maxLam arr `max` maxLam ix

  _                     → error ("maxLam: ")

-- Predefined functions
min' ∷ GetScalar a ⇒ Exp a → Exp a → Exp a
min' a b = If (lessThan a b) a b

getType' ∷ Exp ty → Type ty
getType' = \case
  Constant (ScalarType scalar) _ → 
    Type scalar

  UnOp  Un{}  _     → getType
  BinOp Bin{} _ _   → getType
  TerOp Ter{} _ _ _ → getType
  
  -- Var{} → 
  --   getType

showExpType ∷ Exp ty → String
showExpType = showTy . getType'

opXor :: Exp Int8 -> Exp Int8 -> Exp Int8
opXor = binaryOp OpXor xor

type ARGS = ARGS' Type 

data ARGS' f types retTy where
  NOARGS  :: Exp retTy                 -> ARGS' f '[]    retTy
  ADDARGS :: V x -> ARGS' f xs retTy -> ARGS' f (x:xs) retTy
-- getExpression :: ARGS types retTy -> Exp retTy
-- argsNAME :: Traversal' (ARGS types retTy) (Ex VAR)
-- foo :: Traversal' (ARGS types retTy) (Ex VAR)
-- getArgs' :: ARGS types retTy -> [Ex Type]
-- argsName :: Traversal' (ARGS types retTy) Name

-- getArgs ::                           (Exp ret)                   -> ARGS '[] ret
-- getArgs :: (GetType a)            => (Exp a -> Exp ret)          -> ARGS '[a] ret
-- getArgs :: (GetType a, GetType b) => (Exp a -> Exp b -> Exp ret) -> ARGS '[a,b] ret
-- 
-- >>> getArgs ((+) @(Exp I8))
-- (%arg_1 : i8), (%arg_0 : i8), (NOARGS (%arg_1 +₈ %arg_0))
-- 
-- TODO: Reverse indices.
class GetArgs a where
  type family Args a :: [*]
  type family Ret  a :: *

  getArgs :: a -> ARGS (Args a) (Ret a)

instance GetArgs (Exp a) where
  type Args (Exp _) = '[]
  type Ret  (Exp a) = a

  getArgs :: Exp a -> ARGS '[] a
  getArgs = NOARGS

instance (GetType a, GetArgs rest) => GetArgs (Exp a -> rest) where
  type Args (Exp a -> rest) = a : Args rest
  type Ret  (Exp _ -> rest) = Ret rest

  getArgs :: (Exp a -> rest) -> ARGS (a : Args rest) (Ret rest)
  getArgs exp_fn = let
    i = case maximumOf (argsId.idNat) restArgs of
          Nothing -> 0
          Just n  -> 1 + n

    argument :: V a
    argument = Id "arg" i ::: getType

    rest :: rest
    rest = exp_fn (Var argument)

    restArgs :: ARGS (Args rest) (Ret rest)
    restArgs = getArgs rest
    
    in ADDARGS argument restArgs

getExpression :: ARGS types retTy -> Exp retTy
getExpression = \case
  NOARGS exp     -> exp
  ADDARGS _ rest -> getExpression rest

ex :: (forall x. f x -> r) -> (Ex f -> r)
ex g (Ex fx) = g fx

-- argsNAME :: Traversal' (ARGS types retTy) Id
-- argsNAME f = \case
--   NOARGS exp -> 
--     pure (NOARGS exp)

--   ADDARGS (Id varName i ::: varTy) rest ->  -- do

    -- let u :: Ex V
    --     u = Ex (N varName i ::: varTy)

    -- -- ex :: Ex V <- f u

    -- return (ADDARGS ) -- ADDARGS <$> (VAR ty <$> f name) <*> argsName f rest

getFormattedArgs :: ARGS types retTy -> [String]
getFormattedArgs = \case
  NOARGS  exp -> 
    []

  ADDARGS (id ::: ty) rest -> 
    (showTy ty ++ " " ++ show id) : getFormattedArgs rest

argsId :: Traversal' (ARGS types retTy) Id
argsId f = \case
  NOARGS exp -> 
    pure (NOARGS exp)

  ADDARGS (id ::: ty) rest ->
    ADDARGS 
      <$> (f id <&> \id' -> id' ::: ty)
      <*> argsId f rest

instance Show (ARGS types retTy) where
  show (NOARGS exp) = 
    "(NOARGS " -- ++ show exp ++ ")"

  -- show (ADDARGS name ty rest) = 
  --   "(" ++ show name ++ " : " ++ showTy ty ++ ")" ++ ", " ++ show rest

allargs :: ARGS '[I8, I8, I8, I8, I8] I8
allargs = 
  getArgs ((\a b c d e -> a+b+c+d+e) :: Exp I8 -> Exp I8 -> Exp I8 -> Exp I8 -> Exp I8 -> Exp I8)

type EI8  = Exp Int8
