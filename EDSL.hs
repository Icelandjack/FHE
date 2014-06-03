{-# LANGUAGE RebindableSyntax, GADTs, TypeFamilies, UnicodeSyntax, UndecidableInstances, ScopedTypeVariables, DeriveDataTypeable, PatternSynonyms #-}

module EDSL where

import qualified Prelude as P
import Prelude hiding ((<), (>=), (<=), min, max)
import Data.Bits
import Data.Word
import Data.List
import Data.Maybe
import Data.Generics.Text
import Data.Data
import GHC.TypeLits

infixr 2 :||
infix  4 .==
infix  4 :==

pattern a :<< as ← ((\xs → case null xs of { True → Nothing; _ → Just (head xs, tail xs)}) → Just (a, as))
pattern as :>> a ← ((\xs → case null xs of { True → Nothing; _ → Just (init xs, last xs)}) → Just (as, a))

eval ∷ Exp a → a
eval (Lit i) = i
eval (LitB b) = b
eval (If c t e) = case eval c of
  True  → eval t
  False → eval e
eval (While c b i) = error "while"
  -- head $ dropWhile (eval . c . Value) $ iterate (eval . b . Value) (eval i)
eval (ArrLen arr) = length (eval arr)
eval (Arr l ixf) = let
  len = eval l
  in map eval
   $ map ixf
   $ map Lit [0..len-1]
eval (a :<  b) = eval a P.< eval b
eval (a :<= b) = eval a P.<= eval b
eval (a :>= b) = eval a P.>= eval b
eval (a :== b) = eval a P.== eval b
eval (a :+ b) = eval a P.+ eval b
eval (a :* b) = eval a P.* eval b
eval (a :- b) = eval a P.- eval b
eval (Pair a b) = (eval a, eval b)
eval (Fst a) = fst (eval a)
eval (Snd a) = snd (eval a)
eval (Value a) = a
-- eval (Lookup l ixf) = map ixf (take (eval l) [0..])
eval (Table a)   = a
eval (TableIndex table i) = eval table !! fromIntegral (eval i)
eval (Arr2 p ixf) = Vec (map (eval . ixf) [0..fromIntegral (natVal p - 1)])
eval (Prim2 _ f a b) = f (eval a) (eval b)

min ∷ Exp Int → Exp Int → Exp Int
min a b = ifC (a < b) a b

max ∷ Exp Int → Exp Int → Exp Int
max a b = ifC (a < b) b a

--   Let :: String -> Lam expr (ra -> (ra -> rb) -> rb) (a -> (a -> b) -> b)
--   Inject :: expr role a -> Lam expr role a

newtype LenVec (n ∷ Nat) a = Vec [a] deriving Show

data Exp a where
  -- | Lambda expressions
  Var    ∷ String → Exp a
  Value  ∷ Show a ⇒ a → Exp a
  Lambda ∷ (Exp a → Exp b) → Exp a → Exp b
  (:·)   ∷ Exp (a → b) → Exp a → Exp b
  Let    ∷ String → Exp (a → (a → b) → b)

  Lit    ∷ (Show a, Num a) ⇒ a → Exp a
  LitB   ∷ Bool → Exp Bool
  If     ∷ Exp Bool → Exp a → Exp a → Exp a
  While  ∷ (Exp s → Exp Bool) → (Exp s → Exp s) → Exp s → Exp s
  Pair   ∷ Exp a → Exp b → Exp (a, b)
  Fst    ∷ Exp (a, b) → Exp a
  Snd    ∷ Exp (a, b) → Exp b
  Prim1  ∷ String → (a → b)     → Exp a → Exp b
  Prim2  ∷ String → (a → b → c) → Exp a → Exp b → Exp c

  Conv   ∷ Exp Word8 → Exp Int

  (:<)   ∷ Ord a ⇒ Exp a → Exp a → Exp Bool
  (:<=)  ∷ Ord a ⇒ Exp a → Exp a → Exp Bool
  (:>=)  ∷ Ord a ⇒ Exp a → Exp a → Exp Bool
  (:==)  ∷ (Show a, Eq a) ⇒ Exp a → Exp a → Exp Bool
  (:-)   ∷ Num a ⇒ Exp a → Exp a → Exp a
  (:+)   ∷ Num a ⇒ Exp a → Exp a → Exp a
  (:*)   ∷ Num a ⇒ Exp a → Exp a → Exp a
  
  (:||)  ∷ Exp Bool → Exp Bool → Exp Bool

  Arr2   ∷ KnownNat n ⇒ Proxy n → (Int → Exp a) → Exp (LenVec n a)

  -- Arrays
  Arr    ∷ Exp Int → (Exp Int → Exp a) → Exp [a]
  ArrLen ∷ Exp [a] → Exp Int
  ArrIx  ∷ Exp [a] → Exp Int → Exp a

  -- Lookup table?
  Table      ∷ [Word8] → Exp [Word8]
  TableIndex ∷ Exp [Word8] → Exp Word8 → Exp Word8

  Undef  :: Exp a

  GetBit ∷ Exp Word8 → Exp Int → Exp Word8
--   SetBit ∷ Exp Word8 → Exp Int → Exp 

instance Show (Exp a) where
  show = \case
    Arr l ixf    → "INDEXED " ++ show l ++ " something"
    Lit i        → show i
    LitB b       → show b
    Var x        → x
    If c t e     → "(if " ++ show c ++ " then " ++ show t ++ " else " ++ show e ++ ")"
    a :== b      → "(" ++ show a ++ " == " ++ show b ++ ")"
    Undef        → "UNDEF"
    a :+ b       → "(" ++ show a ++ " + " ++ show b ++ ")"
    Arr2 l ixf   → let
      len ∷ Int
      len = fromInteger (natVal l)
      
      removeParen ∷ String → String
      removeParen ('(' :<< xs :>> ')') = removeParen xs
      removeParen xs                   = xs

      values ∷ [String]
      values = map (removeParen . show . ixf) [0..len - 1]
      in "(ArrStaticLen<" ++ show len ++ "> [" ++ intercalate ", " values ++ "]>)"

    -- | Addition in GF(2⁸)
    Prim2 "GAdd" _ a b → "(" ++ show a ++ " ⊕ " ++ show b ++ ")"
    
    -- | Multiplication in GF(2⁸)
    Prim2 "GMul" _ a b → "(" ++ show a ++ " • " ++ show b ++ ")"

    -- | Table operations
    Table word       → take 14 (show word) ++ "…]"

    TableIndex table index → show table ++ "‼" ++ show index
    
    a                → "."

class Embed a where
  type Repr a
  desugar   ∷ a → Exp (Repr a)
  sugar     ∷ Exp (Repr a) → a

instance Embed (Exp a) where
  type Repr (Exp a) = a
  desugar   = id
  sugar = id

instance (Embed a, Embed b) ⇒ Embed (a, b) where
  type Repr (a, b) = (Repr a, Repr b)
  desugar (a, b) = Pair (desugar a) (desugar b)
  sugar p    = (sugar (Fst p), sugar (Snd p))

instance (Embed a, Embed b, Embed c) ⇒ Embed (a, b, c) where
  type Repr (a, b, c) = (Repr a, (Repr b, Repr c))
  desugar (a, b, c) = Pair (desugar a) (Pair (desugar b) (desugar c))
  sugar p       = (sugar (Fst p), sugar (Fst (Snd p)), sugar (Snd (Snd p)))

true ∷ Exp Bool
true = LitB True

false ∷ Exp Bool
false = LitB False

ifC ∷ Embed a ⇒ Exp Bool → a → a → a
ifC c t e = sugar (If c (desugar t) (desugar e))

(?) ∷ Embed a ⇒ Exp Bool → (a, a) → a
c ? (t, e) = ifC c t e

while ∷ Embed state ⇒ (state → Exp Bool) → (state → state) → state → state
while c b i = sugar $ While (c . sugar)
                              (desugar . b . sugar)
                              (desugar i)

while' ∷ Embed state ⇒ Int → (state → Exp Bool) → (state → state) → state → state
while' unrollLevel c b i = sugar $ While (c . sugar)
                                     (desugar . b . sugar)
                                     (desugar i)

for = forLoop

forLoop ∷ Embed t ⇒ Exp Int → t → (Exp Int → t → t) → t
forLoop len init step = snd $ while (\(i, s) → i < len) (\(i, s) → (i+1, step i s)) (0, init)

(>=) ∷ Exp Int → Exp Int → Exp Bool
(>=) = (:>=)

(<=) ∷ Exp Int → Exp Int → Exp Bool
(<=) = (:<=)

(<) ∷ Exp Int → Exp Int → Exp Bool
(<) = (:<)

(.==) ∷ Exp Int → Exp Int → Exp Bool
Lit a .== Lit b = case a == b of
  True  → true
  False → false
a .== b = a :== b

mod' ∷ Exp Int → Exp Int → Exp Int
mod' a b = while (>= b) (subtract a) a

instance (Show a, Num a) ⇒ Num (Exp a) where
  fromInteger = Lit . fromInteger
  
  Lit a + Lit b = Lit (a + b)
  a     + b     = a :+ b

  Lit a * Lit b = Lit (a * b)
  a     * b     = a :* b
  
  Lit a - Lit b = Lit (a - b)
  a     - b     = a :- b

data Complex = Exp Int :++ Exp Int deriving Show

real ∷ Complex → Exp Int
real (x :++ _) = x

img ∷ Complex → Exp Int
img (_ :++ y) = y

instance Embed Complex where
  type Repr Complex = (Int, Int)
  sugar m      = Fst m :++ Snd m
  desugar (a :++ b) = Pair a b

-- Vector
len ∷ Exp [a] → Exp Int
len arr = ArrLen arr

(<!>) ∷ Embed a ⇒ Exp [Repr a] → Exp Int → a
arr <!> ix = sugar (ArrIx arr ix)

(!) ∷ Vector a → Exp Int → a
Indexed l ixf ! i = ixf i

type Vector1 a = Vector (Exp a)
type Vector2 a = Vector (Vector (Exp a))

data Vector a where
  Indexed ∷ Exp Int → (Exp Int → a) → Vector a

indexed ∷ Exp Int → (Exp Int → a) → Vector a
indexed l idxFun = Indexed l idxFun 

instance Embed a ⇒ Embed (Vector a) where
  type Repr (Vector a) = [Repr a]
  desugar (Indexed l ixf) = Arr l (desugar . ixf)
  sugar arr           = Indexed (len arr) (arr <!>)

-- fromList ∷ [Word8] → Vector (Exp Word8)
-- fromList xs = indexed (Lit (length xs)) indexFunction where

--   indexFunction (Lit i) = Lit (fromJust (lookup i (zip [0..] xs)))

instance (Embed a, Repr a ~ b, Show b) ⇒ Show (Vector a) where
  show a = show (desugar a)

instance (Eq a, Num a) ⇒ Eq (Exp a) where
  Lit i == Lit j = i == j

ifThenElse = If

(...) ∷ Exp Int → Exp Int → Vector1 Int
1 ... n = indexed n   (+ 1)
m ... n = indexed len (+ m) where
  len ∷ Exp Int
  len = if n < m
          then 0
          else n-m+1

map' ∷ (a → b) → Vector a → Vector b
map' f (Indexed len ixf) = Indexed len (f . ixf)

take' ∷ Exp Int → Vector a → Vector a 
take' n (Indexed l ixf) = Indexed (min n l) ixf

drop' ∷ Exp Int → Vector a → Vector a
drop' n (Indexed l ixf) = undefined

zipWithVec ∷ (Embed a, Embed b) ⇒ (a → b → c) → Vector a → Vector b → Vector c
zipWithVec f (Indexed l1 ifx1) (Indexed l2 ifx2) =
  Indexed (min l1 l2) (\ix → f (ifx1 ix) (ifx2 ix))

otp ∷ Vector Int → Vector Int → Vector Int
otp = undefined

sumVec ∷ (Embed a, Num a) ⇒ Vector a → a
sumVec (Indexed l ixf) = for l 0 (\i s -> s + ixf i)

instance Functor Vector where
  fmap f (Indexed l ixf) = Indexed l (f . ixf)

scalarProd ∷ (Embed a, Num a) ⇒ Vector a → Vector a → a
scalarProd a b = sumVec (zipWithVec (*) a b)

fromList ∷ ∀n a. KnownNat n ⇒ [Exp a] → Maybe (Exp (LenVec n a))
fromList xs
  | fromIntegral (length xs) == len = Just (Arr2 proxyLen (atIndex xs))
  | otherwise                       = Nothing

  where
    proxyLen ∷ Proxy n
    proxyLen = Proxy
    
    len ∷ Integer
    len = natVal proxyLen
    
    atIndex ∷ [b] → Int → b
    atIndex xs n = fromJust (lookup n (zip [0..] xs))
