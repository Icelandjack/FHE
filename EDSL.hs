{-# LANGUAGE RebindableSyntax, GADTs, TypeFamilies, UnicodeSyntax, UndecidableInstances #-}

module EDSL where

import qualified Prelude as P
import Prelude hiding ((<), (>=), (<=), min, max)
import Data.Bits
import Data.Word

infixr 2 :||
infix  4 .==
infix  4 :==

eval ∷ Exp a → a
eval (Lit i) = i
eval (LitB b) = b
eval (If c t e) = case eval c of
  True  → eval t
  False → eval e
eval (While c b i) =
  head $ dropWhile (eval . c . Value) $ iterate (eval . b . Value) (eval i)
eval (ArrLen arr) = length (eval arr)
eval (Arr l ixf) = let
  len = eval l
  in map eval $ map ixf $ map Lit [0..len-1]
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

min ∷ Exp Int → Exp Int → Exp Int
min a b = ifC (a < b) a b

max ∷ Exp Int → Exp Int → Exp Int
max a b = ifC (a < b) b a

data Exp a where
  Lit    ∷ Num a ⇒ a → Exp a
  LitB   ∷ Bool → Exp Bool
  If     ∷ Exp Bool → Exp a → Exp a → Exp a
  While  ∷ (Exp s → Exp Bool) → (Exp s → Exp s) → Exp s → Exp s
  Pair   ∷ Exp a → Exp b → Exp (a, b)
  Fst    ∷ Exp (a, b) → Exp a
  Snd    ∷ Exp (a, b) → Exp b
  Arr    ∷ Exp Int → (Exp Int → Exp a) → Exp [a]
  ArrLen ∷ Exp [a] → Exp Int
  ArrIx  ∷ Exp [a] → Exp Int → Exp a
  Value  ∷ a → Exp a
  Prim1  ∷ String → (a → b)     → Exp a → Exp b
  Prim2  ∷ String → (a → b → c) → Exp a → Exp b → Exp c

  (:<)   ∷ Ord a ⇒ Exp a → Exp a → Exp Bool
  (:<=)  ∷ Ord a ⇒ Exp a → Exp a → Exp Bool
  (:>=)  ∷ Ord a ⇒ Exp a → Exp a → Exp Bool
  (:==)  ∷ Eq  a ⇒ Exp a → Exp a → Exp Bool
  (:-)   ∷ Num a ⇒ Exp a → Exp a → Exp a
  (:+)   ∷ Num a ⇒ Exp a → Exp a → Exp a
  (:*)   ∷ Num a ⇒ Exp a → Exp a → Exp a
  (:||)   ∷ Exp Bool → Exp Bool → Exp Bool

instance Show a ⇒ Show (Exp a) where
  show (Lit i) = show i
  show (LitB b) = show b
  show (If c t e) = "(if " ++ show c ++ " then " ++ show t ++ " else " ++ show e ++ ")"
  show a = show (eval a)

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

instance Num a ⇒ Num (Exp a) where
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

len ∷ Exp [a] → Exp Int
len = ArrLen 

(<!>) ∷ Embed a ⇒ Exp [Repr a] → Exp Int → a
arr <!> ix = sugar (ArrIx arr ix)

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

sum' (Indexed l ixf) = forLoop l 0 (\i s -> s + ixf i)