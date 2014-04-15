{-# LANGUAGE GADTs, TypeFamilies, UnicodeSyntax #-}

import qualified Prelude as P
import Prelude hiding ((<), min, max)
import Data.Bits

eval ∷ Exp a → a
eval (LitI i) = i
eval (LitB b) = b
eval (If c t e) = if eval c then eval t else eval e
eval (While c b i) =
  head $ dropWhile (eval . c . Value) $ iterate (eval . b . Value) (eval i)
    
(<) ∷ Exp Int → Exp Int → Exp Bool
LitI i < LitI j = LitB (i P.< j)

min ∷ Exp Int → Exp Int → Exp Int
min a b = ifC (a < b) a b

max ∷ Exp Int → Exp Int → Exp Int
max a b = ifC (a < b) b a

data Exp a where
  LitI   ∷ Int  → Exp Int
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

instance Show a ⇒ Show (Exp a) where
  show (LitI i) = show i
  show (LitI b) = show b
  show (If c t e) = "(if " ++ show c ++ " then " ++ show t ++ " else " ++ show e ++ ")"

class Embed a where
  type Repr a
  toExp   ∷ a → Exp (Repr a)
  fromExp ∷ Exp (Repr a) → a

instance Embed (Exp a) where
  type Repr (Exp a) = a
  toExp   = id
  fromExp = id

instance (Embed a, Embed b) ⇒ Embed (a, b) where
  type Repr (a, b) = (Repr a, Repr b)
  toExp (a, b) = Pair (toExp a) (toExp b)
  fromExp p    = (fromExp (Fst p), fromExp (Snd p))

instance (Embed a, Embed b, Embed c) ⇒ Embed (a, b, c) where
  type Repr (a, b, c) = (Repr a, (Repr b, Repr c))
  toExp (a, b, c) = Pair (toExp a) (Pair (toExp b) (toExp c))
  fromExp p       = (fromExp (Fst p), fromExp (Fst (Snd p)), fromExp (Snd (Snd p)))

true ∷ Exp Bool
true = LitB True

false ∷ Exp Bool
false = LitB False

ifC ∷ Embed a ⇒ Exp Bool → a → a → a
ifC c t e = fromExp (If c (toExp t) (toExp e))

(?) ∷ Embed a ⇒ Exp Bool → (a, a) → a
c ? (t, e) = ifC c t e

while ∷ Embed state ⇒ (state → Exp Bool) → (state → state) → state → state
while c b i = fromExp $ While (c . fromExp)
                              (toExp . b . fromExp)
                              (toExp i)


forLoop ∷ Embed t ⇒ Exp Int → t → (Exp Int → t → t) → t
forLoop len init step = snd $ while (\(i, s) → i < len) (\(i, s) → (i+1, step i s)) (0, init)

instance Num (Exp Int) where
  fromInteger = LitI . fromInteger

data Complex = Exp Int :+ Exp Int deriving Show

real ∷ Complex → Exp Int
real (x :+ _) = x

img ∷ Complex → Exp Int
img (_ :+ y) = y

instance Embed Complex where
  type Repr Complex = (Int, Int)
  fromExp m      = Fst m :+ Snd m
  toExp (a :+ b) = Pair a b

len ∷ Exp [a] → Exp Int
len = ArrLen 

(<!>) ∷ Embed a ⇒ Exp [Repr a] → Exp Int → a
arr <!> ix = fromExp (ArrIx arr ix)

data Vector a where
  Indexed ∷ Exp Int → (Exp Int → a) → Vector a

instance Embed a ⇒ Embed (Vector a) where
  type Repr (Vector a) = [Repr a]
  toExp (Indexed l ixf) = Arr l (toExp . ixf)
  fromExp arr           = Indexed (len arr) (arr <!>)

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