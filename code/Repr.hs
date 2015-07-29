module Repr where

import Exp
import Control.Lens
import Control.Lens.Iso
import Data.Bool
import Numeric.Lens
import Numeric.Natural
import Types
import Codegen

import Control.Monad.ST
import Data.STRef

import Data.Word
import Control.Monad
import Data.Bits.Lens
import Data.Bits

type TRepr t = (Type (ReprType t), Repr t)

class Repr exp where
  {-# MINIMAL repr | (toExp, fromExp) #-}

  type ReprType exp ∷ ★

  repr ∷ Iso' exp (Exp (ReprType exp))
  repr = iso toExp fromExp

  toExp   ∷ exp → Exp (ReprType exp)
  toExp   = view repr

  fromExp ∷ Exp (ReprType exp) → exp
  fromExp = view (from repr)

instance Repr (Exp a) where
  type ReprType (Exp a) = a

  repr ∷ Iso' (Exp a) (Exp a)
  repr = id

-- foldMapOf repr ∷ (Exp Bool → r) → (Exp Bool → r)
-- foldMapOf repr ∷ (Exp Bool → r) → (Bool → r)
instance Repr Bool where
  type ReprType Bool = Bool

  repr ∷ Iso' Bool (Exp Bool)
  repr = iso (bool Fls Tru) eval

instance (TRepr a, TRepr b) ⇒ Repr (a, b) where
  type ReprType (a, b) = (ReprType a, ReprType b)
  
  toExp ∷ (a, b) → Exp (ReprType a, ReprType b)  
  toExp (x, y) = Pair (toExp x) (toExp y)

  fromExp ∷ Exp (ReprType a, ReprType b) → (a, b)
  fromExp p = (fromExp (Fst p), fromExp (Snd p))

ifThenElse ∷ Repr a ⇒ Exp Bool → a → a → a
ifThenElse c t e = fromExp (If c (toExp t) (toExp e))

-- while ∷ Repr st ⇒ (st → Exp Bool) → (st → st) → st → st
-- while c b i = fromExp (While (c . fromExp) (toExp . b . fromExp) (toExp i))

-- forLoop ∷ TRepr t ⇒ Exp Int → t → (Exp Int → t → t) → t
-- forLoop len init step = 
--   while 
--     (\(i, s) → i :<: len)
--     (\(i, s) → (i+1, step i s))
--     (0, init)
--     & snd

