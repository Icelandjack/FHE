module Variable where

import Control.Lens
import Numeric.Natural

-- | Variables, the unique part is their 'Natural' identifier, this
-- way variables constructed when going from a higher- to a
-- first-order representation won't care about the variable names:
-- only their number.

data Name id
  -- | Variable from converting HOAS to a first-order representation:
  --    lam (\x -> x + x)
  -- => Lam (Lambda 1) (Add (Var 1) (Var 1))
  -- This is generated from a different source than other variables so
  -- for they are implicitly prefaced with 'var'
  = Lambda id

  -- | Variables from other sources
  | Variable String id
  deriving (Functor, Foldable, Traversable)

instance Show a ⇒ Show (Name a) where
  show (Lambda        i) = "var" ++ "_" ++ show i
  show (Variable name i) = name  ++ "_" ++ show i

type VarName = Name Natural

var ∷ Lens (Name id) (Name id') id id'
var = lens 
  (\case Lambda     id → id 
         Variable _ id → id)
  (\case Lambda        _ → Lambda
         Variable name _ → Variable name)

