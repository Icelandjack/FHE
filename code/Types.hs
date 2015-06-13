module Types where

data TypeRep a where
  TInt  ∷ TypeRep Int
  TBool ∷ TypeRep Bool
  TArr  ∷ TypeRep a → TypeRep [a]
  TPair ∷ TypeRep a → TypeRep b → TypeRep (a, b)
  TFun  ∷ TypeRep a → TypeRep b → TypeRep (a → b)

deriving instance Show (TypeRep a)

infixr :→:
pattern (:→:) ∷ t ~ (a → b) ⇒ TypeRep a → TypeRep b → TypeRep t
pattern ty :→: pe = TFun ty pe

showTypeRep ∷ TypeRep a → String
showTypeRep TInt        = "i64"
showTypeRep TBool       = "i1"
showTypeRep TPair{}     = "%pairi64i64"
showTypeRep (TArr TInt) = "%String*"

pattern Bools₁ = TBool :→: TBool
pattern Bools₂ = TBool :→: TBool :→: TBool
pattern Ints₁  = TInt  :→: TInt
pattern Ints₂  = TInt  :→: TInt :→: TInt

pattern Domain   ta ← ta :→: _
pattern Codomain tb ← _  :→: tb

argType ∷ TypeRep (a → b) → TypeRep a
argType (Domain ta) = ta

resType ∷ TypeRep (a → b) → TypeRep b
resType (Codomain tb) = tb

class Type a where
  typeRep ∷ TypeRep a

instance Type Int where
  typeRep ∷ TypeRep Int
  typeRep = TInt

instance Type Bool where
  typeRep ∷ TypeRep Bool
  typeRep = TBool

instance (Type a, Type b) ⇒ Type (a, b) where
  typeRep ∷ TypeRep (a, b)
  typeRep = TPair typeRep typeRep

instance (Type a, Type b) ⇒ Type (a → b) where
  typeRep ∷ TypeRep (a → b)
  typeRep = typeRep :→: typeRep

instance Type a ⇒ Type [a] where
  typeRep ∷ TypeRep [a]
  typeRep = TArr typeRep
