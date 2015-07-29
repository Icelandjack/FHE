module Types where

data TypeRep a where
  TInt  ∷ TypeRep Int
  TBool ∷ TypeRep Bool
  TArr  ∷ TypeRep a → TypeRep [a]
  TPair ∷ TypeRep a → TypeRep b → TypeRep (a, b)
  TFun  ∷ TypeRep a → TypeRep b → TypeRep (a → b)

data CType = CInt | CBool | CArr CType | CPair CType CType | CFun CType CType

toCType ∷ TypeRep a → CType
toCType TInt        = CInt
toCType TBool       = CBool
toCType (TArr a)    = CArr (toCType a)
toCType (TPair a b) = CPair (toCType a) (toCType b)

deriving instance Show (TypeRep a)

infixr :→:
pattern (:→:) ∷ t ~ (a → b) ⇒ TypeRep a → TypeRep b → TypeRep t
pattern ty :→: pe = TFun ty pe

showTypeRep ∷ TypeRep a → String
showTypeRep TInt         = "i32"
showTypeRep TBool        = "i1"
showTypeRep TPair{}      = "%pairi32i32"
showTypeRep (TArr TInt)  = "%Arr*"
showTypeRep (TArr TBool) = "%BitVector*"

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
