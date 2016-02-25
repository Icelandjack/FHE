module Types where

import Data.Int
import Data.Kind (type (★))
-- import Data.Constraint hiding (Class)

data D c where D ∷ c ⇒ D c

-- | Numbers
data RepNumber = RepInt8 | RepInt32

data TNumber ∷ RepNumber → ★ → ★ where
  TInt8  ∷ TNumber RepInt8  Int8
  TInt32 ∷ TNumber RepInt32 Int32

pattern INT8 ∷ () ⇒ (rep ~ 'Scalar ('Number RepInt8), ty ~ Int8) ⇒ TType rep ty
pattern INT8 = TScalar (TNumber TInt8)

pattern INT32 ∷ () ⇒ (rep ~ 'Scalar ('Number RepInt32), ty ~ Int32) ⇒ TType rep ty
pattern INT32 = TScalar (TNumber TInt32)

-- | Booleans, characters, …
data RepNotNum = RepBool | RepChar

data TNotNum ∷ RepNotNum → ★ → ★ where
  TBool ∷ TNotNum RepBool Bool
  TChar ∷ TNotNum RepChar Char

pattern BOOL ∷ () ⇒ (rep ~ 'Scalar ('NotNum 'RepBool), ty ~ Bool) ⇒ TType rep ty
pattern BOOL = TScalar (TNotNum TBool)

pattern CHAR ∷ () ⇒ (rep ~ 'Scalar ('NotNum 'RepChar), ty ~ Char) ⇒ TType rep ty
pattern CHAR = TScalar (TNotNum TChar)

-- | Scalar values (numbers, Booleans, characters, …)
data RepScalar = Number RepNumber | NotNum RepNotNum

type DNumber ty = Num ty

data TScalar ∷ RepScalar → ★ → ★ where
  TNumber ∷ Num ty ⇒ TNumber rep ty → TScalar (Number rep) ty
  TNotNum ∷          TNotNum rep ty → TScalar (NotNum rep) ty

-- | All type
data RepType = Scalar RepScalar | Array RepType | Pair RepScalar RepScalar

data TType ∷ RepType → ★ → ★ where
  TScalar ∷ TScalar rep ty → TType ('Scalar rep) ty
  TArr    ∷ TType   rep ty → TType ('Array  rep) [ty]
  TPair   ∷ TScalar rep₁ ty₁
          → TScalar rep₂ ty₂
          → TType ('Pair rep₁ rep₂) (ty₁, ty₂)

deriving instance Show (TNumber rep ty)
deriving instance Show (TNotNum rep ty)
deriving instance Show (TScalar rep ty)
deriving instance Show (TType   rep ty)

-- | Dionaries
getScalarAsNumber ∷ (GetNumber ty) ⇒ ScalarType ty
getScalarAsNumber = 
  case getNumber of
    NumberType ttype → 
      ScalarType ttype

proofNum' ∷ TType (Scalar (Number _)) ty → D (Num ty)
proofNum' INT8  = D
proofNum' INT32 = D
proofNum' _     = error ".."

proofNum'' ∷ NumberType ty → D (Num ty)
proofNum'' NumberType{} = D

pattern IsNumber ∷ Num ty ⇒ TType (Scalar (Number ööh)) ty
pattern IsNumber ← (proofNum' → D)

proofNum ∷ TType w ty → Maybe (D (Num ty))
proofNum INT8  = Just D
proofNum INT32 = Just D
proofNum _     = Nothing

scalarTypeHasNum ∷ ScalarType a → Maybe (D (Num a))
scalarTypeHasNum = \case
  ScalarType INT8  → Just D
  ScalarType INT32 → Just D
  ScalarType _     → Nothing

pattern HasNum ∷ Num a ⇒ () ⇒ ScalarType a
pattern HasNum ← (scalarTypeHasNum → Just D) 

proofShow ∷ TType rep ty → D (Show ty)
proofShow INT8      = D
proofShow INT32     = D
proofShow BOOL      = D
proofShow CHAR      = D
proofShow (TArr ty) = case proofShow ty of
  D → D
proofShow (TPair _ _) = undefined 
proofShow (TScalar _) = undefined 

pattern IsShow ∷ Show ty ⇒ TType ööh ty
pattern IsShow ← (proofShow → D)

-- | Constrained types (this can probably be implemented differently)
data Type ty where
  Type ∷ (Eq ty, Show ty) ⇒ TType öööh ty → Type ty

instance Show (Type ty) where
  show = \case
    Type INT8        → "i8"
    Type INT32       → "i32"
    Type (TArr ty)   → "Arr (" ++ show ty ++ ")"
    Type (TPair _ _) → undefined 
    Type (TScalar _) → undefined 

class (Ord ty, Eq ty) ⇒ GetType ty  where getType ∷ Type ty
instance GetType Int8  where getType = Type $ TScalar (TNumber TInt8)
instance GetType Int32 where getType = Type $ TScalar (TNumber TInt32)
instance GetType Bool  where getType = Type $ TScalar (TNotNum TBool)
instance GetType Char  where getType = Type $ TScalar (TNotNum TChar)
instance GetType a ⇒ GetType [a] where
  getType ∷ Type [a]
  getType = 
    case getType of
      Type a → Type (TArr a) 
    -- case getType @a of
    --   Type a → Type @[a] (TArr a) 

instance (GetScalar a, GetScalar b) ⇒ GetType (a, b) where
  getType ∷ Type (a, b)
  getType = undefined 
  -- getType = case (getScalar, getScalar) of
  --   (ScalarType (TScalar a), ScalarType (TScalar b)) → 
  --     Type (TPair a b)

  -- getType = case (getScalar @a, getScalar @b) of
  --   (ScalarType (TScalar a), ScalarType (TScalar b)) → 
  --     Type @(a, b) (TPair a b)

data ScalarType ty where
  ScalarType ∷ (Eq ty, Show ty)
             ⇒ TType (Scalar öööh) ty → ScalarType ty

class (GetType ty, Ord ty, Eq ty) ⇒ GetScalar ty    where getScalar ∷ ScalarType ty
instance GetScalar Int8  where getScalar = ScalarType $ TScalar (TNumber TInt8)
instance GetScalar Int32 where getScalar = ScalarType $ TScalar (TNumber TInt32)
instance GetScalar Bool  where getScalar = ScalarType $ TScalar (TNotNum TBool)
instance GetScalar Char  where getScalar = ScalarType $ TScalar (TNotNum TChar)

data NumberType ty where
  NumberType ∷ (Show ty, Eq ty, Num ty) 
             ⇒ TType (Scalar (Number öööh)) ty → NumberType ty

class (Eq ty, Num ty, GetScalar ty) ⇒ GetNumber ty    where getNumber ∷ NumberType ty
instance GetNumber Int8  where getNumber = NumberType $ TScalar (TNumber TInt8)
instance GetNumber Int32 where getNumber = NumberType $ TScalar (TNumber TInt32)

data NotNumType ty where
  NotNumType ∷ (Show ty, Eq ty) ⇒ TType (Scalar (NotNum öööh)) ty → NotNumType ty

class GetScalar ty ⇒ GetNotNum ty where getNotNum ∷ NotNumType ty
instance GetNotNum Bool where getNotNum = NotNumType $ TScalar (TNotNum TBool)
instance GetNotNum Char where getNotNum = NotNumType $ TScalar (TNotNum TChar)

instance Show a ⇒ Show (NumberType a) where show (NumberType ty) = show ty
instance Show a ⇒ Show (ScalarType a) where show (ScalarType ty) = show ty
instance Show a ⇒ Show (NotNumType a) where show (NotNumType ty) = show ty

subscript ∷ TType _ _ → String
subscript = \case
  INT8  → "₈"
  INT32 → "₃₂"
  BOOL  → "b"
  CHAR  → "c"
  _     → error "hi"

showNumTypeSubscript ∷ NumberType a → String
showNumTypeSubscript (NumberType n)  = subscript n

showNumType ∷ NumberType a → String
showNumType (NumberType n)  = showTType n

showScalarType ∷ ScalarType a → String
showScalarType (ScalarType sc)  = showTType sc

showTType ∷ TType rep a → String
showTType INT8  = "i8"
showTType INT32 = "i32"
showTType BOOL  = "i1"
showTType CHAR  = error "Types.hs: Haven't implemented CHAR"
showTType (TArr INT8) = "%Arr*"
showTType (TArr a) = "[" ++ showTType a ++ "]"

type I8  = Int8
type I32 = Int32
type B   = Bool
type C   = Char

showTy ∷ Type ty → String
showTy (Type ttype)  = showTType ttype

dispatch' :: Type ty -> String
dispatch' (Type INT8) = 
  "  tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i8 %1) nounwind"

dispatch' (Type INT32) = 
  "  tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 %1) nounwind"

dispatch' (Type (TArr _)) = 
  "  "

-- dispatch ∷ String → String
-- dispatch "i1"  = 
--   "  call void @showbit(i1 %1)"
-- dispatch "i8" = 
--   "  tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i8 %1) nounwind"
-- dispatch "i32" = 
--   "  tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 %1) nounwind"
-- dispatch "%pairi32i32" = 
--   "  call void @showpair(%pairi32i32 %1)"
-- dispatch "%Arr*" = 
--   "  "
-- dispatch "%Arr8*" = 
--   "  "
