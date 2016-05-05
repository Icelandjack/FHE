{-# LANGUAGE UndecidableInstances #-}

module Types where

import Data.Int
import Data.Kind (type Type, Constraint)
import GHC.TypeLits
import Util

-- import Data.Constraint hiding (Class)

-- Type-indexed type representations.
-- 
-- See 
--   https://github.com/goldfirere/dependent-db/blob/65e39caf24207dfec661977ea6ef67fdddc7bdc8/Basics.hs 
-- and
--   "A reflection on types"
data Ty :: Type -> Type where
  I8  :: Ty Int8
  I   :: Ty Int
  F   :: Ty Float
  D   :: Ty Double
  B   :: Ty Bool
  C   :: Ty Char
  A   :: Ty a -> Ty [a]
  P   :: Ty a -> Ty b -> Ty (a, b)
deriving instance Show (Ty a)
deriving instance Eq   (Ty a)

class (Eq a, Ord a, Show a) => GetTy a where 
  getTy :: Ty a

instance GetTy Int8   where getTy = I8 
instance GetTy Int    where getTy = I
instance GetTy Float  where getTy = F
instance GetTy Double where getTy = D
instance GetTy Char   where getTy = C
instance GetTy Bool   where getTy = B

instance GetTy a => GetTy [a] where 
  getTy :: Ty [a]
  getTy = A (getTy @a)

instance (GetTy a, GetTy b) => GetTy (a, b) where 
  getTy :: Ty (a, b)
  getTy = P (getTy @a) (getTy @b)

type family 
  OneOf (ty :: Type) (classes :: [Type]) msg :: Constraint where
  OneOf ty '[]    msg    = TypeError (ShowType ty :<>: Text " " :<>: Text msg)
  OneOf ty (ty:_) _   = ()
  OneOf ty (_:xs) msg = OneOf ty xs msg 

type IsType a = IsScalar a ∨ IsPair a ∨ IsArr a 

type family 
  IsArr a :: Constraint where
  IsArr [a] = IsType a
  IsArr a   = TypeError (ShowType a)

type family 
  IsPair a :: Constraint where
  IsPair (a, b) = IsType a ∧ IsType b
  IsPair a      = TypeError (ShowType a)

-- Implicit type representations,
--   specialised to scalar values:
-- 
-- >>> getSca @Int8
-- I8
-- >>> getSca @Bool
-- B
type IsScalar a = IsNum a ∨ IsNot a
type GetSca   a = (GetTy a, IsScalar a)
getSca :: GetSca a => Ty a
getSca = getTy

-- Gets values that are not numbers
-- type IsNot   a = (a `OneOf` '[Bool,Char]) "is not *not* an Int lul" 
type family IsNot a :: Constraint where
  IsNot Bool = ()
  IsNot Char = ()
  IsNot ty   = TypeError (ShowType ty :<>: Text " is not *not* an Int lul")

type GetNot  a = (GetSca a, IsNot a)
getNot  :: GetNot  a => Ty a
getNot  = getTy

-- Gets numbers
type IsNum  a = IsFrac a ∨ IsInt a
type GetNum a = (GetSca a, IsNum a, Num a)
getNum :: GetNum  a => Ty a
getNum = getTy

-- Get fractional values
type family IsFrac a :: Constraint where
  IsFrac Float  = ()
  IsFrac Double = ()
  IsFrac ty     = TypeError (ShowType ty :<>: Text " is not a fractional value")
-- type IsFrac  a = (a `OneOf` '[Float,Double]) "is not a fractional value"
type GetFrac a = (GetNum a, IsFrac a)
getFrac :: GetFrac a => Ty a
getFrac = getTy

-- Gets an integer
type family IsInt a :: Constraint where
  IsInt Int  = ()
  IsInt Int8 = ()
  IsInt ty   = TypeError (ShowType ty :<>: Text " is not an Int")
-- type IsInt  a = (a `OneOf` '[Int,Int8]) "is not an int" 
type GetInt a = (GetNum a, IsInt a)
getInt :: GetInt a => Ty a
getInt = getTy

subscript :: Ty a -> String
subscript = \case
  I8   -> "₈"
  I    -> "₃₂"
  F    -> "f"
  D    -> "d"
  B    -> "b"
  C    -> "c"
  A a   -> "₍" ++ subscript a ++ "₎"
  P a b -> "₍" ++ subscript a  ++ "," ++ subscript b ++ "₎"

-- -- Classifying types:
-- --     ToTYPE Int8
-- --   = MKSCALAR (MKNUM MKINT)
-- -- 
-- --     ToTYPE (Int8, [Bool])
-- --   = MKPAIR INT (MKARR NOT)
-- data NUM    = MKFRAC           | MKINT
-- data SCALAR = MKNUM NUM        | MKNOT 
-- data TYPE   = MKSCALAR SCALAR  | MKARR TYPE | MKPAIR TYPE TYPE

-- type FRAC   = MKSCALAR (MKNUM MKFRAC)
-- type INT    = MKSCALAR (MKNUM MKINT)
-- type NOT    = MKSCALAR MKNOT

-- -- Maps from Haskell types to their respective classifications.
-- type family
--   ToTYPE (ty :: Type) :: TYPE where
--   ToTYPE Int8   = INT
--   ToTYPE Int32  = INT
--   ToTYPE Float  = FRAC
--   ToTYPE Double = FRAC
--   ToTYPE Bool   = NOT
--   ToTYPE Char   = NOT
--   ToTYPE [a]    = MKARR  (ToTYPE a)
--   ToTYPE (a, b) = MKPAIR (ToTYPE a) (ToTYPE b)

-- -- Implicit type representations
-- -- 
-- -- Each type determines a single classification
-- class (Show ty, Ord ty) => GetTy ty (rep :: TYPE) | ty -> rep where
--   getTy :: Ty ty

-- -- Integrals
-- instance GetTy Int8   INT  where getTy = I8  :: Ty Int8
-- instance GetTy Int32  INT  where getTy = I32 :: Ty Int32

-- -- Fractionals
-- instance GetTy Float  FRAC where getTy = F   :: Ty Float
-- instance GetTy Double FRAC where getTy = D   :: Ty Double
-- instance GetTy Bool   NOT  where getTy = B   :: Ty Bool
-- instance GetTy Char   NOT  where getTy = C   :: Ty Char

-- instance GetTy ty rep => GetTy [ty] (MKARR rep) where 
--   getTy :: Ty [ty]
--   getTy = A getTy

-- instance (GetTy ty1 rep1, GetTy ty2 rep2) => GetTy (ty1, ty2) (MKPAIR rep1 rep2) where 
--   getTy :: Ty (ty1, ty2)
--   getTy = P getTy getTy 

-- type GetSca ty sca = GetTy ty (MKSCALAR sca)
-- getSca :: GetSca ty sca => Ty ty
-- getSca = getTy

-- --   specialised to non-numeric values:
-- -- 
-- -- >>> getNot @Bool
-- -- B
-- type GetNot ty = GetSca ty MKNOT
-- getNot :: GetNot ty => Ty ty
-- getNot = getTy

-- --   specialised to numeric values:
-- type GetNum ty num = (GetSca ty (MKNUM num), Num ty)
-- getNum :: GetNum ty sca => Ty ty
-- getNum = getTy

-- --   specialised to integral values:
-- type GetInt ty = GetNum ty MKINT
-- getInt :: GetInt ty => Ty ty
-- getInt = getTy

-- --   specialised to fractional values:
-- type GetFrac ty = GetNum ty MKFRAC
-- getFrac :: GetFrac ty => Ty ty
-- getFrac = getTy

-- pattern CheckNum :: GetNum ty num => Num ty => Ty ty
-- pattern CheckNum <- _     where
--         CheckNum = getNum

pattern CheckNum :: GetNum ty => Ty ty
pattern CheckNum <- _ where
        CheckNum = getTy

toLLVMType :: Ty a -> String
toLLVMType = \case
  I8   -> "i8"
  I    -> "i32"
  B    -> "i1"
  A I8 -> "%Arr8*"
  A I  -> "%Arr*"
  A B  -> "%Arr1*"
  A (A I8) -> "%Arr8**"
  A (A I)  -> "%Arr**"
  A (A B)  -> "%Arr1**"
  a    -> error ("missing what ever in toLLVM for " ++ show a)

bufferType :: Ty a -> String
bufferType ty = toLLVMType ty ++ "*"

-- -- -- | Numbers
-- -- data RepNumber = RepInt8 | RepInt32

-- -- data TNumber ∷ RepNumber → ★ → ★ where
-- --   TInt8  ∷ TNumber RepInt8  Int8
-- --   TInt32 ∷ TNumber RepInt32 Int32

-- -- pattern INT8 ∷ () ⇒ (rep ~ 'Scalar ('Number RepInt8), ty ~ Int8) ⇒ TType rep ty
-- -- pattern INT8 = TScalar (TNumber TInt8)

-- -- pattern INT32 ∷ () ⇒ (rep ~ 'Scalar ('Number RepInt32), ty ~ Int32) ⇒ TType rep ty
-- -- pattern INT32 = TScalar (TNumber TInt32)

-- -- -- | Booleans, characters, …
-- -- data RepNotNum = RepBool | RepChar

-- -- data TNotNum ∷ RepNotNum → ★ → ★ where
-- --   TBool ∷ TNotNum RepBool Bool
-- --   TChar ∷ TNotNum RepChar Char

-- -- pattern BOOL ∷ () ⇒ (rep ~ 'Scalar ('NotNum 'RepBool), ty ~ Bool) ⇒ TType rep ty
-- -- pattern BOOL = TScalar (TNotNum TBool)

-- -- pattern CHAR ∷ () ⇒ (rep ~ 'Scalar ('NotNum 'RepChar), ty ~ Char) ⇒ TType rep ty
-- -- pattern CHAR = TScalar (TNotNum TChar)

-- -- -- | Scalar values (numbers, Booleans, characters, …)
-- -- data RepScalar = Number RepNumber | NotNum RepNotNum

-- -- type DNumber ty = Num ty

-- -- data TScalar ∷ RepScalar → ★ → ★ where
-- --   TNumber ∷ Num ty ⇒ TNumber rep ty → TScalar (Number rep) ty
-- --   TNotNum ∷          TNotNum rep ty → TScalar (NotNum rep) ty

-- -- -- | All type
-- -- data RepType = Scalar RepScalar | Array RepType | Pair RepScalar RepScalar

-- -- data TType ∷ RepType → ★ → ★ where
-- --   TScalar ∷ TScalar rep ty → TType ('Scalar rep) ty
-- --   TArr    ∷ TType   rep ty → TType ('Array  rep) [ty]
-- --   TPair   ∷ TScalar rep₁ ty₁
-- --           → TScalar rep₂ ty₂
-- --           → TType ('Pair rep₁ rep₂) (ty₁, ty₂)

-- -- deriving instance Show (TNumber rep ty)
-- -- deriving instance Show (TNotNum rep ty)
-- -- deriving instance Show (TScalar rep ty)
-- -- deriving instance Show (TType   rep ty)

-- -- -- | Dionaries
-- -- getScalarAsNumber ∷ (GetNumber ty) ⇒ ScalarType ty
-- -- getScalarAsNumber = 
-- --   case getNumber of
-- --     NumberType ttype → 
-- --       ScalarType ttype

-- -- proofNum' ∷ TType (Scalar (Number _)) ty → D (Num ty)
-- -- proofNum' INT8  = D
-- -- proofNum' INT32 = D
-- -- proofNum' _     = error ".."

-- -- proofNum'' ∷ NumberType ty → D (Num ty)
-- -- proofNum'' NumberType{} = D

-- -- pattern IsNumber ∷ Num ty ⇒ TType (Scalar (Number ööh)) ty
-- -- pattern IsNumber ← (proofNum' → D)

-- -- proofNum ∷ TType w ty → Maybe (D (Num ty))
-- -- proofNum INT8  = Just D
-- -- proofNum INT32 = Just D
-- -- proofNum _     = Nothing

-- -- scalarTypeHasNum ∷ ScalarType a → Maybe (D (Num a))
-- -- scalarTypeHasNum = \case
-- --   ScalarType INT8  → Just D
-- --   ScalarType INT32 → Just D
-- --   ScalarType _     → Nothing

-- -- pattern HasNum ∷ Num a ⇒ () ⇒ ScalarType a
-- -- pattern HasNum ← (scalarTypeHasNum → Just D) 

-- -- proofShow ∷ TType rep ty → D (Show ty)
-- -- proofShow INT8      = D
-- -- proofShow INT32     = D
-- -- proofShow BOOL      = D
-- -- proofShow CHAR      = D
-- -- proofShow (TArr ty) = case proofShow ty of
-- --   D → D
-- -- proofShow (TPair _ _) = undefined 
-- -- proofShow (TScalar _) = undefined 

-- -- pattern IsShow ∷ Show ty ⇒ TType ööh ty
-- -- pattern IsShow ← (proofShow → D)

-- -- -- | Constrained types (this can probably be implemented differently)
-- -- data Type ty where
-- --   Type ∷ (Eq ty, Show ty) ⇒ TType öööh ty → Type ty

-- -- instance Show (Type ty) where
-- --   show = \case
-- --     Type INT8        → "i8"
-- --     Type INT32       → "i32"
-- --     Type (TArr ty)   → "Arr (" ++ show ty ++ ")"
-- --     Type (TPair _ _) → undefined 
-- --     Type (TScalar _) → undefined 

-- -- class (Ord ty, Eq ty) ⇒ GetType ty  where getType ∷ Type ty
-- -- instance GetType Int8  where getType = Type $ TScalar (TNumber TInt8)
-- -- instance GetType Int32 where getType = Type $ TScalar (TNumber TInt32)
-- -- instance GetType Bool  where getType = Type $ TScalar (TNotNum TBool)
-- -- instance GetType Char  where getType = Type $ TScalar (TNotNum TChar)
-- -- instance GetType a ⇒ GetType [a] where
-- --   getType ∷ Type [a]
-- --   getType = 
-- --     case getType of
-- --       Type a → Type (TArr a) 
-- --     -- case getType @a of
-- --     --   Type a → Type @[a] (TArr a) 

-- -- instance (GetScalar a, GetScalar b) ⇒ GetType (a, b) where
-- --   getType ∷ Type (a, b)
-- --   getType = undefined 
-- --   -- getType = case (getScalar, getScalar) of
-- --   --   (ScalarType (TScalar a), ScalarType (TScalar b)) → 
-- --   --     Type (TPair a b)

-- --   -- getType = case (getScalar @a, getScalar @b) of
-- --   --   (ScalarType (TScalar a), ScalarType (TScalar b)) → 
-- --   --     Type @(a, b) (TPair a b)

-- -- data ScalarType ty where
-- --   ScalarType ∷ (Eq ty, Show ty)
-- --              ⇒ TType (Scalar öööh) ty → ScalarType ty

-- -- class (GetType ty, Ord ty, Eq ty) ⇒ GetScalar ty    where getScalar ∷ ScalarType ty
-- -- instance GetScalar Int8  where getScalar = ScalarType $ TScalar (TNumber TInt8)
-- -- instance GetScalar Int32 where getScalar = ScalarType $ TScalar (TNumber TInt32)
-- -- instance GetScalar Bool  where getScalar = ScalarType $ TScalar (TNotNum TBool)
-- -- instance GetScalar Char  where getScalar = ScalarType $ TScalar (TNotNum TChar)

-- -- data NumberType ty where
-- --   NumberType ∷ (Show ty, Eq ty, Num ty) 
-- --              ⇒ TType (Scalar (Number öööh)) ty → NumberType ty

-- -- class (Eq ty, Num ty, GetScalar ty) ⇒ GetNumber ty    where getNumber ∷ NumberType ty
-- -- instance GetNumber Int8  where getNumber = NumberType $ TScalar (TNumber TInt8)
-- -- instance GetNumber Int32 where getNumber = NumberType $ TScalar (TNumber TInt32)

-- -- data NotNumType ty where
-- --   NotNumType ∷ (Show ty, Eq ty) ⇒ TType (Scalar (NotNum öööh)) ty → NotNumType ty

-- -- class GetScalar ty ⇒ GetNotNum ty where getNotNum ∷ NotNumType ty
-- -- instance GetNotNum Bool where getNotNum = NotNumType $ TScalar (TNotNum TBool)
-- -- instance GetNotNum Char where getNotNum = NotNumType $ TScalar (TNotNum TChar)

-- -- instance Show a ⇒ Show (NumberType a) where show (NumberType ty) = show ty
-- -- instance Show a ⇒ Show (ScalarType a) where show (ScalarType ty) = show ty
-- -- instance Show a ⇒ Show (NotNumType a) where show (NotNumType ty) = show ty

-- -- subscript ∷ TType _ _ → String
-- -- subscript = \case
-- --   INT8  → "₈"
-- --   INT32 → "₃₂"
-- --   BOOL  → "b"
-- --   CHAR  → "c"
-- --   _     → error "hi"

-- -- showNumTypeSubscript ∷ NumberType a → String
-- -- showNumTypeSubscript (NumberType n)  = subscript n

-- -- showNumType ∷ NumberType a → String
-- -- showNumType (NumberType n)  = showTType n

-- -- showScalarType ∷ ScalarType a → String
-- -- showScalarType (ScalarType sc)  = showTType sc

-- -- type I8  = Int8
-- -- type I32 = Int32
-- -- type B   = Bool
-- -- type C   = Char

-- showTy ∷ Type ty → String
-- showTy (Type ttype)  = showTType ttype

-- -- dispatch' :: Type ty -> String
-- -- dispatch' (Type INT8) = 
-- --   "  tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i8 %1) nounwind"

-- -- dispatch' (Type INT32) = 
-- --   "  tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 %1) nounwind"

-- -- dispatch' (Type (TArr _)) = 
-- --   "  "

-- -- -- dispatch ∷ String → String
-- -- -- dispatch "i1"  = 
-- -- --   "  call void @showbit(i1 %1)"
-- -- -- dispatch "i8" = 
-- -- --   "  tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i8 %1) nounwind"
-- -- -- dispatch "i32" = 
-- -- --   "  tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 %1) nounwind"
-- -- -- dispatch "%pairi32i32" = 
-- -- --   "  call void @showpair(%pairi32i32 %1)"
-- -- -- dispatch "%Arr*" = 
-- -- --   "  "
-- -- -- dispatch "%Arr8*" = 
-- -- --   "  "

-- -- type NumProof ty rep = NumProof_ ty rep (IsNum rep)

-- -- class (IsNum rep ~ tag, GetTy ty rep) => NumProof_ ty rep tag where
-- --   numProof_ :: Maybe (Dict (Num ty))

-- -- instance GetNum ty num => NumProof_ ty (MKSCALAR (MKNUM num)) True where
-- --   numProof_ :: Maybe (Dict (Num ty))
-- --   numProof_ = Just Dict

-- -- instance (IsNum rep ~ False, GetTy ty rep) => NumProof_ ty rep False where
-- --   numProof_ :: Maybe (Dict (Num ty))
-- --   numProof_ = Nothing

-- -- numProof :: NumProof ty _rep => Ty ty -> Maybe (Dict (Num ty))
-- -- numProof _ = numProof_

-- -- numProof' :: GetNum ty _rep => Ty ty -> Dict (Num ty)
-- -- numProof' = fromJust . numProof

-- Constraint 
data Dict c where 
  Dict :: c => Dict c

newtype a |- b = Sub (a => Dict b)

instance Show (Dict c) where
  show Dict = "Dict"

instance Show (a |- b) where
  show (Sub _) = "Sub Dict"

