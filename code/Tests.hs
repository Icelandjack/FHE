import Control.Monad.Fix
import Control.Applicative

import Test.QuickCheck
import Test.QuickCheck.Function
import qualified Test.QuickCheck.Monadic as M

import Funcs
import Exp
import Types

data AnyExp where
  Any ∷ Exp a → AnyExp

data Hidden where
  (:::) ∷ (Read a, Show a, Eq a) ⇒ Exp a → TypeRep a → Hidden

data AnyRep where
  AnyRep ∷ TypeRep a → AnyRep

deriving instance Show Hidden
deriving instance Show AnyRep

(//) = div

sub₂ ∷ Arbitrary a ⇒ Gen a
sub₂ = scale (// 2) arbitrary

sub₃ ∷ Arbitrary a ⇒ Gen a
sub₃ = scale (// 3) arbitrary

instance Arbitrary AnyRep where
  arbitrary ∷ Gen AnyRep
  arbitrary = sized sizedRep where

    base ∷ Gen AnyRep
    base = elements [ AnyRep TInt, AnyRep TBool ]

    sizedRep ∷ Int → Gen AnyRep 
    sizedRep 0 = base
    sizedRep n = 
      oneof [ 
        base,
        do AnyRep a ← return (AnyRep TInt) -- sizedRep (n//2)
           AnyRep b ← return (AnyRep TInt) -- sizedRep (n//2)
           return (AnyRep (TPair a b))
      ]

arbitraryWithRep ∷ Int → AnyRep → Gen Hidden
arbitraryWithRep n = \case
  AnyRep TInt → do
    a ← resize n arbitrary
    return (a ::: TInt)
  AnyRep TBool → do
    a ← resize n arbitrary
    return (a ::: TBool)
  AnyRep (TPair TInt TInt) → do
    a ← resize n arbitrary
    return (a ::: TPair TInt TInt)
    -- tm1 ::: TInt ← arbitraryWithRep (n//2) (AnyRep TInt)
    -- tm2 ::: TInt ← arbitraryWithRep (n//2) (AnyRep TInt)
    -- return (Pair tm1 tm2 ::: TPair TInt TInt)

instance Arbitrary Hidden where
  arbitrary ∷ Gen Hidden
  arbitrary = do
    typeRep ← arbitrary
    sized (flip arbitraryWithRep typeRep)

-- Arbitrary instances
instance Arbitrary (Exp (Int, Int)) where
  arbitrary ∷ Gen (Exp (Int, Int))
  arbitrary = liftA2 Pair (scale (// 2) arbitrary)
                          (scale (// 2) arbitrary)

instance Arbitrary (Exp Int) where
  arbitrary ∷ Gen (Exp Int)
  arbitrary = sized sizedExp where

    sizedExp ∷ Int → Gen (Exp Int)
    sizedExp 0 = liftA LitI arbitrary
    sizedExp n = do
      
      let subtree₂ = sizedExp (n // 2)
          subtree₃ = sizedExp (n // 3)

      oneof [ liftA  LitI arbitrary
            , liftA  Fst  (resize n arbitrary)
            , liftA  Snd  (resize n arbitrary)
            , liftA2 Add  subtree₂ subtree₂ 
            , liftA2 Mul  subtree₂ subtree₂ 
            , liftA2 Xor  subtree₂ subtree₂ 
            , liftA2 (⊔)  subtree₂ subtree₂ 
            , liftA3 If   (resize (n//3) arbitrary) subtree₃ subtree₃
            ]

instance Arbitrary (Exp Bool) where
  arbitrary ∷ Gen (Exp Bool)
  arbitrary = sized sizedExp where
    
    sizedExp ∷ Int → Gen (Exp Bool)
    sizedExp 0 = liftA LitB arbitrary
    sizedExp n = do

      let subtree₂ = sizedExp (n // 10)
          subtree₃ = sizedExp (n // 20)
      
      oneof [ liftA  LitB arbitrary
            , liftA  Not  arbitrary
            , liftA2 And  subtree₂ subtree₂
            , liftA3 If   subtree₃ subtree₃ subtree₃
            ]

-- instance CoArbitrary (Exp Int) where
--   coarbitrary ∷ Exp Int → (Gen b → Gen b)
--   coarbitrary = undefined 

instance Arbitrary (Exp [Int]) where
  arbitrary ∷ Gen (Exp [Int])
  arbitrary = do
    n ← frequency
     [(9, fmap (LitI . abs) arbitrary), 
      (0, arbitrary)]

    b ∷ Exp Int ← arbitrary
    return (Arr n (+ b))

prop_eval ∷ (Eq a, Show a, Read a) ⇒ Exp a → Property
prop_eval exp = M.monadicIO $ do
  value ← M.run (runRead exp)
  M.run (print value)
  M.assert (eval exp == value)

prop_eval' ∷ Hidden → Property
prop_eval' (exp ::: _) = M.monadicIO $ do
  value ← M.run (runRead exp)
  M.assert (eval exp == value)

prop_bool ∷ Exp Bool → Property
prop_bool = mapSize (* 1000) . prop_eval

prop_int ∷ Exp Int → Property
prop_int = prop_eval

prop_intList ∷ Exp [Int] → Property
prop_intList = prop_eval

tst' ∷ IO ()
tst' = verboseCheckWith stdArgs { maxSuccess = 10 } prop_eval'

tst ∷ IO ()
tst = quickCheckWith stdArgs { maxSuccess = 100 } prop_eval'

-- shrink ∷ Exp → [Exp]
-- shrink = genericShrink

-- arbExp ∷ Gen Exp
-- arbExp = arbitrary

-- zeroExpr ∷ Gen Exp → Gen Exp
-- zeroExpr arb = do
--   a ← arb
--   return (a + I (- eval a))

-- z ∷ Gen Exp
-- z = suchThat arbitrary (\exp → eval exp == 0)

-- prop_foo ∷ Fun t Int → t → Bool
-- prop_foo (Fun _ f) x = do
--   f x == f x

