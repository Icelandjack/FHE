import Control.Monad.Fix
import Control.Applicative

import Test.QuickCheck
import Test.QuickCheck.Function
import qualified Test.QuickCheck.Monadic as M

import Funcs
import Expr

compileRun :: Exp -> IO Integer
compileRun exp = do
  a ← test exp
  return $ read $ last (lines a)

instance Arbitrary Exp where
  arbitrary ∷ Gen Exp 
  arbitrary = sized sizedExpr where

    sizedExpr ∷ Int → Gen Exp
    sizedExpr 0 = I <$> arbitrary
    sizedExpr n = let 
      subtree₂ = sizedExpr (n `div` 2)
      subtree₃ = sizedExpr (n `div` 3)

      zeroBiased ∷ Gen Exp
      zeroBiased = oneof [zeroExpr subtree₃, subtree₃]

      in oneof [ liftA  I   arbitrary
               , liftA2 Add subtree₂ subtree₂
               -- , liftA2 Mul subtree₂ subtree₂
               -- , liftA2 (⊔) subtree₂ subtree₂
               , liftA3 If  zeroBiased subtree₃ subtree₃
               ]

  shrink ∷ Exp → [Exp]
  shrink = genericShrink

arbitraryMin ∷ Gen Exp
arbitraryMin = liftA2 (⊔) arbitrary arbitrary

arbExp ∷ Gen Exp
arbExp = arbitrary

zeroExpr ∷ Gen Exp → Gen Exp
zeroExpr arb = do
  a ← arb
  return (a + I (- eval a))

z ∷ Gen Exp
z = suchThat arbitrary (\exp → eval exp == 0)

instance CoArbitrary Exp where
  coarbitrary ∷ Exp → Gen b → Gen b
  coarbitrary (I n)      = variant 0
  coarbitrary (Add x y)  = variant 1 . coarbitrary (x, y)
  coarbitrary (If c t e) = variant 2 . coarbitrary (c, t, e)
  coarbitrary (Var str)  = variant 3 . coarbitrary str

prop_eval ∷ Exp → Property
prop_eval exp = M.monadicIO $ do
  value ← M.run (compileRun exp)
  M.assert (eval exp == value)

prop_eval₁ ∷ Fun Exp Exp → Exp → Property
prop_eval₁ (Fun _ f) (appVar → exp) = M.monadicIO $ do
  let result = eval (f exp)
  b ← read <$> M.run (run f [eval exp])

  M.assert (result == b)

infixr +
type a + b = Either a b

pattern VAR s     = Left s
pattern II  s     = Right (Left s)
pattern ADD x y   = Right (Right (Left (x, y)))
pattern MUL x y   = Right (Right (Right (Left (x, y))))
pattern ITE x y c = Right (Right (Right (Right (x, y, c))))

instance Function Exp where
  function ∷ (Exp → b) → (Exp :-> b)
  function = functionMap a b where
    a ∷ Exp → String + Integer + (Exp, Exp) + (Exp, Exp) + (Exp, Exp, Exp)
    a (Var s)    = VAR s
    a (I i)      = II i
    a (Add x y)  = ADD x y
    a (Mul x y)  = MUL x y
    a (If c t h) = ITE c t h

    b ∷ String + Integer + (Exp, Exp) + (Exp, Exp) + (Exp, Exp, Exp) → Exp
    b (VAR s)     = Var s
    b (II i)      = I i
    b (ADD x y)   = Add x y
    b (MUL x y)   = Mul x y
    b (ITE c t e) = If c t e

prop_foo ∷ Fun t Int → t → Bool
prop_foo (Fun _ f) x = do
  f x == f x

haha = \case
  Var "var1" → I 0
  _          → I (-1)
-- Add (I (-1)) (I 1)
-- HAHA∶ 1


