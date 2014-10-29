import Circ
import System.Random
import Data.Bits
import Data.Reflection
import Formatting
import qualified Data.Text.Lazy as T
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Control.Monad

type (×) = (,)

type HasParam = Given Param
type Key = Integer

data Bit = O | I

data Param = MkParam {
  nVal ∷ Integer,
  pVal ∷ Integer,
  qVal ∷ Integer
}

n ∷ HasParam ⇒ Integer
n = nVal given

p ∷ HasParam ⇒ Integer
p = pVal given

q ∷ HasParam ⇒ Integer
q = qVal given

makeParameters ∷ Integer → Param
makeParameters λ = MkParam{..} where
  nVal = λ
  pVal = λ^(2 ∷ Integer)
  qVal = λ^(5 ∷ Integer)

nBit ∷ Integer → IO Integer
nBit bitSize = randomRIO (2^(bitSize-1), (2^bitSize)-1)

nBitSuchThat ∷ Integer → (Integer → Bool) → IO Integer
nBitSuchThat bitSize p = do
  int ← nBit bitSize
  if | p int     → return int
     | otherwise → nBitSuchThat bitSize p

keyGen ∷ HasParam ⇒ IO Integer
keyGen = nBitSuchThat p odd

sameParity ∷ Integer → Integer → Bool
sameParity n m = even n == even m

-- odd 0 ≡ False
-- odd 1 ≡ True
encrypt ∷ HasParam ⇒ Key → Integer → IO Integer
encrypt p m = do
  -- m′ has same parity as m
  m' ← nBitSuchThat n (sameParity m)
  
  q' ← nBit q
  
  return (m' + p*q')

decrypt ∷ Integer → Integer → Integer
decrypt p c = c `mod` p `mod` 2

add ∷ Integer × Integer → Integer
add(c₁, c₂) = c₁ + c₂

sub ∷ Integer × Integer → Integer
sub(c₁, c₂) = c₁ - c₂

mul ∷ Integer × Integer → Integer
mul(c₁, c₂) = c₁ * c₂

--

try ∷ HasParam ⇒ Integer → IO Bool
try m = do
  p ← keyGen

  -- c is FRESH ciphertext, since noise (c mod p) is small (n-bits)
  c ← encrypt p m
  print c

  return (decrypt p c == m)

evaluate ∷ Num n ⇒ Circ → [n] → n
evaluate circ = (circ†)

fooo ∷ HasParam ⇒ Circ → [Integer] → IO Bool
fooo circ ms = do
  p  ← keyGen
  cs ← mapM (encrypt p) ms

  let a = evaluate circ ms
  let b = decrypt p (evaluate circ cs)
  return (a == b)
                 
withSecurityParameter ∷ Integer → (Given Param ⇒ r) → r
withSecurityParameter λ m = give (makeParameters λ) m

prop_encdec ∷ Property
prop_encdec = monadicIO $ do
  m ← pick $ choose (0, 1)
  λ ← pick $ choose (2, 5)
  run (withSecurityParameter λ (try m))

prop_add ∷ Property
prop_add = monadicIO $ do
  m ← pick $ choose (0, 1)
  λ ← pick $ choose (2, 5)
  run $ withSecurityParameter λ $ do
    p ← keyGen
    cs ← replicateM 100 (encrypt p m)
    return (decrypt p (sum cs) == sum (replicate 100 m))

prop_mul ∷ Property
prop_mul = monadicIO $ do
  m ← pick $ choose (0, 1)
  λ ← pick $ choose (2, 5)
  run $ withSecurityParameter λ $ do
    p ← keyGen
    cs ← replicateM 100 (encrypt p m)
    return (decrypt p (product cs) == product (replicate 100 m))

prop_addMul ∷ Property
prop_addMul = monadicIO $ do
  m ← pick $ choose (0, 1)
  λ ← pick $ choose (2, 5)
  run $ withSecurityParameter λ $ do
    p ← keyGen

    cs ← replicateM 100 (encrypt p m)
    return (decrypt p (product cs) == product (replicate 100 m))

-- uu ∷ Circ 
-- uu = Circ $ let₃ (\a b c → a ∧ b ∧ c)

-- -- u = do
-- --   a ← arbitrary
-- --   if | a         → undefined
-- --      | otherwise → undefined
-- --   undefined
