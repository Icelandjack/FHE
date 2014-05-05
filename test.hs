import System.Random
import Test.QuickCheck.Monadic

-- | Capital N
valN = 2560

n = 108

-- | Key
-- Odd integer 'p > 2N'.
p = 7010

encryption ∷ Integer → IO Integer
encryption b = do
  x ← randomRIO (-n`div`2, n`div`2) :: IO Integer
  k ← randomRIO (-n`div`2, n`div`2) :: IO Integer
  return (b + 2*x + k*p)
  -- x ← randomRIO (-n`div`2, n`div`2) :: IO Integer


  -- return c

decryption c = c `mod` p `mod` 2

prop bit = monadicIO $ do
  let bit' = abs bit `mod` 2
  
  c ← run (encryption bit')

  let m = decryption c

  assert (m == bit')

  -- do
  -- randomRIO (0, 1)
  -- encryption 