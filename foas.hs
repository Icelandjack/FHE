{-# LANGUAGE GADTs #-}

type Name = Integer

bot ∷ Name
bot = 0

prime ∷ Name → Name
prime = succ

maxVar ∷ Exp → Name
maxVar (Var _)   = bot
maxVar (Lam n _) = n
maxVar (App f a) = maxVar f `max` maxVar a

--     trans (Lam n a) = Lam n (trans' a)
-- should be
--     trans (Lam n a) = lam (\x → trans' (subst n x a))
data Exp = Var Name
         | Lam Name Exp         -- Don't use Lam directly!
         | App Exp Exp
         deriving Show

(·) ∷ Exp → Exp → Exp
(·) = App

lam ∷ (Exp → Exp) → Exp
lam f = Lam n body where
  body = f (Var n)
  n    = prime (maxVar body)

main = do
  print $ Var 1
  print $ Lam 1 (Var 1)
  print $ Lam 1 (Lam 2 (Var 2))