import Control.Monad.State
import Control.Monad.Writer
import Data.Monoid
import Data.Functor

-- Type Synonyms
type Length = Expr Int
type Ix     = Expr Int
type Id     = String

-- Instances
instance Monoid Code where
  mempty = Skip

  mappend Skip m = m
  mappend m Skip = m
  mappend m n    = m :>>: n

-- Data structures
data Expr a where
  Var  ∷ Id → Expr a
  LitI ∷ Int → Expr Int

deriving instance Show (Expr a)

data Code where
  Skip   ∷ Code
  (:>>:) ∷ Code → Code → Code
  For    ∷ Id → Expr Int → Code → Code
--  Write  ∷ Id → Expr a → Expr a → Code
  deriving Show

-- COMPILATION MONAD
newtype CM a = CM (StateT Integer (Writer Code) a)
  deriving (Functor, Monad, MonadState Integer, MonadWriter Code)

run ∷ CM a → Code
run (CM m) = execWriter (evalStateT m 0)

-- 'PushT a' represents push/pull arrays containing a-values.
data PushT b where
  Generate ∷ Length → (Ix → b) → PushT b
  Map      ∷ (a → b) → PushT a → PushT b

-- Turns 'PushT a' arrays into write-ĸontinuations.
apply ∷ PushT a → ((Ix → a → IO ()) → IO ())
apply pushT ĸ = case pushT of
  Generate len ixf → apply undefined undefined
  
  Map f push → apply push (\ix a → ĸ ix (f a))

newId ∷ CM String
newId = do
  i ← get
  put (i + 1)
  return ("v" ++ show i)

localCode ∷ CM a → CM Code
localCode (CM m) = do
  s ← get
  let ((a,s'),code) = runWriter (runStateT m s)
  put s
  return code

for_ ∷ Expr Int → (Expr a → CM ()) → CM ()
for_ n f = do
  id  ← newId
  body ← localCode (f (Var id))
  tell (For id n body)

