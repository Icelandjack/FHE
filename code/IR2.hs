module IR2 where

import Prelude.Extras
import Bound hiding (Scope, instantiate1, unscope, abstract1)
import Bound.Class
import Bound.Scope.Simple
import Bound.Term
import Bound.Var
import Data.Int
import Control.Applicative
import Control.Monad (ap)
import Control.Monad.Trans.Class (lift)
import Data.Foldable
import Data.Functor.Identity
import Data.IORef
import Data.Traversable
import Data.Void (Void, absurd)
import qualified LLVM.General.AST.Constant as C
import Data.Word
import Control.Monad.Gen
import Control.Monad.Cont
import Numeric.Natural

import qualified Exp as Exp
import Codegen
import Variable
import Declarations
import Types

pattern I a = Identity a

pattern EFls = Int 1 0
pattern ETru = Int 1 1

data E
  = Int Word32 Integer
  | Float Float
  | Double Double
  deriving (Eq)

instance Show E where
  show = \case
    Int 8    n -> "i₈ " ++ show n
    Int 32   n -> "i₃₂ " ++ show n
    Int size n -> "i_" ++ show size ++ " " ++ show n

    Float fl -> show fl
    Double dbl -> show dbl

data BINOP = Add | Mul | Sub deriving Eq

instance Show BINOP where
  show = \case
    Add -> "+"
    Mul -> "*"
    Sub -> "-"

data Prog id a 
  = Ret (id a) 
  | Alloca (id a) (Prog (Scope () id) a)
  | Assign E (Prog (Scope () id) a)
  | Binop BINOP (id a) (id a) (Prog (Scope () id) a)
  | For (id a) (Scope () (Prog id) a) (Prog (Scope () id) a)
  deriving (Functor, Foldable, Traversable)

instance (Functor id, Eq1 id, Eq a) => Eq (Prog id a) where
  Ret a == Ret b = 
    a ==# b

  Alloca a body == Alloca b body' = 
    a ==# b && body == body'

  Assign e rest == Assign f rest' = 
    e == f && rest == rest'

  Binop op x y rest == Binop op' x' y' rest' =
    op == op' && x ==# x' && y ==# y' && rest == rest'

  For x body rest == For x' body' rest' =
    x ==# x' && body == body' && rest == rest'

instance (Eq1 id, Functor id) => Eq1 (Prog id)

instance (Op ~ a, Identity ~ id) => Show (Prog id a) where
  show = init . unlines . foo [0..]

foo :: [Natural] -> Prog Identity Op -> [String]
foo ((Reference . Id "var" -> x):xs) = \case
  Ret (Identity a) -> [ "ret " ++ show a ]

  Alloca (Identity a) rest -> 
    [ show x ++ " := alloca " ++ show a ]
    ++
    foo xs (inst1 (Identity x) rest)

  Assign e rest -> 
    [ show x ++ " := " ++ show e ]
    ++
    foo xs (inst1 (Identity x) rest)

  Binop Add (Identity a) (Identity b) rest -> 
    [ show x ++ " := " ++ show a ++ " + " ++ show b ]
    ++
    foo xs (inst1 (Identity x) rest)

inst1 :: forall op b a. Monad op => op a -> Prog (Scope b op) a -> Prog op a
inst1 = go instantiate1
  where
    go :: forall f g u. (forall v. op v -> f v -> g v) -> (op u -> Prog f u -> Prog g u)
    go f x = \case
      Ret o               -> Ret (f x o)
      Alloca size rest    -> Alloca (f x size)          (recur rest)
      Assign exp rest     -> Assign exp                 (recur rest)
      Binop op o1 o2 rest -> Binop op (f x o1) (f x o2) (recur rest)

      where
        f' :: op v -> Scope () f v -> Scope () g v
        f' = hoistScope . f . fmap F 

        recur :: Prog (Scope () f) u -> Prog (Scope () g) u
        recur = go f' x

abs1 :: forall op a. (Functor op, Eq a) => a -> Prog op a -> Prog (Scope () op) a
abs1 = go abstract1
  where
    go :: forall f g u. Eq u => (forall v. Eq v => v -> f v -> g v)
                             -> (u -> Prog f u -> Prog g u)
    go f x = \case
      Ret o               -> Ret (f x o)
      Alloca size rest    -> Alloca (f x size)          (recur rest)
      Assign exp rest     -> Assign exp                 (recur rest)
      Binop op o1 o2 rest -> Binop op (f x o1) (f x o2) (recur rest)

      where
        f' :: forall v. Eq v => v -> Scope () f v -> Scope () g v
        f' = hoistScope . f . F

        recur :: Prog (Scope () f) u -> Prog (Scope () g) u
        recur = go f' x

-- add :: Eq a => a -> a -> a -> Prog Identity a -> Prog Identity a
-- add a b var = Add (I a) (I b) . abs1 var

-- ass :: (Functor id, Eq a) => E -> a -> Prog id a -> Prog id a
-- ass exp var = Assign exp . abs1 var

-- ret = Ret . I

-- term :: Prog Identity Void
-- Just term 
--   = closed
--   $ ass (Int 32 10) 't'
--   $ ass (Int 32 5)  'f'
--   $ ('t' `add` 'f') 'a'
--   $ ('a' `add` 'f') 'b'
--   $ ('a' `add` 't') 'c' 
--   $ ret 'c'

type HAHA = ContT (Prog Identity Op) (Gen Natural)

assign :: E -> HAHA (Identity Op)
assign exp = ContT $ \k -> do
  var  <- [ Reference (Id "var" v) | v <- gen ]
  body <- k (Identity var)
  pure $ Assign exp (abs1 var body)

mk :: (Prog (Scope () Identity) Op -> Prog Identity Op) -> HAHA (Identity Op)
mk ĸ = ContT $ \k -> do
  var  <- [ Reference (Id "var" v) | v <- gen ]
  body <- k (Identity var)
  pure $ ĸ (abs1 var body)

-- runProgm
--   :: Enum e =>
--      ContT (Prog id a) (GenT e Identity) (id a) -> Prog id a
-- runProgm :: HAHA (Identity String) -> Prog Identity String
runProgm (ContT prog) = runGen (prog (pure . Ret))
