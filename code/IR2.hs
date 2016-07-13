module IR2 where

-- >>> arr 10 (\x -> x + x)
-- ((%x + %x) for %x in 0…10₃₂)

-- ~~~>

-- %len := Assign (Int 32 10)
-- %arr := Alloca %len 
-- For %len : %ix 
--   %x := Binop Add %ix %ix
--   Write %arr[%ix] %x

import Prelude.Extras
import Bound (Var(..))
import Bound.Scope.Simple
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

import Control.Lens

import qualified Exp as Exp
import Codegen
import Variable
import Declarations
import Types

v :: Prog Identity Op
v = vv <&> Id??0 <&> Reference

vv :: Prog Identity [Char]
vv = Assign (Int 32 10) 
   $ abs1 "len" 
   $ Alloca (Identity "len") 
   $ abs1 "arr"
   $ For (Identity "len") (abstract1 "ix" 
      $ Binop Add (Identity "ix") (Identity "ix") 
      $ abs1 "x"
      $ Write (Identity "arr") (Identity "ix") (Identity "x")
      $ Br)
   $ Ret (Identity "arr")

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
  = Br
  | Ret (id a) 
  | Alloca (id a) (Prog (Scope () id) a)
  | Assign E (Prog (Scope () id) a)
  | Binop BINOP (id a) (id a) (Prog (Scope () id) a)
  | For (id a) (Scope () (Prog id) a) (Prog id a)
  | Write (id a) (id a) (id a) (Prog id a)
  deriving (Functor, Foldable, Traversable)

instance (Functor id, Eq1 id, Eq a) => Eq (Prog id a) where
  Br == Br = True

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
  Br -> [ "br" ]

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

  For (Identity x) body rest -> 
    [ "for " ++ show x ++ "(" ++ "" ++ ")" ]
    ++
    -- [ show (inst1 undefined body)  ]
    -- ++
    foo xs rest

  Write _ _ _ _ -> undefined 

  a -> error ""

inst1 :: forall op b a. Monad op => op a -> Prog (Scope b op) a -> Prog op a
inst1 = go instantiate1
  where
    go :: forall f g u. (forall v. op v -> f v -> g v) -> (op u -> Prog f u -> Prog g u)
    go f x = \case
      Ret o               -> Ret (f x o)
      Alloca size rest    -> Alloca (f x size)              (recurBound rest)
      Assign exp rest     -> Assign exp                     (recurBound rest)
      Binop op o1 o2 rest -> Binop op (f x o1) (f x o2)     (recurBound rest)
      For id body    rest -> For (f x id) (recurLocal body) (recurNoVar rest)
      

      where
        recurBound :: Prog (Scope () f) u -> Prog (Scope () g) u
        recurBound = go (hoistScope . f . fmap F) x

        recurNoVar :: Prog f u -> Prog g u
        recurNoVar = go f x

        recurLocal :: Scope () (Prog f) u -> Scope () (Prog g) u
        recurLocal = hoistScope (go f (fmap F x))


-- hoistScope :: (f (Var b a) -> g (Var b a)) -> Scope b f a -> Scope b g a 

-- data Prog₀ a = Ret a | Alloc a (Prog₁ a) | E := Prog₁ a | Add a a (Prog₁ a) | ...

-- data Prog₁ a = Ret (Scope () I a) | Alloc (Scope () I a) (Prog₂ a) | E := Prog₂ a | Add (Scope () I a) (Scope () I a) (Prog₂ a) | ...

-- data Prog₂ a 
--   = Ret (Scope () (Scope () I) a) 
--   | Alloc (Scope () (Scope () I) a) (Prog₃ a)
--   | E := Prog₂ a | Add (Scope () I a) (Scope () I a) (Prog₂ a) | ...

abs1 :: forall op a. (Functor op, Eq a) => a -> Prog op a -> Prog (Scope () op) a
abs1 = go abstract1
  where
    go :: forall f g u. 
          (forall v. Eq v => v ->      f v ->      g v)
       ->           (Eq u => u -> Prog f u -> Prog g u)
    go f x = \case
      Br                    -> Br
      Ret o                 -> Ret (f x o)
      Alloca size      rest -> Alloca (f x size)                  (recurBound rest)
      Assign exp       rest -> Assign exp                         (recurBound rest)
      Binop op o1 o2   rest -> Binop op (f x o1) (f x o2)         (recurBound rest)
      For id body      rest -> For (f x id) (recurLocal body)     (recurNoVar rest)
      Write arr ix val rest -> Write (f x arr) (f x ix) (f x val) (recurNoVar rest)

      where
        recurLocal :: Scope () (Prog f) u -> Scope () (Prog g) u
        recurLocal = hoistScope (go f (F x))

        recurNoVar :: Prog f u -> Prog g u
        recurNoVar = go f x

        recurBound :: Prog (Scope () f) u -> Prog (Scope () g) u
        recurBound = go (hoistScope . f . F) x

lyftari :: (forall v. Eq v => v ->      f v ->      g v) 
        -> (forall u. Eq u => u -> Prog f u -> Prog g u)
lyftari f x = \case
  Br -> Br
  Ret id -> Ret (f x id)
  -- Alloca id rest -> 
  --   Alloca (f x id) (lyftari (hoistScope . f . fmap F) rest)


  -- | Alloca (id a) (Prog (Bound.Scope.Simple.Scope () id) a)
  -- | Assign E (Prog (Bound.Scope.Simple.Scope () id) a)
  -- | Binop BINOP
  --         (id a)
  --         (id a)
  --         (Prog (Bound.Scope.Simple.Scope () id) a)
  -- | For (id a) (Bound.Scope.Simple.Scope () (Prog id) a) (Prog id a)
  -- | Write (id a) (id a) (id a) (Prog id a)
  


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

