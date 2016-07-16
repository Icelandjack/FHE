module IR2 where

-- >>> arr 10 (\x -> x + x)
-- ((%x + %x) for %x in 0…10₃₂)

-- ~~~>

-- %len := Assign (Int 32 10)
-- %arr := Alloca %len 
-- For %len : %ix 
--   %x := Binop Add %ix %ix
--   Write %arr[%ix] %x

import Data.Void
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

import Control.Lens hiding (assign)

import qualified Exp as Exp
import Codegen
import Variable
import Declarations
import Types

-- uu :: Prog Identity Op
-- uu = t $ For (I "uuu") (abs1 "uuu" (For (I "u") (abs1 "u" vv) vv)) vv

-- t vv = vv <&> Id??0 <&> Reference

-- v :: Prog Identity Op
-- v = vv <&> Id??0 <&> Reference

-- vv = Assign (Int 32 10) 
--    $ abs1 "len" 
--    $ Alloca (I "len") 
--    $ abs1 "arr"
--    $ For (I "len") (abs1 "ix" 
--       $ Binop Add (I "ix") (I "ix") 
--       $ abs1 "x"
--       $ Write (I "arr") (I "ix") (I "x")
--       $ End)
--    $ Ret (I "arr")

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
    Float fl   -> show fl
    Double dbl -> show dbl

data Binop = Add | Mul | Sub deriving Eq

instance Show Binop where
  show = \case
    Add -> "+"
    Mul -> "*"
    Sub -> "-"

-- for me, for should have type:
--   for :: Prog (Int, Int) -> Prog (Int -> a) -> Prog a
-- alloca on the other hand
--   alloca :: Prog Int -> Prog (a -> b) -> Prog b
-- or something of this kind
data Term id a
  = End
  | Ret (id a) 
  deriving (Eq, Functor, Foldable, Traversable)

data Inst id a
  = For (id a) (Prog (Scope () id) a) 
  | Write (id a) (id a) (id a)
  deriving (Functor, Foldable, Traversable)

data Expr id a
  = Alloca (id a)
  | Assign E
  | MkBinop Binop (id a) (id a) 
  deriving (Functor, Foldable, Traversable)

data Prog id a 
  = MkInst (Inst id a) (Prog id a)
  | MkExpr (Expr id a) (Prog (Scope () id) a)
  | MkTerm (Term id a)
  deriving (Functor, Foldable, Traversable)

instance (Functor id, Eq1 id, Eq a) => Eq (Prog id a) where
  MkInst inst₁ then₁ == MkInst inst₂ then₂ = inst₁ ==# inst₂ && then₁ == then₂
  MkExpr term₁ rest₁ == MkExpr term₂ rest₂ = term₁ ==# term₂ && rest₁ == rest₂
instance (Functor id, Eq1 id, Eq a) => Eq (Expr id a) where
  Alloca id₁        == Alloca id₂        = id₁ ==# id₂
  Assign e₁         == Assign e₂         = e₁ == e₂
  MkBinop op₁ a₁ b₁ == MkBinop op₂ a₂ b₂ = 
    op₁ == op₂ && a₁ ==# a₂ && b₁ ==# b₂
instance (Functor id, Eq1 id, Eq a) => Eq (Inst id a) where
  For x body          == For x' body'        = x    ==# x' && body == body'
  Write arr₁ ix₁ val₁ == Write arr₂ ix₂ val₂ = arr₁ ==# arr₂ && ix₁ ==# ix₂ && val₁ ==# val₂
instance (Eq1 id, Functor id) => Eq1 (Inst id) where
instance (Eq1 id, Functor id) => Eq1 (Expr id) where
instance (Eq1 id, Functor id) => Eq1 (Term id) where
  End     ==# End     = True 
  Ret id₁ ==# Ret id₂ = id₁ ==# id₂

instance (Op ~ a, Identity ~ id) => Show (Prog id a) where
  show = init . unlines . showProg (map ("",) [0..])

-- showProg (((\(str, n) -> Reference (Id (str ++ "var") n)) -> var):vars) = \case

toVar (str, n) = Reference (Id (str ++ "var") n)

showProg :: [(String, Natural)] -> Prog Identity Op -> [String]
showProg (var:vars) = \case
  MkInst inst next -> 
    [ showInstr (var:over (traverse._1) ('l':) vars) inst ]
    ++ 
    showProg vars next

  MkExpr inst rest -> 
    [ showExpr var' inst ]
    ++
    showProg vars (inst1 (I var') rest) where var' = toVar var

  MkTerm End -> 
    [ "end" ]

  MkTerm (Ret (I a)) -> 
    [ "ret " ++ show a ]

showInstr :: [(String, Natural)] -> Inst Identity Op -> String
showInstr (var:vars) = \case
  For id body -> unlines $
    [ "for " ++ show var ++ " in range(" ++ show id ++ ")" ]
    ++
    map ("  " ++) (showProg (var:vars) (inst1 (I (toVar var)) body)) 

  Write (I arr) (I ix) (I val) -> 
    show arr ++ "[" ++ show ix ++ "] := " ++ show val

showExpr :: Op -> Expr Identity Op -> String
showExpr var = \case
  Alloca (I id) -> 
    show var ++ " := alloca " ++ show id

  Assign exp ->
    show var ++ " := " ++ show exp
  
  MkBinop Add (I a) (I b) -> 
    show var ++ " := " ++ show a ++ " + " ++ show b

  MkBinop Mul (I a) (I b) -> 
    show var ++ " := " ++ show a ++ " * " ++ show b

-- inst1Inst :: forall op b a. Monad op => op a -> Inst (Scope b op) a -> Inst op a
-- inst1Inst = go instantiate1
--   where
ins1Inst :: forall op f g u. Functor op 
  => (forall v. op v -> f v -> g v) 
  -> (op u -> Inst f u -> Inst g u)
ins1Inst f x = \case
  For id body -> For (f x id) (recurBoundInst body)
  Write a b c -> Write (f x a) (f x b) (f x c) 
  where
    recurBoundInst :: Prog (Scope () f) u -> Prog (Scope () g) u
    recurBoundInst = ins1 (hoistScope . f . fmap F) x

    recurNoVar :: Inst f u -> Inst g u
    recurNoVar = ins1Inst f x

ins1Expr :: 
     (forall v. op v -> f v -> g v) 
  -> (op u -> Expr f u -> Expr g u)
ins1Expr f x = \case
  Alloca id      -> Alloca (f x id)
  Assign expr    -> Assign expr
  MkBinop op a b -> MkBinop op (f x a) (f x b)

ins1 :: forall op f g u. Functor op 
  => (forall v. op v -> f v -> g v) 
  -> (op u -> Prog f u -> Prog g u)
ins1 f x = \case
  MkInst inst next -> 
    MkInst (ins1Inst f x inst) (recurNoVar next)
  
  MkExpr inst rest -> 
    MkExpr (ins1Expr f x inst) (recurBound rest)

  MkTerm End -> MkTerm End

  MkTerm (Ret id) -> MkTerm (Ret (f x id))

  where
    recurBound :: Prog (Scope () f) u -> Prog (Scope () g) u
    recurBound = ins1 (hoistScope . f . fmap F) x
  
    recurNoVar :: Prog f u -> Prog g u
    recurNoVar = ins1 f x

    recurLocal :: Scope () (Prog f) u -> Scope () (Prog g) u
    recurLocal = hoistScope (ins1 f (fmap F x))

inst1 :: forall op b a. Monad op => op a -> Prog (Scope b op) a -> Prog op a
inst1 = ins1 instantiate1
      -- End                  -> End
      -- Ret o               -> Ret (f x o)
      -- Alloca size    rest -> Alloca (f x size)              (recurBound rest)
      -- Assign exp     rest -> Assign exp                     (recurBound rest)
      -- Binop op o1 o2 rest -> Binop op (f x o1) (f x o2)     (recurBound rest)

abs1 :: forall op a. (Functor op, Eq a) => a -> Prog op a -> Prog (Scope () op) a
abs1 = go abstract1
  where
    go :: forall f g u. 
          (forall v. Eq v => v ->      f v ->      g v)
       ->           (Eq u => u -> Prog f u -> Prog g u)
    go f x = \case
      -- End                    -> End
      -- Ret o                 -> Ret (f x o)
      -- Alloca size      rest -> Alloca (f x size)                  (recurBound rest)
      -- Assign exp       rest -> Assign exp                         (recurBound rest)
      -- Binop op o1 o2   rest -> Binop op (f x o1) (f x o2)         (recurBound rest)
      -- For id body      rest -> For (f x id) (recurBound body)     (recurNoVar rest)
      -- Write arr ix val rest -> Write (f x arr) (f x ix) (f x val) (recurNoVar rest)

      where
        recurLocal :: Scope () (Prog f) u -> Scope () (Prog g) u
        recurLocal = hoistScope (go f (F x))

        recurNoVar :: Prog f u -> Prog g u
        recurNoVar = go f x

        recurBound :: Prog (Scope () f) u -> Prog (Scope () g) u
        recurBound = go (hoistScope . f . F) x

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

-- (Op -> 
type ExprCont = ContT Expr_ (Gen Natural)
type Expr_    = Prog Identity Op

type InstrCont = ContT Instr_ (Gen Natural)
type Instr_    = Inst Identity NoVarBound

data NoVarBound = NoVarBound

-- assign :: E -> ExprCont (Identity Op)
-- assign exp = ContT $ \k -> do
--   var  <- [ Reference (Id "var" v) | v <- gen ]
--   body <- k (I var)
--   pure $ Assign exp (abs1 var body)

-- mkBinder :: (Prog (Scope () Identity) Op -> Prog Identity Op) -> ExprCont (Identity Op)
-- mkBinder f = ContT $ \ĸ -> do
--   var  <- [ Reference (Id "var" v) | v <- gen ]
--   body <- ĸ (I var)

--   pure $ f (abs1 var body)

-- mkNoVar :: (a -> a) -> ContT a (Gen Natural) NoVarBound
-- mkNoVar f = ContT $ \ĸ -> 
--   f <$> ĸ NoVarBound

-- runProgm :: ContT (Prog id a) (Gen Natural) (id a) -> Prog id a
-- runProgm :: HAHA (Identity String) -> Prog Identity String
-- runProgm :: HAHA (Maybe Op) -> Prog Identity Op
-- runProgm (ContT prog) = runGen @Natural $ prog $ \case
--   Nothing -> pure End
--   Just x  -> pure (Ret (Identity x))

-- runInstr :: HAHA () -> Prog Identity ()
-- runInstr (ContT prog) = runGen @Natural $ prog 

-- runInstr :: InstrCont NoVarBound -> Instr
-- runInstr (ContT prog) = runGen $ prog $ \NoVarBound -> 
--   pure End
