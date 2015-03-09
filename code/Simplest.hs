{-# LANGUAGE DatatypeContexts #-}
import System.Process
import System.IO
import System.Exit
import Control.Monad.Writer
import Control.Monad.State
import Text.Read (readMaybe)
-- import Test.QuickCheck

data Exp 
  = I Int 
  | Add Exp Exp 
  | Mul Exp Exp 
  deriving Show

instance Num Exp where
  fromInteger = I . fromInteger
  (+) = Add
  (*) = Mul

class Foo repr where
  i ∷ Int  → repr
  a ∷ repr → repr → repr
  m ∷ repr → repr → repr

instance Foo Exp where
  i = I
  a = Add
  m = Mul

getLog ∷ WriterT [String] (State Int) a → ([String], Int)
getLog exp = runState (execWriterT exp) 1

newLabel ∷ (MonadState b m, Num b) ⇒ m b
newLabel = do
  i ← get
  put (i + 1)
  return i

compile ∷ Exp → WriterT [String] (State Int) Int
compile (I n) = do
  i ← newLabel
  tell ["%" ++ show i ++ " = add i64 0, " ++ show n]
  return i
compile (Add e₁ e₂) = do
  reg₁ ← compile e₁
  reg₂ ← compile e₂
  i ← newLabel
  tell ["%" ++ show i ++ " = add i64 %" ++ show reg₁ ++ ", %" ++ show reg₂]
  return i
compile (Mul e₁ e₂) = do
  reg₁ ← compile e₁
  reg₂ ← compile e₂
  i ← newLabel
  tell ["%" ++ show i ++ " = mul i64 %" ++ show reg₁ ++ ", %" ++ show reg₂]
  return i

compileExp ∷ Exp → ([String], Int)
compileExp = fmap pred . getLog . compile

type NumFoo repr = (Num repr, Foo repr)

foo ∷ NumFoo repr ⇒ repr
foo = 4 + 10

pattern Stdout a ← (ExitSuccess, a, _)
pattern Int    n ← (readMaybe → Just (n ∷ Int))

run ∷ Exp → IO Int
run exp = do
  let (code, reg) = compileExp exp

  withFile "/tmp/foo.ll" WriteMode (\h → do
    hPutStrLn(h) "@.str = private unnamed_addr constant [4 x i8] c\"%d\\0A\\00\", align 1"
    hPutStrLn(h) "declare i32 @printf(i8* nocapture, ...) nounwind"
    hPutStrLn(h) ""
    hPutStrLn(h) "define i32 @main() {"
    mapM_ (hPutStrLn(h)) code
    hPutStrLn(h) ("  %" ++ show (reg + 1) ++ " = tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i64 0, i64 0), i64 %" ++ show reg ++ ") nounwind")
    hPutStrLn(h) "  ret i32 0"
    hPutStrLn(h) "}")

  Stdout (Int n) ← readProcessWithExitCode "lli" ["/tmp/foo.ll"] ""
  return n

