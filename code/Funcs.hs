{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}

import System.Process
import System.IO
import System.Exit
import Control.Applicative
import Data.Maybe
import Text.Read (readMaybe)
import Prelude 
import Data.Monoid 
import Data.Ord
import Data.List
import Data.Function
import qualified Data.Foldable as F
import qualified Data.Map as M
import Control.Monad.State

import Codegen
import Expr

-- comp ∶             (Exp) → Codegen String
-- comp ∶       (Exp → Exp) → Codegen String
-- comp ∶ (Exp → Exp → Exp) → Codegen String
class Comp a where
  comp ∷ a → Codegen ([String], String)

instance Comp Exp where
  comp ∷ Exp → Codegen ([String], String)
  comp e = fmap ([], ) (compile e)

instance Comp p ⇒ Comp (Exp → p) where
  comp ∷ (Exp → p) → Codegen ([String], String)
  comp f = do
    arg          ← [ "var" ++ show x | x ← fresh ]
    (args, code) ← comp (f (Var arg))

    return (arg : args, code)


compile ∷ Exp → Codegen String
compile (I n) = do
  instr ("add i64 0, " ++ show n)

compile (Add e₁ e₂) = do
  reg₁ ← compile e₁
  reg₂ ← compile e₂
  instr ("add i64 " ++ reg₁ ++ ", " ++ reg₂)

compile (Mul e₁ e₂) = do
  reg₁ ← compile e₁
  reg₂ ← compile e₂
  instr ("mul i64 " ++ reg₁ ++ ", " ++ reg₂)

compile (IfThenElse cond tru fls) = do
  ifthen ← addBlock "if.then"
  ifelse ← addBlock "if.else"
  ifcont ← addBlock "if.cont"

  cond ← compile cond
  test ← instr ("icmp ne i64 0, " ++ cond)

  terminate ("br i1 " ++ test ++ ", label %" ++ ifthen 
                              ++ ", label %" ++ ifelse)

  -- | if.then
  setBlock ifthen
  aaaa ← compile tru
  terminate ("br label %" ++ ifcont)
  ifthen ← getBlock

  -- | if.else
  setBlock ifelse
  bbbb ← compile fls
  terminate ("br label %" ++ ifcont)
  ifelse ← getBlock

  setBlock ifcont
  instr ("phi i64 [" ++ aaaa ++ ", %" ++ ifthen ++ "], "
              ++ "[" ++ bbbb ++ ", %" ++ ifelse ++ "]")

compile (Var str)    = do
  return ("%" ++ str)

compile (Fn₁ name a) = do
  param ← compile a
  instr ("call i64 @" ++ name ++ "(i64 " ++ param ++ ")")

compileExp ∷ Comp a ⇒ a → (([String], String), CodegenState)
compileExp exp = runCodegen $ do
  addBlock "entry" 
  (args, reg) ← comp exp
  reg ← terminate ("ret i64 " ++ reg)
  return (args, reg)

  -- instr ("tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i64 0, i64 0), i64 " ++ reg ++ ") nounwind")

pattern Stdout a ← (ExitSuccess, a, _)
pattern Stderr b ← (ExitFailure _, _, b)
pattern Int    n ← (readMaybe → Just (n ∷ Int))

run ∷ Comp a ⇒ a → [Int] → IO String
run exp xs = do
  let ((args, reg), code) = compileExp exp

      code₁ = M.toList (blocks code)
      code₂ = sortBy (comparing (index . snd)) code₁

  let args' = intercalate ", " [ "i64 %" ++ arg    | arg ← args ]
      xs'   = intercalate ", " [ "i64 "  ++ show x | x   ← xs   ]

  withFile "/tmp/foo.ll" WriteMode (\h → do
    hPutStrLn(h) "@.str = private unnamed_addr constant [4 x i8] c\"%d\\0A\\00\", align 1"
    hPutStrLn(h) "declare i32 @printf(i8* nocapture, ...) nounwind"
    hPutStrLn(h) ""
    hPutStrLn(h) "declare i64 @putint(i64 %x)"
    hPutStrLn(h) ""
    hPutStrLn(h) "declare i64 @plusone(i64 %x)"
    hPutStrLn(h) ""
    hPutStrLn(h) ("define i64 @foobar(" ++ args' ++ ") {")

    forM_ code₂ $ \(label, MkBB{..}) → do
      hPutStrLn(h) (label ++ ":")
      forM_ instructions $ \instruction → do
        hPutStrLn(h) ("  " ++ instruction)
      hPutStrLn(h) ("  " ++ terminator)

    -- hPutStrLn(h) "  ret i64 %x"
    hPutStrLn(h) "}"
    hPutStrLn(h) ""
    
    hPutStrLn(h) "define i32 @main() {"
    hPutStrLn(h) ("  %1 = call i64 @foobar(" ++ xs' ++ ")")
    hPutStrLn(h) "  tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i64 0, i64 0), i64 %1) nounwind"
    hPutStrLn(h) "  ret i32 0"
    hPutStrLn(h) "}")

  readProcess "lli" [
      -- "-load=/home/baldur/repo/code/libfuncs.so", 
      "/tmp/foo.ll"
    ] ""

{-
@.str = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1
declare i32 @printf(i8* nocapture, ...) nounwind

define i32 @main() {
  %1 = add i64 0, 42
  %2 = tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i64 0, i64 0), i64 %1) nounwind
  ret i32 0
}
-}

eval ∷ Exp → Integer
eval = \case
  I a              → a
  Add a b          → eval a + eval b
  Mul a b          → eval a * eval b
  IfThenElse c a b 
    | eval c /= 0  → eval a 
    | otherwise    → eval b

