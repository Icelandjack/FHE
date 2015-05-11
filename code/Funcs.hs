{-# LANGUAGE RebindableSyntax, PatternSynonyms, UnicodeSyntax, LambdaCase, ViewPatterns, ScopedTypeVariables, RecordWildCards #-}

-- http://ellcc.org/demo/index.cgi

module Funcs where

import Data.Char
import System.Process
import System.IO
import System.Exit
import Control.Applicative
import Data.Maybe
import Text.Read (readMaybe)
import Text.Printf
import Prelude hiding (and)
import Data.Monoid 
import Data.Ord
import Data.List hiding (And, and)
import Data.Function
import Data.Foldable (for_)
import qualified Data.Foldable as F hiding (And, and)
import qualified Data.Map as M
import Control.Monad.State
import Numeric.Natural

import Codegen
import Expr
import Util
import Vect

type Label = String

compile ∷ Exp → Codegen String
compile (I n) = do
  return (show n)

compile (B False) = do
  return "0"

compile (B True) = do
  return "1"

compile (e₁ :+: e₂) = do
  reg₁ ← compile e₁
  reg₂ ← compile e₂
  add reg₁ reg₂

compile (e₁ :×: e₂) = do
  reg₁ ← compile e₁
  reg₂ ← compile e₂
  mul reg₁ reg₂

compile (And e₁ e₂) = do
  reg₁ ← compile e₁
  reg₂ ← compile e₂
  and reg₁ reg₂

compile (Xor e₁ e₂) = do
  reg₁ ← compile e₁
  reg₂ ← compile e₂
  xor reg₁ reg₂

compile (e₁ :≤: e₂) = do
  reg₁ ← compile e₁
  reg₂ ← compile e₂

  bit ← reg₁ ≤ reg₂
  "conv" `namedInstr` printf "zext i1 %s to i64" bit

compile (Var str)    = do
  return ("%" ++ str)

compile (Fn₁ name a) = do
  param ← compile a
  instr (printf "call i64 @%s(i64 %s" name param)

-- http://www.stephendiehl.com/llvm/#if-expressions
compile (If cond tru fls) = do
  ifthen ← addBlock "if.then"
  ifelse ← addBlock "if.else"
  ifcont ← addBlock "if.cont"

  condition ← compile cond
  test      ← "0" ≠ condition
  br test ifthen ifelse

  let 
    block ∷ (Exp, Label) → Codegen (String, Label)
    block (val, lbl) = do
      setBlock lbl
      foo ← compile val
      jmp ifcont

      -- This is important (see link) “The problem is that theifthen
      -- expression may actually itself change the block that the
      -- Builder is emitting into if, for example, it contains a
      -- nested "if/then/else" expression. Because calling cgen
      -- recursively could arbitrarily change the notion of the
      -- current block, we are required to get an up-to-date value for
      -- code that will set up the Phi node.”
      lbl ← getBlock
      return (foo, lbl)

  true  ← block (tru, ifthen)
  false ← block (fls, ifelse)

  setBlock ifcont
  φ "i64" true false

-- 
compile (While condTest body init) = mdo
  undefined 

compile (Arr _ ixf) = mdo
  entry ← getBlock
  loop  ← addBlock "arr.loop"
  post  ← addBlock "arr.post"

  jmp loop

  -- | arr.loop
  -- Increment from [0…len) and 
  setBlock loop
  i₀  ← φ "i64" ("0", entry)
                (i₁ , loop')
  i₁  ← incr i₀

  ptr   ← "ptr" `namedInstr` printf "getelementptr i64* %%mem1, i64 %s" i₀

  value ← compile (ixf (Var (tail i₀)))
  loop' ← getBlock 

  value ≔ ptr

  cmp ← "9" ≡ i₀
  
  br cmp post loop
  setBlock loop

  -- | arr.post
  setBlock post

  compile 42

compile (Len (Arr len ixf)) = do
  compile len

compile (ArrIx (Var mem) index) = do
  ix  ← compile index
  ptr ← "ptr" `namedInstr` printf "getelementptr i64* %%%s, i64 %s" mem ix
  "load" `namedInstr` printf "load i64* %s" ptr

compile (ArrIx arr index) = do
  -- ix  ← compile index
  -- ptr ← "ptr" `namedInstr` printf "getelementptr i64* %%%s, i64 %s" mem ix
  -- "load" `namedInstr` printf "load i64, i64* %s" ptr
  undefined 

compileExp ∷ Comp a ⇒ a → (([String], String), CodegenState)
compileExp exp = runCodegen $ do
  addBlock "entry" 
  (args, reg) ← comp exp
  reg ← terminate ("ret i64 " ++ reg)
  return (args, reg)

pattern Stdout a ← (ExitSuccess, a, _)
pattern Stderr b ← (ExitFailure _, _, b)
pattern Int    n ← (readMaybe → Just (n ∷ Int))

run ∷ Comp a ⇒ a → [Integer] → IO String
run exp xs = do
  let ((args, reg), code) = compileExp exp

      code₁ = M.toList (blocks code)
      code₂ = sortBy (comparing (index . snd)) code₁

  let comma = intercalate ", "
      args' = comma $ ["i64* %mem1", "i64* %mem2"]
                   ++ [ "i64 %" ++ arg    | arg ← args ]
      xs'   = comma $ ["i64* %mem1.b", "i64* %mem2.b"]
                   ++ [ "i64 "  ++ show x | x   ← xs   ]

  withFile "/tmp/foo.ll" WriteMode (\h → do
    hPutStrLn(h) "@.str = private unnamed_addr constant [4 x i8] c\"%d\\0A\\00\", align 1"
    hPutStrLn(h) "@fmt  = internal constant [5 x i8] c\"%d, \\00\""
    hPutStrLn(h) "@nil  = internal constant [1 x i8] c\"\\00\""

    hPutStrLn(h) "declare i32 @printf(i8* nocapture, ...) nounwind"
    hPutStrLn(h) ""
    hPutStrLn(h) "declare i64 @putint(i64 %x)"
    hPutStrLn(h) ""
    hPutStrLn(h) "declare i64 @plusone(i64 %x)"
    hPutStrLn(h) ""
    hPutStrLn(h) "declare i32 @puts(i8*)"
    hPutStrLn(h) ""

    hPutStrLn(h) initialise
    hPutStrLn(h) ""
    hPutStrLn(h) buttCode
    hPutStrLn(h) ""
    hPutStrLn(h) nlCode
    hPutStrLn(h) ""
    hPutStrLn(h) printArray
    hPutStrLn(h) ""

    hPrintf(h)   "define i64 @foobar(%s) {\n" args'

    forM_ code₂ $ \(label, MkBB{..}) → do
      hPrintf(h) "%s:\n" label
      forM_ instructions $ \instruction → do
        hPrintf(h) "  %s\n" instruction
      hPrintf(h) "  %s\n" terminator

    -- hPutStrLn(h) "  ret i64 %x"
    hPutStrLn(h) "}"
    hPutStrLn(h) ""
    
    hPutStrLn(h) "define i32 @main(i32 %argc, i8** %argv) {"
    hPutStrLn(h) "  %mem1.a = alloca [10 x i64]"
    hPutStrLn(h) "  %mem2.a = alloca [10 x i64]"
    hPutStrLn(h) "  %mem1.b = bitcast [10 x i64]* %mem1.a to i64*"
    hPutStrLn(h) "  %mem2.b = bitcast [10 x i64]* %mem2.a to i64*"
    hPutStrLn(h) "  call void @initialise(i64* %mem1.b)"
    hPutStrLn(h) "  call void @initialise(i64* %mem2.b)"

    let 
      msg_key ∷ [(Int, Int, Int)]
      msg_key = zipWith3 (,,) [0..] (map ord "Baldur") (map ord "ABCD12345")

    for_ msg_key $ \(index, msg, key) → do
      hPrintf(h) "  %%index%d = getelementptr i64* %%mem1.b, i64 %d\n" index index
      hPrintf(h) "  %%ind%d = getelementptr i64* %%mem2.b, i64 %d\n" index index
      hPrintf(h) "  store i64 %d, i64* %%index%d\n" msg index
      hPrintf(h) "  store i64 %d, i64* %%ind%d\n" key index

    hPutStrLn(h) ("  %1 = call i64 @foobar(" ++ xs' ++ ")")
    hPutStrLn(h) "  call void @printArray(i64* %mem1.b)"
    hPutStrLn(h) "  call void @printArray(i64* %mem2.b)"
    hPutStrLn(h) "  call void @nl()"
    hPutStrLn(h) "  tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i64 0, i64 0), i64 %1) nounwind"
    hPutStrLn(h) "  ret i32 0"
    hPutStrLn(h) "}")

  readProcess "lli" [
      -- "-load=/home/baldur/repo/code/libfuncs.so", 
      "/tmp/foo.ll"
    ] ""

run'' ∷ Exp → IO ()
run'' (exp ∷ Exp) = putStrLn (run' exp [])

run' ∷ Exp → [Integer] → String
run' exp xs = let
  ((args, reg), code) = compileExp exp

  code₁ = M.toList (blocks code)
  code₂ = sortBy (comparing (index . snd)) code₁

  args' = intercalate ", " [ "i64 %" ++ arg    | arg ← args ]
  xs'   = intercalate ", " [ "i64 "  ++ show x | x   ← xs   ]

  in unlines [ 
    unlines $ (label ++ ":") : map ("  " ++) (instructions ++ [terminator]) 
  | (label, MkBB{..}) ← code₂ 
  ]

eval ∷ Exp → Integer
eval = \case
  I a              → a
  Add a b          → eval a + eval b
  Mul a b          → eval a * eval b
  If c a b 
    | eval c /= 0  → eval a 
    | otherwise    → eval b
  Var{} → error "VAR"
  Fn{}  → error "FN"
  Lam{} → error "LAM"
  Arr{} → error "ARR"
  Len{} → error "LEN"

test ∷ Exp → IO String
test exp = run exp []

test' ∷ Exp → IO ()
test' exp = putStrLn =<< run exp []

-- dsp ∷ Exp → IO ()
-- dsp exp = do
--   foo_ll ← readFile "/tmp/foo.ll"
--   putStrLn foo_ll
--   as ← readProcess "llvm-as-3.4" [] "bound"
--   return ()

-- f ∶ M → ℂ
-- f ∶ M → ℂ

-- comp ∶             (Exp) → Codegen String
-- comp ∶       (Exp → Exp) → Codegen String
-- comp ∶ (Exp → Exp → Exp) → Codegen String
class Comp a where
  comp ∷ a → Codegen ([String], String)

instance Comp Exp where
  comp ∷ Exp → Codegen ([String], String)
  comp e = ([], ) <$> compile e

instance Comp p ⇒ Comp (Exp → p) where
  comp ∷ (Exp → p) → Codegen ([String], String)
  comp f = do
    arg          ← [ printf "var%d" x | x ← fresh ]
    (args, code) ← comp (f (Var arg))

    return (arg : args, code)

-- Feldspar compiler's input is a core language program represented as
-- a graph.  This graph is first transformed to an ABSTRACT
-- IMPERAITIVE PROGRAM that is no longer purely functional. 
