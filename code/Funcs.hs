{-# LANGUAGE RebindableSyntax, PatternSynonyms, UnicodeSyntax, LambdaCase, ViewPatterns, ScopedTypeVariables, RecordWildCards #-}

-- http://ellcc.org/demo/index.cgi

-- Metaphors don't inspire definitions but insight and intuition.

-- IC -IC-optimisation→  IC 
--    -Code-Generation→  Symbolic instructions
--    -Target-code-opt→  Symbolic instructions
--    -Machine-code-gen→ Bit patterns

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
import Data.Foldable (for_, traverse_)
import qualified Data.Foldable as F hiding (And, and)
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Writer
import Numeric.Natural
import qualified Data.Bits as B

import Control.Lens hiding (index, (<.))

import Codegen
import Exp
import Repr
import Util
import Vect

type Label = String

compile ∷ Exp a → Codegen String
compile (LitI n) = do
  return (show n)

compile Fls = do
  return "false"

compile Tru = do
  return "true"

compile (Add e₁ e₂) = do
  reg₁ ← compile e₁
  reg₂ ← compile e₂
  add reg₁ reg₂

compile (Mul e₁ e₂) = do
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
  xor "i64" reg₁ reg₂

compile (Not bool) = do
  b ← compile bool
  xor "i1" b "true"

compile (e₁ :≤: e₂) = do
  reg₁ ← compile e₁
  reg₂ ← compile e₂

  reg₁ ≤ reg₂
  -- "conv" `namedInstr` printf "zext i1 %s to i64" bit

compile (Var str)    = do
  return ("%" ++ str)

-- compile (Fn₁ name a) = do
--   param ← compile a
--   instr (printf "call i64 @%s(i64 %s" name param)

-- http://www.stephendiehl.com/llvm/#if-expressions
compile (If cond tru fls) = do
  if_then ← addBlock "if.then"
  if_else ← addBlock "if.else"
  if_cont ← addBlock "if.cont"

  condition ← compile cond
  br condition if_then if_else

  let 
    block ∷ (Exp a, Label) → Codegen (String, Label)
    block (val, lbl) = do
      setBlock lbl
      foo ← compile val
      jmp if_cont

      -- This is important (see link) “The problem is that theifthen
      -- expression may actually itself change the block that the
      -- Builder is emitting into if, for example, it contains a
      -- nested "if/then/else" expression. Because calling cgen
      -- recursively could arbitrarily change the notion of the
      -- current block, we are required to get an up-to-date value for
      -- code that will set up the Phi node.”
      lbl ← getBlock
      return (foo, lbl)

  true  ← block (tru, if_then)
  false ← block (fls, if_else)

  setBlock if_cont
  φ (showTy tru) true false

-- compile (While condTest body init) = mdo
--   undefined 

compile (Pair x y) = do
  let insNum ∷ String → Int → String → Codegen String
      insNum pair index reg = 
        namedInstr "updated" 
         (printf "insertvalue %%pairi64i64 %s, i64 %s, %d" pair reg index)

      mkPair ∷ String → String → Codegen String
      mkPair x y = do
       let initVal = "{i64 undef, i64 undef}"
       retVal₁ ← insNum initVal 0 x
       retVal₂ ← insNum retVal₁ 1 y
       return retVal₂

  val₁  ← compile x
  val₂  ← compile y
  
  mkPair val₁ val₂

compile (Fst pair) = do
  π(0) =<< compile pair

compile (Snd pair) = do
  π(1) =<< compile pair

compile (Arr len ixf) = mdo
  entry   ← getBlock
  loop_1  ← addBlock "arr.loop1"
  loop_2  ← addBlock "arr.loop2"
  post    ← addBlock "arr.post"

  arrLength  ← compile len
  arrMem     ← mallocStr arrLength
  buffer     ← getBuffer arrMem

  jmp loop_1

  -- | arr.loop
  -- Increment from [0…len) 
  setBlock loop_1
  i₀  ← φ "i64" ("0", entry)
                (i₁ , loop_2')
  i₁  ← incr i₀

  keepGoing ← i₀ <. arrLength
  br keepGoing loop_2 post

  setBlock loop_2 

  ptr ← namedInstr "ptr" (printf "getelementptr i64* %s, i64 %s" buffer i₀)

  value ← compile (ixf (Var (tail i₀)))
  loop_2' ← getBlock

  ptr ≔ value
  jmp loop_1

  setBlock post 

  -- | arr.post
  setBlock post

  instr_ (printf "call void @printString(%%String* %s)" arrMem)
  return arrMem

-- compile (Len (Arr len _)) = do
--   compile len

compile (Len arr) = do
  compile arr >>= getLength >>= i32toi64

compile (ArrIx arr index) = do
  array_val ← compile arr
  index_val ← i32toi64 =<< compile index

  buffer   ← getBuffer array_val

  elt_ptr ← namedInstr "ptr" 
    (printf "getelementptr i64* %s, i64 %s" buffer index_val)
  namedInstr "length" (printf "load i64* %s" elt_ptr)

--   -- ix  ← compile index
--   -- ptr ← "ptr" `namedInstr` printf "getelementptr i64* %%%s, i64 %s" mem ix
--   -- "load" `namedInstr` printf "load i64, i64* %s" ptr
--   undefined 

-- compile (ArrIx (Var mem) index) = do
--   ix  ← compile index
--   ptr ← "ptr" `namedInstr` printf "getelementptr i64* %%%s, i64 %s" mem ix
--   "load" `namedInstr` printf "load i64* %s" ptr


pattern Stdout a ← (ExitSuccess, a, _)
pattern Stderr b ← (ExitFailure _, _, b)

pattern Int      ∷ Int → String
pattern Int    n ← (readMaybe → Just (n ∷ Int))

getOutput ∷ Comp a ⇒ a → [Integer] → IO String
getOutput exp xs = do
  let ((args, reg, returnType), code) = compileExp exp

      code₁ = M.toList (blocks code)
      code₂ = sortBy (comparing (index . snd)) code₁

  let comma = intercalate ", "
      args' = comma $ ["i64* %mem1bbb", "i64* %mem2bbb"]
                   ++ [ "i64 %" ++ arg    | arg ← args ]
      xs'   = comma $ ["i64* %mem1.b", "i64* %mem2.b"]
                   ++ [ "i64 "  ++ show x | x   ← xs   ]

  withFile "/tmp/foo.ll" WriteMode (\h → do
    hPutStrLn(h) "@.str = private unnamed_addr constant [4 x i8] c\"%d\\0A\\00\", align 1"
    hPutStrLn(h) "@fmt  = internal constant [5 x i8] c\"%d, \\00\""
    hPutStrLn(h) "@nil  = internal constant [1 x i8] c\"\\00\""
    hPutStrLn(h) "@tru  = internal constant [5 x i8] c\"True\\00\""
    hPutStrLn(h) "@fls  = internal constant [6 x i8] c\"False\\00\""
    hPutStrLn(h) "@pair = internal constant [13 x i8] c\"(%llu, %llu)\\00\""
    hPutStrLn(h) "%pairi64i64 = type { i64, i64 }"
    hPutStrLn(h) "%String = type { i64*, i32 }"

    hPutStrLn(h) "declare i32  @printf(i8* nocapture, ...) nounwind"
    hPutStrLn(h) "declare i64  @putint(i64)"
    hPutStrLn(h) "declare i64  @plusone(i64)"
    hPutStrLn(h) "declare i32  @puts(i8*)"
    hPutStrLn(h) "declare i8*  @memcpy(i8*, i8*, i32)"
    hPutStrLn(h) "declare i8*  @malloc(i32)"
    hPutStrLn(h) "declare void @free(i8*)"
    hPutStrLn(h) ""
    hPutStrLn(h) showBit
    hPutStrLn(h) initialise
    hPutStrLn(h) buttCode
    hPutStrLn(h) nlCode
    hPutStrLn(h) printArray
    hPutStrLn(h) printString
    hPutStrLn(h) initPair
    hPutStrLn(h) showPair
    hPutStrLn(h) stringCreateDefault
    hPutStrLn(h) ""

    hPrintf(h)   "define %s @foobar(%s) {\n" returnType args' 

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

    hPrintf(h)   "  %%1 = call %s @foobar(%s)\n" returnType xs'
    -- hPutStrLn(h) "  call void @printArray(i64* %mem1.b)"
    -- hPutStrLn(h) "  call void @printArray(i64* %mem2.b)"
    -- hPutStrLn(h) "  call void @nl()"
    hPutStrLn(h) (dispatch returnType)
    hPutStrLn(h) "  ret i32 0"
    hPutStrLn(h) "}")

      -- "-load=/home/baldur/repo/code/libfuncs.so", 
  foo ← readProcessWithExitCode "lli-3.6" ["/tmp/foo.ll"] "" 
  case foo of
    Stdout output → return output
    _             → return $ show foo

blabla ∷ IO ()
blabla = do
  system "llc-3.6 -filetype=obj /tmp/foo.ll -o /tmp/foo.o"
  system "gcc -o /tmp/foo /tmp/foo.o  -L/usr/lib/i386-linux-gnu -lstdc++"
  system "/tmp/foo" 
    & void

dispatch ∷ String → String
dispatch "i1"  = 
  "  call void @showbit(i1 %1)"
dispatch "i64" = 
  "  tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i64 0, i64 0), i64 %1) nounwind"
dispatch "%pairi64i64" = 
  "  call void @showpair(%pairi64i64 %1)"
dispatch "%String*" = 
  "  "

run' ∷ Exp a → [Integer] → String
run' exp xs = let
  ((args, reg, _), code) = compileExp exp

  code₁ = M.toList (blocks code)
  code₂ = sortBy (comparing (index . snd)) code₁

  args' = intercalate ", " [ "i64 %" ++ arg    | arg ← args ]
  xs'   = intercalate ", " [ "i64 "  ++ show x | x   ← xs   ]

  in unlines [ 
    unlines $ (label ++ ":") : map ("  " ++) (instructions ++ [terminator]) 
  | (label, MkBB{..}) ← code₂ 
  ]

eval ∷ Exp a → a
eval = \case
  LitI a   → a
  LitB b   → b
  Not b    → not (eval b)
  Pair a b → (eval a, eval b)
  Fst a    → fst (eval a)
  Snd a    → snd (eval a)
  Add a b  → eval a + eval b
  a :≤: b  → eval a <= eval b
  And a b  → eval a && eval b
  Mul a b  → eval a * eval b
  Xor a b  → B.xor (eval a) (eval b)
  If c a b 
    | eval c    → eval a
    | otherwise → eval b
  Arr len ixf → let
    ℓ  = eval len
    is = [0..ℓ-1]
    in undefined
  a → error ("ERROR: " ++ show a)

-- dsp ∷ Exp → IO ()
-- dsp exp = do
--   foo_ll ← readFile "/tmp/foo.ll"
--   putStrLn foo_ll
--   as ← readProcess "llvm-as-3.4" [] "bound"
--   return ()

-- Feldspar compiler's input is a core language program represented as
-- a graph.  This graph is first transformed to an ABSTRACT
-- IMPERAITIVE PROGRAM that is no longer purely functional. 

foo ∷ Exp Bool → Exp Int
foo a = if a then 2 else 10

-- Compile

-- comp ∶ (Exp a)                 → Codegen String
-- comp ∶ (Exp a → Exp b)         → Codegen String
-- comp ∶ (Exp a → Exp b → Exp c) → Codegen String
class Comp a where
  comp ∷ a → Codegen ([String], String, Maybe String)

instance Comp (Exp a) where
  comp ∷ Exp a → Codegen ([String], String, Maybe String)
  comp exp = do
    compiled ← compile exp
    return ([], compiled, Just (showTy exp))

instance Comp p ⇒ Comp (Exp a → p) where
  comp ∷ (Exp a → p) → Codegen ([String], String, Maybe String)
  comp f = do
    arg                   ← [ printf "var%d" x | x ← fresh ]
    (args, code, Nothing) ← comp (f (Var arg))

    return (arg : args, code, Nothing)

foobar ∷ Codegen ([String], String, Maybe String) 
       → Codegen ([String], String, Maybe String)
foobar codegen = do
  (args, reg, Just returnType) ← codegen
  reg ← terminate (printf "ret %s %s" returnType reg)
  undefined 

compileExp ∷ Comp a ⇒ a → (([String], String, String), CodegenState)
compileExp exp = runCodegen $ do
  -- Create the entry basic block
  prologue

  (args, reg, Just returnType) ← free'd (comp exp)

  

  reg ← terminate (printf "ret %s %s" returnType reg)

  return (args, reg, returnType)

  where
    prologue ∷ Codegen ()
    prologue = void (addBlock "entry")

    -- Free pointers in epilogue
    free'd ∷ Codegen a → Codegen a
    free'd = useOutput (traverse_ free) 

run ∷ Exp a → IO ()
run exp = putStrLn =<< getOutput exp []

runI ∷ Exp Int → IO ()
runI = run

code ∷ Exp a → IO ()
code exp = putStrLn (run' exp [])

codeI ∷ Exp Int → IO ()
codeI = code

test' ∷ Exp a → IO String
test' exp = getOutput exp []

compileRun ∷ Read a ⇒ Exp a → IO a
compileRun exp = 
  read . last . lines <$> test' exp


