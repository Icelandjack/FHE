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
import Control.Applicative
import Data.Maybe
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

import GHC.Read
import Test.QuickCheck.Monadic hiding (run)
import qualified Test.QuickCheck.Monadic as M
import Control.Lens.Internal.Setter
import Control.Lens.TH

import Control.Lens hiding (index, (<.), Indexed)

import Codegen
import Exp
import Repr
import Util
import Vect
import Types

import Data.Proxy
  
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
  xor "i32" reg₁ reg₂

compile (Not bool) = do
  b ← compile bool
  xor "i1" b "true"

compile (e₁ :≤: e₂) = do
  reg₁ ← compile e₁
  reg₂ ← compile e₂

  reg₁ ≤ reg₂
  -- "conv" `namedInstr` printf "zext i1 %s to i64" bit

compile (Var n)    = do
  return ("%var" ++ show n)

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

compile (Pair x y) = do
  let insNum ∷ String → Int → String → Codegen String
      insNum pair index reg = 
        namedInstr "updated" 
         (printf "insertvalue %%pairi32i32 %s, i32 %s, %d" pair reg index)

      mkPair ∷ String → String → Codegen String
      mkPair x y = do
       let initVal = "{i32 undef, i32 undef}"
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

compile (While n condTest body init) = mdo
  entry       ← getBlock
  while_test  ← addBlock "while.test"
  while_body  ← addBlock "while.body"
  while_post  ← addBlock "while.post"

  init_val ← compile init
  jmp while_test

  -- TEST
  setBlock while_test
  val_1 ← φ "i32" (init_val, entry)
                  (val_2,    while_body)

  variable ← addInstr n ("add i32 0, " ++ val_1)

  keepGoing ← compile condTest
  br keepGoing while_body while_post

  -- BODY
  setBlock while_body
  val_2 ← compile body 
  jmp while_test

  -- POST
  setBlock while_post
  return variable

compile (Arr len n ixf) = mdo
  entry   ← getBlock
  loop_1  ← addBlock "arr.loop1"
  loop_2  ← addBlock "arr.loop2"
  post    ← addBlock "arr.post"

  arrLength ← compile len
  arrMem    ← mallocStr arrLength
  buffer    ← getBuffer("i32") arrMem

  jmp loop_1

  -- | arr.loop
  -- Increment from [0…len) 
  setBlock loop_1
  i₀  ← φ "i32" ("0", entry)
                (i₁ , loop_2')
  i₁  ← incr i₀

  keepGoing ← i₀ <. arrLength
  br keepGoing loop_2 post

  setBlock loop_2 

  ptr ← "ptr" `namedInstr` printf "getelementptr i32* %s, i32 %s" buffer i₀

  value ← undefined  --compile (ixf (Var (tail i₀)))
  loop_2' ← getBlock

  ptr ≔ value
  jmp loop_1

  setBlock post 

  -- | arr.post
  setBlock post

  return arrMem

-- compile (Len (Arr len _)) = do
--   compile len

compile (Len arr) = do
  compile arr >>= getLength -- >>= i32toi64

compile (ArrIx arr index) = do
  array_val ← compile arr
  index_val ← {- i32toi64 =<< -} compile index

  buffer   ← getBuffer("i32") array_val

  elt_ptr ← namedInstr "ptr" 
    (printf "getelementptr i32* %s, i32 %s" buffer index_val)
  namedInstr "length" (printf "load i32* %s" elt_ptr)

compile (Lam n body) = 
  undefined 

foobarDef ∷ (([String], t, String), CodegenState) → [Integer] → Writer [String] ()
foobarDef ((args, reg, returnType), code) xs = do
  tell [printf "define %s @foobar(%s) {" returnType args']
  foobarBody sortedCode
  tell ["}"]

  where
  foobarBody ∷ MonadWriter [String] f ⇒ [(String, BasicBlock)] → f ()
  foobarBody code = do
    for_ code $ \(label, MkBB{..}) → do
      tell [label ++ ":"]
      for_ _instructions $ \instruction → do
        tell ["  " ++ instruction]
      tell ["  " ++ _terminator]

  sortedCode ∷ [(String, BasicBlock)]
  sortedCode = M.toList (_blocks code)
    & sortOn (_index' . snd)

  comma = intercalate ", "

  isArray ∷ Bool
  isArray = returnType == "%Arr*"

  args' = comma $ [ "%Arr** %out" | isArray    ] 
               ++ [ "i32 %" ++ arg   | arg ← args ]

mainDef ∷ (([String], t, String), CodegenState) → [Integer] → Writer [String] ()
mainDef ((args, reg, returnType), code) xs = do
  let isArray ∷ Bool
      isArray = returnType == "%Arr*"

      xs' = intercalate ", " $
          [ "%Arr** %arrmem" | isArray ]
       ++ [ "i32 "  ++ show x   | x ← xs  ]

  tell [ "define i32 @main(i32 %argc, i8** %argv) {" ]

  tell [ "  %arrmem = alloca %Arr*"             | isArray   ]
  tell [ printf "  %%1 = call %s @foobar(%s)" returnType xs' ]

  tell [ "  %arr = load %Arr** %arrmem"         | isArray   ]
  tell [ "  call void @printArr(%Arr* %arr)" | isArray   ]

  tell [dispatch returnType,
        "  ret i32 0",
        "}"]

-- Feldspar compiler's input is a core language program represented as
-- a graph.  This graph is first transformed to an ABSTRACT
-- IMPERAITIVE PROGRAM that is no longer purely functional. 

-- Compile

-- comp ∶ (Exp a)                 → Codegen String
-- comp ∶ (Exp a → Exp b)         → Codegen String
-- comp ∶ (Exp a → Exp b → Exp c) → Codegen String

blah ∷ (Exp a → Exp b) → ([Name], Exp b)
blah f = ([n], body) where
  n    = 1 + maxLam body
  body = f (Var n)

blah2 ∷ (Exp a → Exp b → Exp c) → ([Name], Exp c)
blah2 f = ([n, m], body) where
  n    = 1 + maxLam body
  m    = 1 + n
  body = f (Var n) (Var m)

a ∷ Exp a → ([Name], Exp a)
a exp = ([], exp)

b ∷ (Exp a → Exp b) → ([Name], Exp b)
b exp = ([n], body) where
  n    = 1 + maxLam body
  body = exp (Var n)

c ∷ (Exp a → Exp b → Exp c) → ([Name], Exp c)
c exp = ([n, m], body) where
  n    = 1 + maxLam body
  m    = 1 + n
  body = exp (Var n) (Var m)

d ∷ (Exp a → Exp b → Exp c → Exp d) → ([Name], Exp d)
d exp = ([n, m, i], body) where
  n    = 1 + maxLam body
  m    = 1 + n
  i    = 1 + m
  body = exp (Var n) (Var m) (Var i)

comp ∷ Exp a → Codegen ([String], String, Maybe String)
comp exp = do
  compiled ← compile exp
  return ([], compiled, Just (showTy exp))

-- class Comp a where
--   comp ∷ a → Codegen ([String], String, Maybe String)

-- instance Comp (Exp a) where
--   comp ∷ Exp a → Codegen ([String], String, Maybe String)
--   comp exp = do
--     compiled ← compile exp
--     return ([], compiled, Just (showTy exp))

-- instance Comp p ⇒ Comp (Exp a → p) where
--   comp ∷ (Exp a → p) → Codegen ([String], String, Maybe String)
--   comp f = do
--     arg                   ← fresh
--     (args, code, Nothing) ← comp (f (Var arg))

--     return (arg : args, code, Nothing)

-- compileExp ∷ Comp a ⇒ a → (([String], String, String), CodegenState)
compileExp ∷ Exp a → (([String], String, String), CodegenState)
compileExp exp = runCodegen $ do
  -- Create the entry basic block
  prologue

  (args, reg, Just returnType) ← free'd (comp exp)

  when (returnType == "%Arr*")$ do
    instr_ (printf "store %%Arr* %s, %%Arr** %%out" reg)

  reg ← terminate (printf "ret %s %s" returnType reg)

  return (args, reg, returnType)

  where
    prologue ∷ Codegen ()
    prologue = void (addBlock "entry")

    -- Free pointers in epilogue
    free'd ∷ Codegen a → Codegen a
    free'd = id -- useOutput (traverse_ free) 

-- Run
run ∷ Exp a → IO ()
run = (getOutput ?? []) >=> putStrLn

runI ∷ Exp Int → IO ()
runI = run

runRead ∷ Read a ⇒ Exp a → IO a
runRead exp = read . last . lines <$> getOutput exp []

-- Code
code ∷ Exp a → IO ()
code exp = compileExp exp
  & (foobarDef ?? [])
  & execWriter
  & traverse_ putStrLn

codeI ∷ Exp Int → IO ()
codeI = code

msg ∷ Exp a → IO ()
msg exp = do
  getOutput exp [] 

  system "llc-3.6 -filetype=obj /tmp/foo.ll -o /tmp/foo.o && gcc -o /tmp/foo /tmp/foo.o -L/usr/lib/i386-linux-gnu -lstdc++ && /tmp/foo"
    & void

-- -- otp ∷ Vector (Exp Int) → Vector (Exp Int) → Vector (Exp Int)
-- -- otp = map₂ (⊕)

-- -- _Indexed ∷ Type a ⇒ Iso' (Vector (Exp a)) (Exp [a]) 
-- -- _Indexed = iso  (\(Indexed l ixf) → Arr l ixf) $ \case
-- --   Arr l ixf → Indexed l ixf

-- runPure ∷ Comp exp ⇒ exp → [Integer] → Writer [String] ()
runPure ∷ Exp a → [Integer] → Writer [String] ()
runPure exp xs = do
  let result = compileExp exp

  tell constants
  tell declarations
  tell definitions

  foobarDef result xs
  mainDef   result xs

-- getOutput ∷ Comp a ⇒ a → [Integer] → IO String
getOutput ∷ Exp a → [Integer] → IO String
getOutput exp xs = do
  runPure exp xs
    & execWriter
    & unlines
    & writeFile "/tmp/foo.ll"

  -- "-load=/home/baldur/repo/code/libfuncs.so", 
  foo ← readProcessWithExitCode "lli-3.6" ["/tmp/foo.ll"] "" 
  case foo of
    Stdout output → return output
    _             → return (show foo)


allvars ∷ Traversal' (Exp a) Name
allvars f = \case
  Var n  → Var <$> f n
  LitI i → pure $  LitI i
  LitB b → pure $  LitB b
  While n a b c → While <$> f n    <*> allvars f a <*> allvars f b <*> allvars f c
  Fn₂ a b c d e → Fn₂   <$> pure a <*> pure b      <*> pure c      <*> allvars f d <*> allvars f e
