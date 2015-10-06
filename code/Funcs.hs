{-# LANGUAGE RebindableSyntax, PatternSynonyms, UnicodeSyntax, LambdaCase, ViewPatterns, ScopedTypeVariables, RecordWildCards, OverloadedStrings #-}

-- Feldspar compiler's input is a core language program represented as
-- a graph.  This graph is first transformed to an ABSTRACT
-- IMPERAITIVE PROGRAM that is no longer purely functional. 

-- http://ellcc.org/demo/index.cgi

-- Metaphors don't inspire definitions but insight and intuition.

-- IC -IC-optimisation→  IC 
--    -Code-Generation→  Symbolic instructions
--    -Target-code-opt→  Symbolic instructions
--    -Machine-code-gen→ Bit patterns

module Funcs where

import Data.String
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
import Data.Bifunctor
import Control.Exception (evaluate)

import GHC.Read
import Test.QuickCheck.Monadic hiding (run)
import qualified Test.QuickCheck.Monadic as M
import Data.Data
import Data.Typeable
import Debug.Trace

import Formatting
import Formatting.ShortFormatters

import Control.Lens hiding (op, index, (<.), Indexed)

import Codegen
import Exp
import Repr
import Util
import Vect
import Types
import Variable
import Declarations

-- `compile' has to deal with more than just registers so the return
-- works with operands `Op' that are either references (`Name') or
-- constants (`ConstTru', `ConstFls', `ConstNum Int').
compile ∷ Exp a → Codegen Op
compile (Var var) = do
  pure (Reference var)

compile (LitI n) = do
  pure (ConstNum n)

compile Fls = do
  pure ConstFls

compile Tru = do
  pure ConstTru

compile (UnOp op _ _ a) = do
  reg ← compile a

  compileUnop op reg

compile (BinOp op _ _ a b) = do
  reg₁ ← compile a
  reg₂ ← compile b

  compileBinop op reg₁ reg₂

-- http://www.stephendiehl.com/llvm/#if-expressions
compile (If cond tru fls) = do
  if_then ← newBlock "if.then"
  if_else ← newBlock "if.else"
  if_cont ← newBlock "if.cont"

  condition ← compile cond
  br condition if_then if_else

  let 
    block ∷ (Exp a, Label) → Codegen (Op, Label)
    block (val, label) = do
      setBlock label
      foo ← compile val
      jmp if_cont

      -- This is important (see link) “The problem is that theifthen
      -- expression may actually itself change the block that the
      -- Builder is emitting into if, for example, it contains a
      -- nested "if/then/else" expression. Because calling cgen
      -- recursively could arbitrarily change the notion of the
      -- current block, we are required to get an up-to-date value for
      -- code that will set up the Phi node.”
      label ← getBlock
      return (foo, label)

  true  ← block (tru, if_then)
  false ← block (fls, if_else)

  setBlock if_cont
  φ (showTy tru) true false
    <&> Reference

-- compile (Pair x y) = do
--   let insNum ∷ String → Int → String → Codegen String
--       insNum pair index reg = 
--         namedInstr "updated" 
--          (PRINTF "insertvalue %%pairi32i32 %s, i32 %s, %d" pair reg index)

--       mkPair ∷ String → String → Codegen String
--       mkPair x y = do
--        let initVal = "{i32 undef, i32 undef}"
--        retVal₁ ← insNum initVal 0 x
--        retVal₂ ← insNum retVal₁ 1 y
--        return retVal₂

--   val₁  ← compile x
--   val₂  ← compile y
  
--   mkPair val₁ val₂

-- compile (Fst pair) = do
--   π(0) =<< compile pair

-- compile (Snd pair) = do
--   π(1) =<< compile pair

compile (While var condTest body init) = mdo
  -- Create blocks
  entry       ← getBlock
  while_cond  ← newBlock "while.cond"
  while_body  ← newBlock "while.body"
  while_post  ← newBlock "while.post"

  -- Compile the initial value of the while expression
  init_val ← compile init
  jmp while_cond

  -- TEST
  setBlock while_cond
  val_1 ← φ "i32" (init_val, entry)
                  (val_2,    while_body)

  -- When compiling
  --   While "%lam_1" (5 < "%lam_1") ("%lam_1" + 1) 0
  -- "%lam_1" is the variable bound by the binding construct While and
  -- must refer to the LLVM register "val_1"
  --   val_1 ← φ …
  -- which is a fresh variable. So we replace all occurances of
  -- "%lam_1" in the conditional and body before compiling it.
  keepGoing ← compile (rename var val_1 condTest)
  br keepGoing while_body while_post

  -- BODY
  setBlock while_body

  -- Same as with the conditional expression.
  val_2     ← compile (rename var val_1 body)
  jmp while_cond

  -- POST
  setBlock while_post
  pure (Reference val_1)

compile (Arr len var ixf) = mdo
  entry   ← getBlock
  loop_1  ← newBlock "arr.loop1"
  loop_2  ← newBlock "arr.loop2"
  post    ← newBlock "arr.post"

  arrLength ← compile len
  arrMem    ← mallocStr arrLength
  buffer    ← getBuffer("i32") arrMem

  jmp loop_1

  -- | arr.loop
  -- Increment from [0…len) 
  setBlock loop_1
  i₀  ← φ "i32" (ConstNum  0,  entry)
                (Reference i₁, loop_2')
  i₁  ← incr i₀

  keepGoing ← namedOp "slt"
    ("icmp slt i32 " %sh% ", " %sh) i₀ arrLength

  br keepGoing loop_2 post

  setBlock loop_2 

  ptr ← namedInstr "ptr" 
    ("getelementptr i32* " %sh% ", i32 " %sh) buffer i₀

  value    ← compile (rename var i₀ ixf)
  loop_2'  ← getBlock

  ptr ≔ value
  jmp loop_1

  -- | arr.post
  setBlock post

  pure (Reference arrMem)

-- -- compile (Len (Arr len _)) = do
-- --   compile len

-- compile (Len arr) = do
--   compile arr >>= getLength -- >>= i32toi64

-- compile (ArrIx arr index) = do
--   array_val ← compile arr
--   index_val ← {- i32toi64 =<< -} compile index

--   buffer   ← getBuffer("i32") array_val

--   elt_ptr ← namedInstr "ptr" 
--     (PRINTF "getelementptr i32* %s, i32 %s" buffer index_val)
--   namedInstr "length" (PRINTF "load i32* %s" elt_ptr)

-- compile (Lam n body) = 
--   undefined 

foobarDef ∷ (([Name], {- t, -} String), CodegenState) → [Integer] → Writer [String] ()
foobarDef ((args, {- reg, -} returnType), code) xs = do
  emit ("define "%s%" @foobar("%comma%") {") returnType args'
  genBody sortedCode
  emit "}"

  where
  genBody ∷ [(String, BasicBlock)] → Writer [String] ()
  genBody code = 
    for_ code 
      genBasicBlock 

  genBasicBlock ∷ (String, BasicBlock) → Writer [String] ()
  genBasicBlock (label, basicBlock) = do
    for_ (basicBlock^.instructions) 
      (indented string)
    indented string (basicBlock^.terminator)

  sortedCode ∷ [(String, BasicBlock)]
  sortedCode = M.toList (code^.blocks)
                 & sortOn (view (_2.index'))
                 & map (first show)

  isArray = returnType == "%Arr*"
  args'   = [ "%Arr** %out"       | isArray    ] 
         ++ [ "i32 %" ++ show arg | arg ← args ]

mainDef ∷ (([Name], {-t, -} String), CodegenState) → [Integer] → Writer [String] ()
mainDef ((args, {-reg, -}returnType), code) xs = do
  let isArray ∷ Bool
      isArray = returnType == "%Arr*"

      xs' = [ "%Arr** %arrmem"  | isArray ]
         ++ [ "i32 "  ++ show x | x ← xs  ]

  emit "define i32 @main(i32 %argc, i8** %argv) {"

  indentedWhen isArray
    "%arrmem = alloca %Arr*"

  indented ("%1 = call "%s%" @foobar("%comma%")") returnType xs'

  indentedWhen isArray 
    "%arr = load %Arr** %arrmem"

  indentedWhen isArray 
    "call void @printArr(%Arr* %arr)"

  tell [dispatch returnType,
        "  ret i32 0",
        "}"]

-- comp ∶ (Exp a)                 → Codegen String
-- comp ∶ (Exp a → Exp b)         → Codegen String
-- comp ∶ (Exp a → Exp b → Exp c) → Codegen String
class Comp a where
  comp ∷ a → Codegen (Op, [Name], Maybe String)

instance Comp (Exp a) where
  comp ∷ Exp a → Codegen (Op, [Name], Maybe String)
  comp exp = do
    -- Make all variables and binders unique 
    exp' ← makeFresh exp

    compiled ← compile exp'
    pure (compiled, [], Just (showTy exp'))

instance Comp p ⇒ Comp (Exp a → p) where
  comp ∷ (Exp a → p) → Codegen (Op, [Name], Maybe String)
  comp partAppliedExp = do
    var ← uniqueVarName "arg"
    let exp = partAppliedExp (Var var)
    (op, args, ty) ← comp exp 
    pure (op, var : args, ty)

compileExp ∷ Comp a ⇒ a → (([Name], String), CodegenState)
compileExp exp = runCodegen $ do
  (reg, args, Just returnType) ← free'd (comp exp)
  when (returnType == "%Arr*")$ do
    instr_ ("store %Arr* " %sh% ", %Arr** %out") reg

  terminate ("ret "%s%" "%op) returnType reg

  return (args, returnType)

  where
    -- Free pointers in epilogue
    free'd ∷ Codegen a → Codegen a
    free'd = id -- useOutput (traverse_ free) 

-- Run
run ∷ Exp a → IO ()
run = getOutput [] >=> putStrLn

runI ∷ Exp Int → IO ()
runI = run

runRead ∷ Read a ⇒ Exp a → IO a
runRead exp = read.last.lines <$> getOutput [] exp

-- Code
code ∷ Exp a → IO ()
code exp = compileExp exp
  & (foobarDef ?? [])
  & execWriter
  & traverse_ putStrLn

codeI ∷ Exp Int → IO ()
codeI = code

msg ∷ Comp exp ⇒ exp → IO ()
msg exp = do
  getOutput [] exp

  system "llc-3.6 -filetype=obj /tmp/foo.ll -o /tmp/foo.o && gcc -o /tmp/foo /tmp/foo.o -L/usr/lib/i386-linux-gnu -lstdc++ && /tmp/foo"
    & void

msgI ∷ Exp Int → IO ()
msgI = msg

-- runPure ∷ Comp exp ⇒ exp → [Integer] → Writer [String] ()
runPure ∷ Comp exp ⇒ [Integer] → exp → Writer [String] ()
runPure xs exp = do
  let result = compileExp exp

  tell constants
  tell declarations
  tell definitions

  foobarDef result xs
  mainDef   result xs

getOutput ∷ Comp exp ⇒ [Integer] → exp → IO String
getOutput xs exp = do
  runPure xs exp
    & execWriter
    & unlines
    & writeFile "/tmp/foo.ll"

  -- "-load=/home/baldur/repo/code/libfuncs.so", 
  foo ← readProcessWithExitCode "lli-3.6" ["/tmp/foo.ll"] "" 
  case foo of
    Stdout output → return output
    _             → return (show foo)

-- allvars ∷ Traversal' (Exp a) Name
-- allvars f = \case
--   Var n  → Var <$> f n
--   LitI i → pure $  LitI i
--   LitB b → pure $  LitB b
--   While n a b c → While <$> f n    <*> allvars f a <*> allvars f b <*> allvars f c
--   Fn₂ a b c d e → Fn₂   <$> pure a <*> pure b      <*> pure c      <*> allvars f d <*> allvars f e

-- fact ∷ Exp (Int, Int)
-- fact = 
--   while 
--     (\pair → Fst pair :≤: 4) 
--     (\pair → Pair (1 + Fst pair) (Snd pair))
--     (Pair 0 0)

-- otp ∷ Vector (Exp Int) → Vector (Exp Int) → Vector (Exp Int)
-- otp = map₂ (⊕)

-- _Indexed ∷ Type a ⇒ Iso' (Vector (Exp a)) (Exp [a]) 
-- _Indexed = iso  (\(Indexed l ixf) → Arr l ixf) $ \case
--   Arr l ixf → Indexed l ixf

