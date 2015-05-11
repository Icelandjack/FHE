{-# LANGUAGE UnicodeSyntax #-}

module Codegen where

import Prelude
import qualified Data.Map as M
import Control.Monad.State
import Data.Functor
import Text.Printf

import Expr
  
type Instruction = String

data BasicBlock = MkBB {
  instructions ∷ [Instruction],
  terminator   ∷ String,
  index        ∷ Int
} deriving Show

data CodegenState = MkCodegen {
  currentBlock ∷ String,
  blocks       ∷ M.Map String BasicBlock,
  blockCount   ∷ Int, 
  nameUsage    ∷ M.Map String Int,
  count        ∷ Int
} deriving Show

type Codegen = State CodegenState

-- | Get a unique string.
-- If it exists in name supply then we add stuff to it.
uniqueName ∷ String → Codegen String 
uniqueName name = do
  names ← gets nameUsage

  case M.lookup name names of
    Nothing → name <$ modify (\s→s{nameUsage=M.insert name 1 names}) 
    Just i  → case M.lookup (name ++ show i) names of
      Nothing → name ++ show i <$ modify (\s→s{nameUsage=M.insert (name ++ show i) 1 names}) 
      Just j  → uniqueName (name ++ "e")

emptyBlock ∷ Int → String → BasicBlock 
emptyBlock index name = MkBB [] (error (name ++ ": NEEDS A TERMINATOR")) index

emptyState ∷ CodegenState
emptyState = MkCodegen "entry" M.empty 0 M.empty 0 

-- TODO: vars ∶ [(String, Operand)] to { symtab = vars }
runCodegen ∷ Codegen a → (a, CodegenState)
runCodegen codegen = runState codegen emptyState

entry ∷ Codegen String
entry = gets currentBlock

addBlock ∷ String → Codegen String
addBlock str = do
  bls        ← gets blocks
  blockCnt   ← gets blockCount
  blockName  ← uniqueName str
  
  modify (\state → state {
    blocks     = M.insert blockName (emptyBlock blockCnt blockName) bls,
    blockCount = blockCnt + 1
  })
  
  return blockName

setBlock ∷ String → Codegen String
setBlock newBlock = do
  modify (\state → state { currentBlock = newBlock })
  return newBlock

getBlock ∷ Codegen String
getBlock = gets currentBlock

modifyBlock ∷ BasicBlock → Codegen ()
modifyBlock new = do
  active ← gets currentBlock
  modify $ \s → s { blocks = M.insert active new (blocks s) }

fresh ∷ Codegen Int
fresh = do
  i ← gets count
  modify (\s → s { count = i + 1 })
  return (i + 1)

current ∷ Codegen BasicBlock
current = do
  c ← gets currentBlock
  blks ← gets blocks
  case M.lookup c blks of
    Just x  → return x
    Nothing → error $ "No such block: " ++ show c

-- global = @
-- local  = %
namedInstr ∷ String → Instruction → Codegen String
namedInstr var newInstructions = do
  ref ← fresh
  blk ← current

  let instrs   = instructions blk
      localVar = "%" ++ var ++ show ref

  modifyBlock (blk { 
    instructions = instrs ++ [localVar ++ " = " ++ newInstructions] 
  })
  
  return localVar

instr ∷ Instruction → Codegen String
instr = namedInstr "u"

instr_ ∷ Instruction → Codegen ()
instr_ newInstructions = do
  blk ← current

  let instrs   = instructions blk

  modifyBlock (blk { 
    instructions = instrs ++ [newInstructions] 
  })

terminate ∷ String → Codegen String
terminate newTerm = do
  block ← current
  modifyBlock (block { terminator = newTerm })
  return newTerm

initialise ∷ String
initialise = unlines [
  "define void @initialise(i64* %arr) {",
  "pre:",
  "  br label %loop",
  "",
  "loop:",
  "  %i.1 = phi i64 [ 0,    %pre  ],",
  "                 [ %i.2, %loop ]",
  "  %i.2 = add i64 %i.1, 1",
  "",
  "  %ptr.1 = getelementptr i64* %arr, i64 %i.1",
  "",
  -- "  %val = add i64 %i.1, 5",
  -- "",
  -- "  store i64 %val, i64* %ptr.1",
  "  store i64 0, i64* %ptr.1",
  "",
  "  %cmp = icmp eq i64 %i.1, 9",
  "  br i1 %cmp, label %post, label %loop",
  "",
  "post:",
  "  ret void",
  "}"]

printArray ∷ String
printArray = unlines [
  "define void @printArray(i64* %arr) {",
  "pre:",
  "  br label %loop",
  "loop:",
  "  %i.1   = phi i64 [ 0,    %pre  ],",
  "                   [ %i.2, %loop ]",
  "  %i.2   = add i64 %i.1, 1",
  "  %ptr.1 = getelementptr i64* %arr, i64 %i.1",
  "  %val.1 = load i64* %ptr.1",
  "  call void @butt(i64 %val.1)",
  "  %cmp   = icmp eq i64 %i.1, 9",
  "  br i1 %cmp, label %post, label %loop",
  "post:",
  "  call void @nl()",
  "  ret void",
  "}"]

buttCode ∷ String
buttCode = unlines [
 "define void @butt(i64 %x) {",
  "  call i32 (i8*, ...)* @printf(i8* getelementptr([5 x i8]* @fmt, i64 0, i64 0), i64 %x)",
  "  ret void",
  "}"]

nlCode ∷ String
nlCode = unlines [
   "define void @nl() {",
  "  call i32 @puts(i8* getelementptr([1 x i8]* @nil, i32 0, i32 0))",
  "  ret void",
  "}"]

{-
@.str = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1
declare i32 @printf(i8* nocapture, ...) nounwind

define i32 @main() {
  %1 = add i64 0, 42
  %2 = tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i64 0, i64 0), i64 %1) nounwind
  ret i32 0
}
-}

butt ∷ String → Codegen ()
butt n = do
  instr_ (printf "call void @butt(i64 %s)" n)
  nl

nl ∷ Codegen ()
nl = instr_ (printf "call void @nl()")

incr ∷ String → Codegen String
incr = add "1"

add ∷ String → String → Codegen String
add reg₁ reg₂ = namedInstr "add" (printf "add i64 %s, %s" reg₁ reg₂)

mul ∷ String → String → Codegen String
mul reg₁ reg₂ = namedInstr "mul" (printf "mul i64 %s, %s" reg₁ reg₂)

and ∷ String → String → Codegen String
and reg₁ reg₂ = namedInstr "and" (printf "and i64 %s, %s" reg₁ reg₂)

xor ∷ String → String → Codegen String
xor reg₁ reg₂ = namedInstr "xor" (printf "xor i64 %s, %s" reg₁ reg₂)

φ ∷ String → (String, String) → (String, String) → Codegen String
φ τ (a, b) (c, d) = namedInstr "phi" (printf "phi %s [%s, %%%s], [%s, %%%s]" τ a b c d)

jmp ∷ String → Codegen String
jmp label = terminate ("br label %" ++ label)

(≠) ∷ String → String → Codegen String
reg₁ ≠ reg₂ = namedInstr "neq" (printf "icmp ne i64 %s, %s" reg₁ reg₂)

(≡) ∷ String → String → Codegen String
reg₁ ≡ reg₂ = namedInstr "eq"  (printf "icmp eq i64 %s, %s" reg₁ reg₂)

(≤) ∷ String → String → Codegen String
reg₁ ≤ reg₂ = namedInstr "sle"  (printf "icmp sle i64 %s, %s" reg₁ reg₂)

br ∷ String → String → String → Codegen String
br a b c = terminate (printf "br i1 %s, label %%%s, label %%%s" a b c)

(≔) ∷ String → String → Codegen ()
loc ≔ gildi = instr_ (printf "store i64 %s, i64* %s" loc gildi)
