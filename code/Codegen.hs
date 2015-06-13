{-# LANGUAGE UnicodeSyntax #-}

module Codegen where

import Prelude
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader {- rm ltr -}
import Data.Functor
import Data.Functor.Identity
import Text.Printf
import Data.Foldable
import Data.Traversable

import Util

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

type Codegen = WriterT (Epilogue Instruction) (State CodegenState)

newtype Epilogue a 
  = Epilogue [a] 
  deriving (Show, Monoid, Functor, Foldable, Traversable)

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
runCodegen ∷ ∀a. Codegen a → (a, CodegenState)
runCodegen codegen = runState noEpilogue emptyState

  where
    -- We've already used the epilogue so we are only interested in
    -- the return value
    noEpilogue ∷ State CodegenState a
    noEpilogue = evalWriterT codegen

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

  let instrs = instructions blk

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

printString ∷ String
printString = unlines [
  "define void @printString(%String* %str) {",
  "pre:",
  "  %buf.ptr = getelementptr %String* %str, i32 0, i32 0",
  "  %len.ptr = getelementptr %String* %str, i32 0, i32 1",
  "  %buffer  = load i64** %buf.ptr",
  "  %length  = load i32*  %len.ptr",
  "  br label %loop.1",
  "",
  "loop.1:",
  "  %i.1  = phi i32 [ 0,    %pre    ],",
  "                  [ %i.2, %loop.2 ]",
  "  %i.2  = add i32 1, %i.1",
  "",
  "  %keepGoing = icmp slt i32 %i.1, %length",
  "  br i1 %keepGoing, label %loop.2, label %post",
  "",
  "loop.2:",
  "  %ptr = getelementptr i64* %buffer, i32 %i.1",
  "  %val = load i64* %ptr",
  "  call void @butt(i64 %val)",
  "  br label %loop.1",
  "",
  "post:",
  "  call void @nl()",
  "  ret void",
  "}"]

stringCreateDefault ∷ String
stringCreateDefault = unlines [
  "define fastcc i8* @String_Create_Default(%String* %this, i32 %elts) nounwind {",
  "  ; Initialize 'buffer'.",
  "  %buff.ptr   = getelementptr %String* %this, i32 0, i32 0",
  "  %sizeof     = mul i32 %elts, 8",
  "  %buff.bytes = call i8* @malloc(i32 %sizeof)",
  "  %buff.i64   = bitcast i8* %buff.bytes to i64* ",
  "  store i64* %buff.i64, i64** %buff.ptr",
  "  ; Initialize 'length'.",
  "  %len.ptr = getelementptr %String* %this, i32 0, i32 1",
  "  store i32 %elts, i32* %len.ptr",
  "  ret i8* %buff.bytes",
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

showBit ∷ String
showBit = unlines [
  "define void @showbit(i1 %bit) {",
  "  br i1 %bit, label %true, label %false",
  "true:",
  "  call i32 @puts(i8* getelementptr([5 x i8]* @tru, i64 0, i64 0))",
  "  ret void",
  "false:",
  "  call i32 @puts(i8* getelementptr([6 x i8]* @fls, i64 0, i64 0))",
  "  ret void",
  "}"] 

initPair ∷ String
initPair = unlines [
  "define void @initpair(%pairi64i64* %pair, i64 %fst, i64 %snd) {",
  "  %pair.1 = getelementptr %pairi64i64* %pair, i32 0, i32 0",
  "  %pair.2 = getelementptr %pairi64i64* %pair, i32 1, i32 0",
  "  store i64 %fst, i64* %pair.1",
  "  store i64 %snd, i64* %pair.2",
  "  ret void",
  "}"]

showPair ∷ String
showPair = unlines [
  "define void @showpair(%pairi64i64 %pair) {",
  "  %fst = extractvalue %pairi64i64 %pair, 0",
  "  %snd = extractvalue %pairi64i64 %pair, 1",
  "  call i32 (i8*, ...)* @printf(i8* getelementptr ([13 x i8]* @pair, i64 0, i64 0), i64 %fst, i64 %snd)",
  "  call void @nl()",
  "  ret void ",
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

prnt ∷ String → Codegen ()
prnt str = void $ instr (printf "call i32 (i8*, ...)* @printf(i8* %s)" str)

nl ∷ Codegen ()
nl = instr_ (printf "call void @nl()")

incr ∷ String → Codegen String
incr = add "1"

malloc ∷ String → WriterT (Epilogue Instruction) (State CodegenState) String
malloc size = do
  mem ← namedInstr "mem" (printf "call i8* @malloc(i32 %s)" size)
  tell (Epilogue [mem])

  -- arr ← namedInstr "arr" (printf "bitcast i8* %s to i64*" mem)
  -- %foo = bitcast i8* %1 to %Foo*
  return mem

mallocStr ∷ String → Codegen String
mallocStr size = do
  let sizeofString ∷ Int
      sizeofString = 8 {- i64* buffer -} + 4 {- i32 len -} 

  sizeofBuf  ← instr (printf "mul i32 8, %s" size)

  string_mem ← malloc (show sizeofString)
  string     ← namedInstr "str" (printf "bitcast i8* %s to %%String*" string_mem)

  buffer_mem ← malloc sizeofBuf
  buffer     ← namedInstr "buf" (printf "bitcast i8* %s to i64*" buffer_mem)

  buffer_ptr ← namedInstr "buffer.ptr"$
    printf "getelementptr %%String* %s, i32 0, i32 0" string
  length_ptr ← namedInstr "string.ptr"$
    printf "getelementptr %%String* %s, i32 0, i32 1" string

  instr_ (printf "store i64* %s, i64** %s" buffer buffer_ptr)
  instr_ (printf "store i32  %s, i32*  %s" size   length_ptr)

  return string

free ∷ String → Codegen ()
free memptr = do
  begin   ← addBlock "free.begin"
  close   ← addBlock "free.close"
  
  notNull ← namedInstr "neq" (printf "icmp ne i8* %s, null" memptr)

  br notNull begin close

  setBlock begin 
  -- butt "42"
  instr_ (printf "call void @free(i8* %s)" memptr)
  jmp close

  void (setBlock close)

type Type = String

add ∷ String → String → Codegen String
add reg₁ reg₂ = namedInstr "add" (printf "add i64 %s, %s" reg₁ reg₂)

mul ∷ String → String → Codegen String
mul reg₁ reg₂ = namedInstr "mul" (printf "mul i64 %s, %s" reg₁ reg₂)

and ∷ String → String → Codegen String
and reg₁ reg₂ = namedInstr "and" (printf "and i1 %s, %s" reg₁ reg₂)

xor ∷ Type → String → String → Codegen String
xor ty reg₁ reg₂ = namedInstr "xor" (printf "xor %s %s, %s" ty reg₁ reg₂)

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

(<.) ∷ String → String → Codegen String
reg₁ <. reg₂ = namedInstr "sle"  (printf "icmp slt i64 %s, %s" reg₁ reg₂)

br ∷ String → String → String → Codegen String
br a b c = terminate (printf "br i1 %s, label %%%s, label %%%s" a b c)

(≔) ∷ String → String → Codegen ()
loc ≔ gildi = instr_ (printf "store i64 %s, i64* %s" gildi loc)

π ∷ Int → String → Codegen String
π(n) pair = "fst" `namedInstr` printf "extractvalue %%pairi64i64 %s, %d" pair n

-- Get the underlying buffer
getBuffer ∷ String → Codegen String
getBuffer = 
  namedInstr "buffer.ptr" . printf "getelementptr %%String* %s, i32 0, i32 0"
  >=>
  namedInstr "buffer"     . printf "load i64** %s" 

getLength ∷ String → Codegen String
getLength = 
  namedInstr "len.ptr" . printf "getelementptr %%String* %s, i32 0, i32 1" 
  >=>
  namedInstr "length"  . printf "load i32* %s"

i32toi64 ∷ String → Codegen String
i32toi64 = namedInstr "asi32" . printf "zext i32 %s to i64"
