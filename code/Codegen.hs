{-# LANGUAGE OverloadedStrings #-}
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
import Control.Lens

import Data.Char

import Util

type Instruction = String

data Reg 
  = Reg String 
  | String String [Reg]
  deriving Show

data BasicBlock = MkBB {
  _instructions ∷ [Instruction],
  _terminator   ∷ String,
  _index'       ∷ Int
} deriving Show

data CodegenState = MkCodegen {
  _currentBlock ∷ String,
  _blocks       ∷ M.Map String BasicBlock,
  _blockCount   ∷ Int, 
  _nameUsage    ∷ M.Map String Int,
  _count        ∷ Int
} deriving Show

makeClassy       ''BasicBlock
makeClassyPrisms ''BasicBlock
makeClassy       ''CodegenState
makeClassyPrisms ''CodegenState

type Codegen = WriterT (Epilogue Instruction) (State CodegenState)

newtype Epilogue a 
  = Epilogue [a] 
  deriving (Show, Monoid, Functor, Foldable, Traversable)

-- | Get a unique string.
-- If it exists in name supply then we add stuff to it.
-- 
-- 
uniqueName ∷ String → Codegen String 
uniqueName name = do
  names ← gets _nameUsage

  case M.lookup name names of
    Nothing → name <$ modify (\s→s{_nameUsage=M.insert name 1 names}) 
    Just i  → case M.lookup (name ++ show i) names of
      Nothing → name ++ show i <$ modify (\s→s{_nameUsage=M.insert (name ++ show i) 1 names}) 
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
entry = gets _currentBlock

-- addBlock' ∷ String → Codegen' String
-- addBlock' str = do
--   blockCount' += 1
--   undefined 

addBlock ∷ String → Codegen String
addBlock str = do
  bls        ← gets _blocks
  blockCnt   ← gets _blockCount
  blockName  ← uniqueName str
  
  modify (\state → state {
    _blocks     = M.insert blockName (emptyBlock blockCnt blockName) bls,
    _blockCount = blockCnt + 1
  })
  
  return blockName

setBlock ∷ String → Codegen String
setBlock newBlock = do
  modify (\state → state { _currentBlock = newBlock })
  return newBlock

getBlock ∷ Codegen String
getBlock = gets _currentBlock

modifyBlock ∷ BasicBlock → Codegen ()
modifyBlock new = do
  active ← gets _currentBlock
  modify $ \s → s { _blocks = M.insert active new (_blocks s) }

fresh ∷ Codegen Int
fresh = do
  i ← gets _count
  modify (\s → s { _count = i + 1 })
  return (i + 1)

current ∷ Codegen BasicBlock
current = do
  c ← gets _currentBlock
  blks ← gets _blocks
  case M.lookup c blks of
    Just x  → return x
    Nothing → error $ "No such block: " ++ show c

-- global = @
-- local  = %
namedInstr ∷ String → Instruction → Codegen String
namedInstr var newInstructions = do
  ref ← fresh
  blk ← current

  let instrs   = _instructions blk
      localVar = "%" ++ var ++ show ref

  modifyBlock (blk { 
    _instructions = instrs ++ [localVar ++ " = " ++ newInstructions] 
  })
  
  return localVar

addInstr ∷ Int → String → Codegen String
addInstr (printf "%%var%d" → var) instr = do
  blk ← current

  modifyBlock (blk { 
    _instructions = _instructions blk ++ [printf "%s = %s" var instr]
  })

  return var

instr ∷ Instruction → Codegen String
instr = namedInstr "u"

instr_ ∷ Instruction → Codegen ()
instr_ newInstructions = do
  blk ← current

  let instrs = _instructions blk

  modifyBlock (blk { 
    _instructions = instrs ++ [newInstructions] 
  })

terminate ∷ String → Codegen String
terminate newTerm = do
  block ← current
  modifyBlock (block { _terminator = newTerm })
  return newTerm

printArr ∷ [String]
printArr = [
  "define void @printArr(%Arr* %str) {",
  "pre:",
  "  call i32 (i8*, ...)* @printf(i8* getelementptr([2 x i8]* @open, i32 0, i32 0))",
  "  %buf.ptr = getelementptr %Arr* %str, i32 0, i32 0",
  "  %len.ptr = getelementptr %Arr* %str, i32 0, i32 1",
  "  %buffer  = load i8** %buf.ptr",
  "  %cast    = bitcast i8* %buffer to i32*",
  "  %length  = load i32*  %len.ptr",
  "  %isEmpty = icmp eq i32 %length, 0",
  "  %length2 = add i32 %length, -1",
  "  br i1 %isEmpty, label %empty, label %loop.1",
  "loop.1:",
  "  %i.1  = phi i32 [ 0,    %pre    ],",
  "                  [ %i.2, %loop.2 ]",
  "  %i.2  = add i32 1, %i.1",
  "  %keepGoing = icmp slt i32 %i.1, %length2",
  "  %ptr = getelementptr i32* %cast, i32 %i.1",
  "  br i1 %keepGoing, label %loop.2, label %post",
  "loop.2:",
  "  %val = load i32* %ptr",
  "  call i32 (i8*, ...)* @printf(i8* getelementptr([3 x i8]* @fmt, i32 0, i32 0), i32 %val)",
  "  call i32 (i8*, ...)* @printf(i8* getelementptr([3 x i8]* @comma, i32 0, i32 0))",
  "  br label %loop.1",
  "post:",
  "  %ptr.post = getelementptr i32* %cast, i32 %i.1",
  "  %val.post = load i32* %ptr",
  "  call i32 (i8*, ...)* @printf(i8* getelementptr([3 x i8]* @fmt, i32 0, i32 0), i32 %val.post)",
  "  br label %empty",
  "empty:",
  "  call i32 (i8*, ...)* @printf(i8* getelementptr([2 x i8]* @close, i32 0, i32 0))",
  "  call void @nl()",
  "  ret void",
  "}"]

stringCreateDefault ∷ [String]
stringCreateDefault = []
  -- "define fastcc i8* @String_Create_Default(%String* %this, i64 %elts) nounwind {",
  -- "  ; Initialize 'buffer'.",
  -- "  %buff.ptr   = getelementptr %String* %this, i32 0, i32 0",
  -- "  %sizeof     = mul i64 %elts, 8",
  -- "  %buff.bytes = call i8* @malloc(i32 %sizeof)",
  -- "  %buff.i64   = bitcast i8* %buff.bytes to i64* ",
  -- "  store i64* %buff.i64, i64** %buff.ptr",
  -- "  ; Initialize 'length'.",
  -- "  %len.ptr = getelementptr %String* %this, i64 0, i64 1",
  -- "  store i64 %elts, i64* %len.ptr",
  -- "  ret i8* %buff.bytes",
  -- "}"]

buttCode ∷ [String]
buttCode = [
 "define void @butt(i32 %x) {",
  "  call i32 (i8*, ...)* @printf(i8* getelementptr([3 x i8]* @fmt, i32 0, i32 0), i32 %x)",
  "  ret void",
  "}"]

nlCode ∷ [String]
nlCode = [
   "define void @nl() {",
  "  call i32 @puts(i8* getelementptr([1 x i8]* @nil, i32 0, i32 0))",
  "  ret void",
  "}"]

showBit ∷ [String]
showBit = [
  "define void @showbit(i1 %bit) {",
  "  br i1 %bit, label %true, label %false",
  "true:",
  "  call i32 @puts(i8* getelementptr([5 x i8]* @tru, i32 0, i32 0))",
  "  ret void",
  "false:",
  "  call i32 @puts(i8* getelementptr([6 x i8]* @fls, i32 0, i32 0))",
  "  ret void",
  "}"] 

initPair ∷ [String]
initPair = [
  "define void @initpair(%pairi32i32* %pair, i32 %fst, i32 %snd) {",
  "  %pair.1 = getelementptr %pairi32i32* %pair, i32 0, i32 0",
  "  %pair.2 = getelementptr %pairi32i32* %pair, i32 1, i32 0",
  "  store i32 %fst, i32* %pair.1",
  "  store i32 %snd, i32* %pair.2",
  "  ret void",
  "}"]

showPair ∷ [String]
showPair = [
  "define void @showpair(%pairi32i32 %pair) {",
  "  %fst = extractvalue %pairi32i32 %pair, 0",
  "  %snd = extractvalue %pairi32i32 %pair, 1",
  "  call i32 (i8*, ...)* @printf(i8* getelementptr ([9 x i8]* @pair, i32 0, i32 0), i32 %fst, i32 %snd)",
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
  instr_ (printf "call void @butt(i32 %s)" n)
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
  sizeofString ← sizeof "%Arr"

      --  {- i64* buffer -} + 4 {- i32 len -} 
  let sizeofString = "8"

  sizeofBuf  ← instr (printf "mul i32 8, %s" size)

  string_mem ← malloc "1" -- sizeofString
  string     ← namedInstr "str" (printf "bitcast i8* %s to %%Arr*" string_mem)

  buffer_mem ← malloc sizeofBuf
  -- buffer     ← namedInstr "buf" (printf "bitcast i8* %s to i32*" buffer_mem)

  buffer_ptr ← namedInstr "buffer.ptr"$
    printf "getelementptr %%Arr* %s, i32 0, i32 0" string
  length_ptr ← namedInstr "string.ptr"$
    printf "getelementptr %%Arr* %s, i32 0, i32 1" string
  
  instr_ (printf "store i8* %s, i8** %s" buffer_mem buffer_ptr)
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

sizeof ∷ String → Codegen String
sizeof ty = do
  ptr ← namedInstr "ptr" (printf "getelementptr %s* null, i32 1" ty)
  namedInstr "size" (printf "ptrtoint %s* %s to i32" ty ptr)
       
add ∷ String → String → Codegen String
add reg₁ reg₂ = namedInstr "add" (printf "add i32 %s, %s" reg₁ reg₂)

mul ∷ String → String → Codegen String
mul reg₁ reg₂ = namedInstr "mul" (printf "mul i32 %s, %s" reg₁ reg₂)

and ∷ String → String → Codegen String
and reg₁ reg₂ = namedInstr "and" (printf "and i1 %s, %s" reg₁ reg₂)

xor ∷ String → String → String → Codegen String
xor ty reg₁ reg₂ = namedInstr "xor" (printf "xor %s %s, %s" ty reg₁ reg₂)

φ ∷ String → (String, String) → (String, String) → Codegen String
φ τ (a, b) (c, d) = namedInstr "phi" (printf "phi %s [%s, %%%s], [%s, %%%s]" τ a b c d)

jmp ∷ String → Codegen String
jmp label = terminate ("br label %" ++ label)

(≠) ∷ String → String → Codegen String
reg₁ ≠ reg₂ = namedInstr "neq" (printf "icmp ne i32 %s, %s" reg₁ reg₂)

(≡) ∷ String → String → Codegen String
reg₁ ≡ reg₂ = namedInstr "eq"  (printf "icmp eq i32 %s, %s" reg₁ reg₂)

(≤) ∷ String → String → Codegen String
reg₁ ≤ reg₂ = namedInstr "sle"  (printf "icmp sle i32 %s, %s" reg₁ reg₂)

(<.) ∷ String → String → Codegen String
reg₁ <. reg₂ = namedInstr "sle"  (printf "icmp slt i32 %s, %s" reg₁ reg₂)

br ∷ String → String → String → Codegen String
br a b c = terminate (printf "br i1 %s, label %%%s, label %%%s" a b c)

(≔) ∷ String → String → Codegen ()
loc ≔ gildi = instr_ (printf "store i32 %s, i32* %s" gildi loc)

π ∷ Int → String → Codegen String
π(n) pair = "fst" `namedInstr` printf "extractvalue %%pairi32i32 %s, %d" pair n

-- Get the underlying buffer
getBuffer ∷ String → String → Codegen String
getBuffer ty = 
  namedInstr "buffer.ptr" . printf "getelementptr %%Arr* %s, i32 0, i32 0"
  >=>
  namedInstr "buffer"     . printf "load i8** %s" 
  >=>
  namedInstr "cast"       . (printf "bitcast i8* %s to %s*" ?? ty)

getLength ∷ String → Codegen String
getLength = 
  namedInstr "len.ptr" . printf "getelementptr %%Arr* %s, i32 0, i32 1" 
  >=>
  namedInstr "length"  . printf "load i32* %s"

i32toi64 ∷ String → Codegen String
i32toi64 = namedInstr "asi32" . printf "zext i32 %s to i64"

definitions ∷ [String]
definitions = concat 
  [showBit, buttCode, nlCode, printArr, 
   initPair, showPair] 

constants ∷ [String]
constants = [
  "@.str       = internal constant [4 x i8] c\"%d\\0A\\00\"",
  "@fmt        = internal constant [3 x i8] c\"%d\00\"",
  "@comma      = internal constant [3 x i8] c\", \00\"",
  "@open       = internal constant [2 x i8] c\"[\00\"",
  "@close      = internal constant [2 x i8] c\"]\00\"",
  "@nil        = internal constant [1 x i8] c\"\\00\"",
  "@tru        = internal constant [5 x i8] c\"True\\00\"",
  "@fls        = internal constant [6 x i8] c\"False\\00\"",
  "@pair       = internal constant [9 x i8] c\"(%d, %d)\\00\"",
  "%pairi32i32 = type { i32, i32 }",
  "%Arr        = type { i8*, i32 }"
  -- "%BitVector  = type { i1*, i32 }"
  ]

declarations ∷ [String]
declarations = [
  "declare i32  @printf(i8* nocapture, ...) nounwind",
  "declare i64  @putint(i64)",
  "declare i64  @plusone(i64)",
  "declare i32  @puts(i8*)",
  "declare i8*  @memcpy(i8*, i8*, i32)",
  "declare i8*  @malloc(i32)",
  "declare void @free(i8*)"
  ]

dispatch ∷ String → String
dispatch "i1"  = 
  "  call void @showbit(i1 %1)"
dispatch "i32" = 
  "  tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 %1) nounwind"
dispatch "%pairi32i32" = 
  "  call void @showpair(%pairi32i32 %1)"
dispatch "%Arr*" = 
  "  "
dispatch str = error "foo"
