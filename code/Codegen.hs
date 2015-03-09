{-# LANGUAGE UnicodeSyntax #-}

module Codegen where

import qualified Data.Map as M
import Control.Monad.State
import Data.Functor

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

emptyBlock ∷ Int → BasicBlock 
emptyBlock index = MkBB [] (error "NEEDS A TERMINATOR") index

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
    blocks     = M.insert blockName (emptyBlock blockCnt) bls,
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
instr ∷ Instruction → Codegen String
instr newInstructions = do
  ref ← fresh
  blk ← current

  let instrs   = instructions blk
      localVar = "%u" ++ show ref

  modifyBlock (blk { 
    instructions = instrs ++ [localVar ++ " = " ++ newInstructions] 
  })
  
  return localVar

terminate ∷ String → Codegen String
terminate newTerm = do
  block ← current
  modifyBlock (block { terminator = newTerm })
  return newTerm

