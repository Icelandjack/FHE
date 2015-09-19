-- {-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnicodeSyntax #-}

module Codegen where

import Prelude
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader {- rm ltr -}
import Data.Functor
import Data.Functor.Identity
import Text.Printf
import Data.Foldable
import Data.Traversable
import Control.Lens
import Numeric.Natural

import Data.Char

import Util
import Variable

type Instruction = String

data BasicBlock = MkBB {
  _instructions ∷ [Instruction],
  _terminator   ∷ String,
  _index'       ∷ Natural
} deriving Show

data CodegenState = MkCodegen {
  _codegenStateCurrentBlock ∷ Label,
  _codegenStateBlocks       ∷ M.Map Label BasicBlock,
  _codegenStateBlockCount   ∷ Natural, 
  _codegenStateCount        ∷ Natural
} deriving Show
-- _codegenStateNameUsage    ∷ M.Map String Natural,

makeClassy       ''BasicBlock
makeClassyPrisms ''BasicBlock
makeClassy       ''CodegenState
makeClassyPrisms ''CodegenState
makeFields       ''CodegenState

type Codegen = WriterT (Epilogue Name) (State CodegenState)

newtype Epilogue a = Epilogue [a]
  deriving (Show, Monoid, Functor, Foldable, Traversable)

-- VARIABLES

fresh ∷ Codegen Natural
fresh = 
  count <+= 1

-- | Get a unique string. After several iterations I'm falling back on
-- appending a fresh number as naively as possible.
uniqueVarName ∷ String → Codegen Name
uniqueVarName name  = do
  Variable name <$> fresh

uniqueLabelName ∷ String → Codegen Label
uniqueLabelName name  = do
  Label name <$> fresh

-- global = @
-- local  = %
-- namedInstr ∷ String → Instruction → Codegen String
namedInstr ∷ String → Instruction → Codegen Name
namedInstr name newInstruction = do
  var ← uniqueVarName name

  let instr ∷ String
      instr = printf "%s = %s" (show var) newInstruction

  currentLens.instructions <>= [instr]
  
  return var

namedOp ∷ String → Instruction → Codegen Op
namedOp name newInstruction = 
  Reference <$> namedInstr name newInstruction

addBlock ∷ String → Codegen Label
addBlock str = do
  blockCnt   ← use blockCount
  labelName  ← uniqueLabelName str

  let newBlock ∷ BasicBlock
      newBlock = emptyBlock blockCnt labelName

  blocks.at labelName ?= newBlock
  blockCount          += 1

  return labelName

emptyBlock ∷ Natural → Label → BasicBlock 
emptyBlock index label = 
  MkBB [] (error (show label ++ ": NEEDS A TERMINATOR")) index

emptyState ∷ CodegenState
-- emptyState = MkCodegen (error "no-initial") M.empty 0 {- M.empty -} 0
emptyState = 
  MkCodegen 
  (Label "no-initial" 0)
  M.empty 0 {- M.empty -} 0
  -- "entry" (M.singleton "entry" (emptyBlock 0 "entry")) 1 M.empty (S.singleton "entry") 0 

-- TODO: vars ∶ [(String, Operand)] to { symtab = vars }
runCodegen ∷ ∀a. Codegen a → (a, CodegenState)
runCodegen codegen = runState noEpilogue emptyState

  where
    -- We've already used the epilogue so we are only interested in
    -- the return value
    noEpilogue ∷ State CodegenState a
    noEpilogue = evalWriterT codegen

entry ∷ Codegen Label
entry = use currentBlock

setBlock ∷ Label → Codegen ()
setBlock newBlock = do
  currentBlock .= newBlock

getBlock ∷ Codegen Label
getBlock = use currentBlock

modifyBlock ∷ BasicBlock → Codegen ()
modifyBlock new = do
  active ← use currentBlock
  blocks.at active ?= new

-- current ∷ Codegen BasicBlock
-- current = do
--   c    ← use currentBlock
--   blks ← use blocks
--   case M.lookup c blks of
--     Just x  → return x
--     Nothing → error $ "No such block: " ++ show c

currentLens ∷ Lens' CodegenState BasicBlock
currentLens = singular current'

current' ∷ Traversal' CodegenState BasicBlock
current'
  f
  (MkCodegen current blocks blockCount cnt) 
  = 
  MkCodegen 
  <$>
  pure current
  <*>
  traverseOf (ix current) f blocks
  <*>
  pure blockCount
  <*>
  pure cnt

-- -- THIS SHOULD BE REMOVED
-- addInstr ∷ Natural → String → Codegen String
-- addInstr (printf "%%var%d" → var) instr = do
--   currentLens.instructions <>= [printf "%s = %s" var instr]
--   return var

-- addInstr ∷ Natural → String → Codegen String
-- addInstr (printf "%%var%d" → var) instr = do
--   blk ← current

--   modifyBlock (blk { 
--     _instructions = _instructions blk ++ [printf "%s = %s" var instr]
--   })

--   return var

instr ∷ Instruction → Codegen Name
instr = namedInstr "u"

instr_ ∷ Instruction → Codegen ()
instr_ newInstruction = 
  currentLens.instructions <>= [newInstruction]

terminate ∷ String → Codegen ()
terminate newTerm = do
  currentLens.terminator .= newTerm
-- terminate ∷ String → Codegen String
-- terminate newTerm = do
--   currentLens.terminator <.= newTerm

