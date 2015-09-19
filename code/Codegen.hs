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

------------------------------------------------------------------------------
-- Basic Blocks & Codegeneration State
------------------------------------------------------------------------------

-- | Basic Blocks are a list of instructions and a terminator.
--   INSTRUCTIONS:
--     [%a = add i32 15, 15,
--      %b = add i32 %a, %a]
--   TERMINATOR:
--     ret i32 %b
-- The `index'' keeps track of the order 

data BasicBlock = MkBB {
  _instructions ∷ [Instruction],
  _terminator   ∷ String,
  _index'       ∷ Natural
} deriving (Eq, Show)

data CodegenState = MkCodegen {
  _codegenStateCurrentBlock ∷ Label,
  _codegenStateBlocks       ∷ M.Map Label BasicBlock,
  _codegenStateBlockCount   ∷ Natural, 
  _codegenStateCount        ∷ Natural
} deriving (Eq, Show)

makeClassy       ''BasicBlock
makeClassyPrisms ''BasicBlock
makeClassy       ''CodegenState
makeClassyPrisms ''CodegenState
makeFields       ''CodegenState

-- | The code generation monad.
type Codegen = WriterT (Epilogue Name) (State CodegenState)

-- | TODO: Explain.
-- This is used to store actions that need to be run after the
-- generated code has run to completion, like freeing memory.
newtype Epilogue a = Epilogue [a]
  deriving (Show, Monoid, Functor, Foldable, Traversable)

-- | Gets the value 
runCodegen ∷ Codegen a → (a, CodegenState)
runCodegen = runCodegenWith emptyState

runCodegenWith ∷ ∀a. CodegenState → Codegen a → (a, CodegenState)
runCodegenWith initState codegen = runState noEpilogue initState

  where
    -- We've already used the epilogue so we are only interested in
    -- the return value
    noEpilogue ∷ State CodegenState a
    noEpilogue = evalWriterT codegen

------------------------------------------------------------------------------
-- Block Operations 
------------------------------------------------------------------------------

-- | Creates an empty block, bumping the `blockCount'.
emptyBlock ∷ Label → Codegen BasicBlock
emptyBlock label = do
  index ← blockCount <+= 1
  pure (MkBB [] terminator index) where

  terminator ∷ String
  terminator = error (printf "%s: NEEDS A TERMINATOR!" (show label))

-- | Creates a new block given a string as a preferred name.
newBlock ∷ String → Codegen Label
newBlock name = do
  blockName ← uniqueLabelName name
  newBlock  ← emptyBlock blockName

  -- Add `newBlock' to the map of blocks and return the block name
  blocks.at blockName ?= newBlock
  pure blockName

setBlock ∷ Label → Codegen ()
setBlock newBlock = do
  currentBlock .= newBlock

getBlock ∷ Codegen Label
getBlock = do
  use currentBlock

-- | Sets the current block to `new'.
modifyBlock ∷ BasicBlock → Codegen ()
modifyBlock new = do
  currBlock .= new

-- | A lens that peers into CodegenState's map of blocks and focuses
-- on the value pointed at by the current block as key.
-- 
-- An invariant of the `CodegenState' is that the `currentBlock'
-- should always be present as a key of the map. If this is not the
-- case this lens will fail.
-- 
-- This lens is a life saver.
currBlock ∷ Lens' CodegenState BasicBlock
currBlock = lens get set where

  get ∷ CodegenState → BasicBlock
  get codegenState = 
    codegenState ^?! blocks.ix (codegenState^.currentBlock)

  set ∷ CodegenState → BasicBlock → CodegenState
  set codegenState bb 
    | Just a ← codegenState ^? blocks.ix (codegenState^.currentBlock)
    = codegenState 
        & blocks.ix (codegenState^.currentBlock) .~ bb
    | otherwise = error "CURRENT BLOCK NOT IN MAP"

------------------------------------------------------------------------------
-- State Operations 
------------------------------------------------------------------------------

-- TODO: Use non-bogus initial label.
emptyState ∷ CodegenState
emptyState = MkCodegen (Label "no-initial" 0) M.empty 0 0

------------------------------------------------------------------------------
-- Variables
------------------------------------------------------------------------------

-- | Bumps the counter by one and return the new value.
fresh ∷ Codegen Natural
fresh = 
  count <+= 1

-- | Get a unique string. After several iterations I'm falling back on
-- appending a fresh number as naively as possible.
uniqueVarName ∷ String → Codegen Name
uniqueVarName name = do
  Variable name <$> fresh

uniqueLabelName ∷ String → Codegen Label
uniqueLabelName name  = do
  Label name <$> fresh

------------------------------------------------------------------------------
-- OPERATIONS
------------------------------------------------------------------------------

-- | Appends a raw instruction (as a String…) to the instruction list of
-- the current block, returns its newly generated identifier which is
-- based off "u".
instr ∷ Instruction → Codegen Name
instr = namedInstr "u"

-- | Appends a raw instruction (as a String…) to the instruction list of
-- the current block.
instr_ ∷ Instruction → Codegen ()
instr_ newInstruction = 
  currBlock.instructions <>= [newInstruction]

-- | Appends an instruction to the instruction list of the current
-- block, generating a unique identifier.
namedInstr ∷ String → Instruction → Codegen Name
namedInstr name newInstruction = do
  ref ← uniqueVarName name

  instr_ (printf "%s = %s" (show ref) newInstruction)

  return ref

-- | Adds an instruction to the current basic block and returns the
-- reference as an operand for easier use with `compile'.
namedOp ∷ String → Instruction → Codegen Op
namedOp name newInstruction = 
  Reference <$> namedInstr name newInstruction

-- | Appends a terminator instruction to the current basic block's
-- instruction list.
-- Will overwrite existing terminator.
terminate ∷ String → Codegen ()
terminate newTerm = do
  currBlock.terminator .= newTerm

{-
--Debug
fakeCodegen = MkCodegen other (M.fromList [(entry, fakeBasicBlock), (foo,  fakeBasicBlock')]) 1 5 where   
  entry = Label "entry" 0
  foo   = Label "foo" 1
  other = Label "weird" 666
fakeBasicBlock = MkBB ["a = 5", "b = a + a", "c = a + b"] "ret a + b + c" 5
fakeBasicBlock' = MkBB ["litla", "rassgat"] "ret 420" 10
-}

-- -- THIS SHOULD BE REMOVED
-- addInstr ∷ Natural → String → Codegen String
-- addInstr (printf "%%var%d" → var) instr = do
--   currBlock.instructions <>= [printf "%s = %s" var instr]
--   return var

-- addInstr ∷ Natural → String → Codegen String
-- addInstr (printf "%%var%d" → var) instr = do
--   blk ← current

--   modifyBlock (blk { 
--     _instructions = _instructions blk ++ [printf "%s = %s" var instr]
--   })

--   return var

