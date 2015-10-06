{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedStrings #-}
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

import Control.Lens hiding (op)
import Control.Lens.Internal.Zoom

import Numeric.Natural
import Data.List

import Formatting
import Formatting.Internal
import Formatting.ShortFormatters

import Data.Text.Internal.Builder

import qualified Data.Text              as T
import qualified Data.Text.Lazy         as TL
import qualified Data.Text.Lazy.Builder as TLB

import Util
import Variable
import Exp

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

data BasicBlock = BB {
  _instructions ∷ [Instruction],
  _terminator   ∷ String,
  _index'       ∷ Natural
} deriving (Eq, Show)

data CodegenState = CGS {
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

type Codegen = Codegen' CodegenState

-- | The code generation monad.
newtype Codegen' st a = CG { runCG ∷ WriterT (Epilogue Name) (State st) a }
  deriving (Functor, Applicative, Monad,
            MonadWriter (Epilogue Name),
            MonadState  st,
            MonadFix)

type instance Zoomed (Codegen' st) = Zoomed (WriterT (Epilogue Name) (State st))

-- zoom currentBlock ∷ Codegen' Label c → Codegen c
instance Zoom (Codegen' state) (Codegen' state') state state' where
    zoom ∷ LensLike' (Zoomed (Codegen' state) c) state' state
         → Codegen' state c → Codegen' state' c
    zoom l (CG m) = CG (zoom l m)

-- | TODO: Explain.
-- This is used to store actions that need to be run after the
-- generated code has run to completion, like freeing memory.
newtype Epilogue a = Epilogue [a]
  deriving (Show, Monoid, Functor, Foldable, Traversable)

------------------------------------------------------------------------------
-- State Operations 
------------------------------------------------------------------------------

-- See explanation in ‘runCodegenWith’.
uninitialisedState ∷ CodegenState
uninitialisedState = CGS (Label "NO-INITIAL!!!" 0) M.empty 0 0 

-- | Gets the value and final state
runCodegen ∷ Codegen' CodegenState a → (a, CodegenState)
runCodegen = runCodegenWith uninitialisedState

-- | Gets the value 
evalCodegen ∷ Codegen c → c
evalCodegen = fst . runCodegen


runCodegenWith ∷ ∀a. CodegenState → Codegen a → (a, CodegenState)
runCodegenWith initState codegen = runState noEpilogue initState

  where
    -- We've already used the epilogue so we are only interested in
    -- the return value
    noEpilogue ∷ State CodegenState a
    noEpilogue = evalWriterT $ runCG $ do

      -- This is a bit odd, to initialize a state CodegenState needs
      -- an initial Label but to create a label purely I would have to
      -- duplicate all the logic in `newBlock` and `setBlock`: since
      -- this cannot be done purely the initial state is uninitialised
      -- and then initialised within the Codegen Monad.

      -- Creates the initial entry block.
      setNewBlock "entry"
      codegen

------------------------------------------------------------------------------
-- Block Operations 
------------------------------------------------------------------------------

-- | Creates an empty block, bumping the `blockCount'.
emptyBlock ∷ Label → Codegen BasicBlock
emptyBlock label = do
  index ← blockCount <+= 1
  pure (BB [] terminator index) where

    terminator = "BOGUS TERMINATOR" -- error (show label ++ ": NEEDS A TERMINATOR!")

-- | Creates a new block given a string as a preferred name.
newBlock ∷ String → Codegen Label
newBlock name = do
  blockName ← uniqueLabelName name
  newBlock  ← emptyBlock blockName

  -- Add `newBlock' to the map of blocks and return the block name
  blocks.at blockName ?= newBlock
  pure blockName

setBlock ∷ Label → Codegen ()
setBlock blockName = do
  currentBlock .= blockName

-- | The not-as-common-as-originally-though idiom of creating and
-- setting a block.
setNewBlock ∷ String → Codegen Label
setNewBlock name = do
  label ← newBlock name
  setBlock label
  pure label

getBlock ∷ Codegen Label
getBlock = do
  use currentBlock

-- | Sets the current block to `new'. Currently unused?
-- modifyBlock ∷ BasicBlock → Codegen ()
-- modifyBlock new = do
--   currBlock .= new

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

-- | Makes all generated variable names unique.
-- Carries around a map from names to their new names.
-- Our first tier of variables comes from converting higher-order
-- syntax to first-order syntax.

-- TODO: Check invariants of circular method.
makeFresh ∷ Exp a → Codegen (Exp a)
makeFresh = aux M.empty where 
  aux ∷ M.Map Name Name → Exp a → Codegen (Exp a)
  aux m = \case
    -- Interesting cases, 
    Var name → 
      case M.lookup name m of
        Nothing →
          pure (Var name)
        Just newName → 
          pure (Var newName)
  
    While n cond body init → do
      new ← uniqueVarName "while"
      let m' = M.insert n new m
  
      While new
        <$> aux m' cond
        <*> aux m' body
        <*> aux m' init
    
    Arr len n val → do
      new ← uniqueVarName "arr"
      let m' = M.insert n new m
  
      Arr 
        <$> aux m' len
        <*> pure new
        <*> aux m' val
  
    Lam n body → do
      new ← uniqueVarName "lam"
      let m' = M.insert n new m
  
      Lam
        <$> pure new
        <*> aux m' body
  
    -- Rote
    LitI i → 
      pure (LitI i)
  
    LitB b → 
      pure (LitB b)
  
    If a b c → 
      If 
        <$> aux m a 
        <*> aux m b 
        <*> aux m c
  
    UnOp op f rep a → 
      UnOp op f rep 
        <$> aux m a
  
    BinOp op f rep a b → 
      BinOp op f rep
        <$> aux m a 
        <*> aux m b
  
    Len arr →
      Len <$> aux m arr
  
    ArrIx arr ix → 
      ArrIx 
        <$> aux m arr
        <*> aux m ix
  
    Fst pair → 
      Fst <$> aux m pair
  
    Snd pair → 
      Snd <$> aux m pair
  
    _ → error "add case"
  
-- | Invariant: 'new ∷ Name' is a fresh variable and does not appear in
-- 'Exp a'.
-- 
-- Substitutes a variable by a new variable.
-- data Operand a = Reference a | ConstTru | ConstFls | ConstNum Int
rename ∷ Name → Name → Exp a → Exp a
rename old new originalExp = case originalExp of
  -- Interesting cases, 
  Var name 
    | name == old 
    → Var new

    | otherwise
    → originalExp

  While name cond body init 
    | name == old
    → originalExp

    | otherwise
    → While name 
        (rename old new cond)
        (rename old new body)
        (rename old new init)
  
  Arr len name val 
    | name == old
    → originalExp
    
    | otherwise 
    → Arr 
        (rename old new len)
        name
        (rename old new val)

  Lam name body 
    | name == old
    → originalExp

    | otherwise
    → Lam name
        (rename old new body)

  -- Rote
  LitI i → 
    LitI i

  LitB b → 
    LitB b

  If a b c → 
    If 
      (rename old new a)
      (rename old new b)
      (rename old new c)

  UnOp op f rep a → 
    UnOp op f rep 
      (rename old new a)

  BinOp op f rep a b → 
    BinOp op f rep
      (rename old new a)
      (rename old new b)

  Len arr →
    Len (rename old new arr)

  ArrIx arr ix → 
    ArrIx 
      (rename old new arr)
      (rename old new ix)

  Fst pair → 
    Fst (rename old new pair)

  Snd pair → 
    Snd (rename old new pair)

  _ → error "add case"

------------------------------------------------------------------------------
-- OPERATIONS
------------------------------------------------------------------------------

-- | Appends a raw instruction (as a String…) to the instruction list of
-- the current block.
instr_ ∷ Format (Codegen ()) a → a
instr_ = runFormat ?? \txtBuilder → do
  let instr = TL.unpack (TLB.toLazyText txtBuilder)
  currBlock.instructions <>= [instr]

-- | Adds an instruction to the current basic block and returns the
-- variable name of the register returned.
namedInstr ∷ String → Format (Codegen Name) a → a
namedInstr name = runFormat ?? \txtBuilder → do
  ref ← uniqueVarName name
  instr_ (sh%" = "%builder) ref txtBuilder
  pure ref

-- | Adds an instruction to the current basic block and returns the
-- reference as an operand for easier use with `compile'.
namedOp ∷ String → Format (Codegen Op) a → a
namedOp name = runFormat ?? \txtBuilder → do
  ref ← uniqueVarName name
  instr_ (sh%" = "%builder) ref txtBuilder
  pure (Reference ref)

-- | Appends a raw instruction (as a String…) to the instruction list of
-- the current block, returns its newly generated identifier which is
-- based off "u".
instr ∷ Format (Codegen Name) a → a
instr = namedInstr "u" 

operand ∷ Format (Codegen Op) a → a
operand = namedOp "u" 

-- | Appends a terminator instruction to the current basic block's
-- instruction list.
-- Will overwrite existing terminator.
terminate ∷ Format (Codegen ()) a → a
terminate = runFormat ?? \txtBuilder → do
  let newTerminator = TL.unpack (TLB.toLazyText txtBuilder)

  currBlock.terminator .= newTerminator

-- | Emit a binary operation.
createBinop ∷ String → String → Op → Op → Codegen Op
createBinop op =  
  namedOp (last (words op))
    (s% " " %s% " " %sh% ", " %sh) op 

-- | Compiles a unary operation.
compileUnop ∷ UnOp a b → Op → Codegen Op
compileUnop = \case
  OpNeg → 
    createBinop "sub" "i32" (ConstNum 0) 
  OpNot → 
    createBinop "xor" "i1 " ConstTru

-- | Compiles a binary operation.
compileBinop ∷ BinOp a b c → Op → Op → Codegen Op
compileBinop = \case
  OpAdd → 
    createBinop "add" "i32"
  OpSub → 
    createBinop "sub" "i32" 
  OpMul → 
    createBinop "mul" "i32" 

  OpEqual → 
    createBinop "icmp eq"  "i32" 
  OpNotEqual → 
    createBinop "icmp ne"  "i32" 
  OpLessThan → 
    createBinop "icmp slt" "i32" 
  OpLessThanEq → 
    createBinop "icmp sle" "i32" 
  OpGreaterThan → 
    createBinop "icmp sgt" "i32" 
  OpGreaterThanEq → 
    createBinop "icmp sge" "i32" 

  -- a ∧ b = a * b
  OpAnd → 
    createBinop "mul" "i1"  

  -- a ∨ b = a + b + ab
  OpOr → \a b → do
    a_plus_b ← createBinop "add" "i1" a b
    a_mult_b ← createBinop "mul" "i1" a b
    createBinop "add" "i1" a_plus_b a_mult_b

  OpXor → 
    createBinop "xor" "i32" 

------------------------------------------------------------------------------
-- CODE GENERATION
------------------------------------------------------------------------------

emit ∷ MonadWriter [String] m ⇒ Format (m ()) b → b
emit = emitWhen True

emitWhen ∷ MonadWriter [String] m ⇒ Bool → Format (m ()) b → b
emitWhen cond = runFormat ?? \txtBuilder → do
  let code = TL.unpack (TLB.toLazyText txtBuilder)
  when cond
    (tell [code])

indented ∷ MonadWriter [String] m ⇒ Format (m ()) b → b
indented = indentedWhen True

indentedWhen ∷ MonadWriter [String] m ⇒ Bool → Format (m ()) b → b
indentedWhen cond = runFormat ?? \txtBuilder → do
  let code = TL.unpack (TLB.toLazyText txtBuilder)
  when cond
    (tell ["  " ++ code])

comma ∷ Format r ([String] → r)
comma = later (TLB.fromText . T.pack . intercalate ", ")

lbl ∷ Format r (Label → r)
lbl = later (\lbl → TLB.fromText (T.pack ("%" ++ show lbl)))

op ∷ Format r (Op → r)
op = later (TLB.fromText . T.pack . show)

{-
--Debug
fakeCodegen = MkCodegen other (M.fromList [(entry, fakeBasicBlock), (foo,  fakeBasicBlock')]) 1 5 where   
  entry = Label "entry" 0
  foo   = Label "foo" 1
  other = Label "weird" 666
fakeBasicBlock = MkBB ["a = 5", "b = a + a", "c = a + b"] "ret a + b + c" 5
fakeBasicBlock' = MkBB ["litla", "rassgat"] "ret 420" 10
-}
