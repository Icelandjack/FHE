{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE UnicodeSyntax, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, TemplateHaskell #-}

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
import Types
import Operators

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

-- makeClassy       ''BasicBlock
-- makeClassyPrisms ''BasicBlock
-- makeClassy       ''CodegenState
-- makeClassyPrisms ''CodegenState
-- makeFields       ''CodegenState

type Codegen = Codegen' CodegenState

-- | The code generation monad.
newtype Codegen' st a = CG { runCG ∷ WriterT (Epilogue Id) (State st) a }
  deriving (Functor, Applicative, Monad,
            MonadWriter (Epilogue Id),
            MonadState  st,
            MonadFix)

-- TH doesn't generate shit for some reason
instructions :: Lens' BasicBlock [Instruction]
instructions = lens _instructions $ 
  \(BB _ b c) a -> BB a b c

terminator :: Lens' BasicBlock String
terminator = lens _terminator $ 
  \(BB a _ c) b -> BB a b c

index' :: Lens' BasicBlock Natural
index' = lens _index' $ 
  \(BB a b _) c -> BB a b c

currentBlock :: Lens' CodegenState Label
currentBlock = lens _codegenStateCurrentBlock $ \(CGS _ b c d) a -> 
  CGS a b c d

blocks :: Lens' CodegenState (M.Map Label BasicBlock)
blocks = lens _codegenStateBlocks $ \(CGS a _ c d) b -> 
  CGS a b c d

blockCount :: Lens' CodegenState Natural
blockCount = lens _codegenStateCount $ \(CGS a b _ d) c -> 
  CGS a b c d

count :: Lens' CodegenState Natural
count = lens _codegenStateCount $ \(CGS a b c _) d -> 
  CGS a b c d

-- type instance Zoomed (Codegen' st) = Zoomed (WriterT (Epilogue Name) (State st))

-- zoom currentBlock ∷ Codegen' Label c → Codegen c
-- instance Zoom (Codegen' state) (Codegen' state') state state' where
--     zoom ∷ LensLike' (Zoomed (Codegen' state) c) state' state
--          → Codegen' state c → Codegen' state' c
--     zoom l (CG m) = CG (zoom l m)

-- | TODO: Explain.
-- This is used to store actions that need to be run after the
-- generated code has run to completion, like freeing memory.
newtype Epilogue a = Epilogue [a]
  deriving (Show, Monoid, Functor, Foldable, Traversable)

-- ------------------------------------------------------------------------------
-- -- State Operations 
-- ------------------------------------------------------------------------------

-- See explanation in ‘runCodegenWith’.
uninitialisedState ∷ CodegenState
uninitialisedState = CGS (Label "NO-INITIAL!!!" 0) M.empty 0 0 

-- | Gets the value and final state
runCodegen ∷ Codegen' CodegenState a → (a, CodegenState)
runCodegen = runCodegenWith uninitialisedState

-- | Gets the value 
evalCodegen ∷ Codegen c → c
evalCodegen = fst . runCodegen

-- | Gets the value 
execCodegen ∷ Codegen c → CodegenState
execCodegen = snd . runCodegen

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
fresh :: MonadState CodegenState m => m Natural
fresh = 
  count <+= 1

-- | Get a unique string. After several iterations I'm falling back on
-- appending a fresh number as naively as possible.
uniqueVarId :: MonadState CodegenState f => String -> f Id
uniqueVarId name = 
  Id name <$> fresh

uniqueLabelName :: MonadState CodegenState f => String -> f Label
uniqueLabelName name =
  Label name <$> fresh

-- | Makes all generated variable names unique.
-- Carries around a map from names to their new names.
-- Our first tier of variables comes from converting higher-order
-- syntax to first-order syntax.

-- TODO: Check invariants of circular method.
makeFresh ∷ Exp a → Codegen (Exp a)
makeFresh = aux M.empty where 
  aux ∷ M.Map Id Id → Exp a → Codegen (Exp a)
  aux m = \case
    -- Interesting cases, 
    -- Var (VAR ty name) → 
    --   case M.lookup name m of
    --     Nothing →
    --       pure (Var (VAR ty name))
    --     Just newId → 
    --       pure (Var (VAR ty newId))
  
    -- Rote
    Constant ty c →
      pure (Constant ty c)

    -- BinOp (Bin (OpArr n) f) len val 
    -- Arr len n val → do
    --   new ← uniqueVarN "arr"
    --   let m' = M.insert n new m
  
    --   Arr 
    --     <$> aux m' len
    --     <*> pure new
    --     <*> aux m' val

    -- While n cond body init → do
    --   new ← uniqueVarId "while"
    --   let m' = M.insert n new m
  
    --   While new
    --     <$> aux m' cond
    --     <*> aux m' body
    --     <*> aux m' init

    -- Lam n body → do
    --   new ← uniqueVarId "lam"
    --   let m' = M.insert n new m
  
    --   Lam
    --     <$> pure new
    --     <*> aux m' body

    -- This should appear before cases like "Arr" and "While" 
    --  (I refactored, no longer true?)
    UnOp unaryOp a → 
      UnOp unaryOp
        <$> aux m a

    BinOp binaryOp a b → 
      BinOp binaryOp
          <$> aux m a 
          <*> aux m b

    TerOp ternaryOp a b c →
      TerOp ternaryOp
        <$> aux m a
        <*> aux m b
        <*> aux m c
  
    _ → error "makeFresh: add case"
  
-- | Invariant: 'new ∷ Id' is a fresh variable and does not appear in
-- 'Exp a'.
-- 
-- Substitutes a variable by a new variable.
-- data Operand a = Reference a | ConstTru | ConstFls | ConstNum Int
rename ∷ Id → Id → Exp a → Exp a
rename old new originalExp = case originalExp of
  -- Interesting cases, 
  Var (name ::: ty)
    | name == old 
    → Var (new ::: ty)

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

  -- Lam name body 
  --   | name == old
  --   → originalExp

  --   | otherwise
  --   → Lam name
  --       (rename old new body)

  -- Rote
  Constant ty c →
    Constant ty c

  If a b c → 
    If 
      (rename old new a)
      (rename old new b)
      (rename old new c)

  UnOp unaryOp a → 
    UnOp unaryOp
      (rename old new a)

  BinOp binaryOp a b → 
    BinOp binaryOp
      (rename old new a)
      (rename old new b)

  Len arr →
    Len (rename old new arr)

  ArrIx arr ix → 
    ArrIx 
      (rename old new arr)
      (rename old new ix)

  _ → error "rename: add case"

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
namedInstr ∷ String → Format (Codegen Id) a → a
namedInstr name = runFormat ?? \txtBuilder → do
  ref ← uniqueVarId name
  instr_ (sh%" = "%builder) ref txtBuilder
  pure ref

-- | Adds an instruction to the current basic block and returns the
-- reference as an operand for easier use with `compile'.
namedOp ∷ String → Format (Codegen Op) a → a
namedOp name = runFormat ?? \txtBuilder → do
  ref ← uniqueVarId name
  instr_ (sh%" = "%builder) ref txtBuilder
  pure (Reference ref)

-- | Appends a raw instruction (as a String…) to the instruction list of
-- the current block, returns its newly generated identifier which is
-- based off "u".
instr ∷ Format (Codegen Id) a → a
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
  OpNot → 
    createBinop "xor" "i1 " ConstTru
  OpNeg num → do

    let numberToOp ∷ NumberType a → Integer → Op
        numberToOp (NumberType INT8)  = ConstNum8  . fromInteger 
        numberToOp (NumberType INT32) = ConstNum32 . fromInteger 

    createBinop "sub" "i32" (numberToOp num 0) 

  OpFst → 
    π(0) 

  OpSnd →
    π(1)

  OpLen →
    getLength

π ∷ Int → Op → Codegen Op
π(n) pair = namedOp "fst" ("extractvalue %pairi32i32 "%op%", "%int) pair n

getLength ∷ Op → Codegen Op
getLength nm = do
  len ← namedInstr "len.ptr" ("getelementptr %Arr* "%op%", i32 0, i32 1") nm
  namedOp "length" ("load i32* "%shown) len

-- compile (Len (Arr len _ _)) = do
--   compile len

-- compile (Len arr) = do
--   compile arr >>= getLength -- >>= i32toi64


-- | Compiles a binary operation.
compileBinop ∷ BinOp a b c → Op → Op → Codegen Op
compileBinop = \case
  OpAdd num → 
    createBinop "add" (showNumType num)
  OpSub num → 
    createBinop "sub" (showNumType num)
  OpMul num → 
    createBinop "mul" (showNumType num)

  OpEqual scalar → 
    createBinop "icmp eq" (showScalarType scalar)
  OpNotEqual scalar → 
    createBinop "icmp ne" (showScalarType scalar)
  OpLessThan scalar → 
    createBinop "icmp slt" (showScalarType scalar)
  OpLessThanEq scalar → 
    createBinop "icmp sle" (showScalarType scalar)
  OpGreaterThan scalar → 
    createBinop "icmp sgt" (showScalarType scalar)
  OpGreaterThanEq scalar → 
    createBinop "icmp sge" (showScalarType scalar)

  -- a ∧ b = a * b
  OpAnd → 
    createBinop "mul" "i1"  

  -- a ∨ b = a + b + ab
  OpOr → \a b → do
    a_plus_b ← createBinop "add" "i1" a b
    a_mult_b ← createBinop "mul" "i1" a b
    createBinop "add" "i1" a_plus_b a_mult_b

  OpXor → 
    createBinop "xor" "i8" 

  OpPair → let
    insNum ∷ Op → Op → Int → Codegen Op
    insNum = 
      namedOp "updated" 
       ("insertvalue %pairi32i32 "%op%", i32 "%op%", "%d) 

    mkPair ∷ Op → Op → Codegen Op
    mkPair x y = do
     let initVal = Struct [Undef "i32", Undef "i32"]
     retVal₁ ← insNum initVal x 0
     retVal₂ ← insNum retVal₁ y 1
     return retVal₂

    in mkPair

  foo -> error (show foo ++ " ndefined shit")

compileTerop ∷ TernOp a b c d → Op → Op → Op → Codegen Op
compileTerop = \case
  OpIf → 
    error "if..."

  OpWhile name →
    error "while..."

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

