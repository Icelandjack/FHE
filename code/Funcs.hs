{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RebindableSyntax, PatternSynonyms, UnicodeSyntax, LambdaCase, ViewPatterns, ScopedTypeVariables, RecordWildCards, OverloadedStrings #-}

-- http://chrisdone.com/posts/making-ghci-fast 
-- ghci> :set -fobject-code 

-- Feldspar compiler's input is a core language program represented as
-- a graph.  This graph is first transformed to an ABSTRACT
-- IMPERAITIVE PROGRAM that is no longer purely functional. 

-- http://ellcc.org/demo/index.cgi

-- Metaphors don't inspire definitions but insight and intuition.

-- IC -IC-optimisation→  IC 
--    -Code-Generation→  Symbolic instructions
--    -Target-code-opt→  Symbolic instructions
--    -Machine-code-gen→ Bit patterns

-- Shrinking reductions = restriction of β-reduction (inlining) to
-- cases where bound variable is used 0 (dead-code elimination) or one
-- (linear inlining) times.

module Funcs where

import Data.Kind (type (*))
import Data.String
import Data.Char
import System.Process
import System.IO
import Control.Applicative hiding (some)
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
import Data.Int
import Test.QuickCheck.Monadic hiding (run)
import qualified Test.QuickCheck.Monadic as M
-- import Data.Data
-- import Data.Typeable
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
import Operators

-- _Constant ∶ Prism' (Exp a) Int
-- _Constant ∶ Prism' (Exp a) Int8 …?

-- _Constant ∶ Prism' (Exp a) (Dict (a ~ Int),  a)
-- _Constant ∶ Prism' (Exp a) (Dict (a ~ Int8), a) …?

-- `compile' has to deal with more than just registers so the return
-- works with operands `Op' that are either references (`Name') or
-- constants (`ConstTru', `ConstFls', `ConstNum Int').
compile ∷ ∀a. Exp a → Codegen Op

compile (ArrIx arr index) = do
  array_val ← compile arr
  index_val ← {- i32toi64 =<< -} compile index

  buffer   ← getBuffer("i8") array_val

  elt_ptr ← namedInstr "ptr" 
    ("getelementptr i8* "%sh%", i32 "%op) buffer index_val
  -- namedOp "length" ("load i32* "%sh) elt_ptr
  namedOp "val" ("load i8* "%sh) elt_ptr

compile (Arr len var ixf) = mdo
  entry   ← getBlock
  loop_1  ← newBlock "arr.loop1"
  loop_2  ← newBlock "arr.loop2"
  post    ← newBlock "arr.post"

  arrLength ← compile len
  arrMem    ← mallocStr arrLength
  buffer    ← getBuffer("i8") (Reference arrMem)

  jmp loop_1

  -- | arr.loop
  -- Increment from [0…len) 
  setBlock loop_1
  i₀  ← φ "i32" (ConstNum8 0,  entry)
                (Reference i₁, loop_2')
  i₁  ← incr i₀

  keepGoing ← namedOp "slt"
    ("icmp slt i32 " %sh% ", " %sh) i₀ arrLength

  br keepGoing loop_2 post

  setBlock loop_2 

  ptr ← namedInstr "ptr" 
    ("getelementptr i8* " %sh% ", i32 " %sh) buffer i₀

  value    ← compile (rename var i₀ ixf)
  loop_2'  ← getBlock

  ptr ≔ value
  jmp loop_1

  -- | arr.post
  setBlock post

  pure (Reference arrMem)

compile (MkInt8  val) = 
  pure (ConstNum8 val)

compile (MkInt32 val) = 
  pure (ConstNum32 val)

compile Tru = 
  pure ConstTru

compile Fls = 
  pure ConstFls

compile (MkChar ch) = 
  error "no operand for CHAR"

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
      pure (foo, label)

  true  ← block (tru, if_then)
  false ← block (fls, if_else)
  
  setBlock if_cont

  φ (toLLVMType (getTy @a)) true false
    <&> Reference

-- compile (While var condTest body init) = mdo
--   -- Create blocks
--   entry       ← getBlock
--   while_cond  ← newBlock "while.cond"
--   while_body  ← newBlock "while.body"
--   while_post  ← newBlock "while.post"

--   -- Compile the initial value of the while expression
--   init_val ← compile init
--   jmp while_cond

--   -- TEST
--   setBlock while_cond
--   val_1 ← φ (showExpType init) (init_val, entry)
--                                (val_2,    while_body)

--   -- When compiling
--   --   While "%lam_1" (5 < "%lam_1") ("%lam_1" + 1) 0
--   -- "%lam_1" is the variable bound by the binding construct While and
--   -- must refer to the LLVM register "val_1"
--   --   val_1 ← φ …
--   -- which is a fresh variable. So we replace all occurances of
--   -- "%lam_1" in the conditional and body before compiling it.
--   keepGoing ← compile (rename var val_1 condTest)
--   br keepGoing while_body while_post

--   -- BODY
--   setBlock while_body

--   -- Same as with the conditional expression.
--   val_2     ← compile (rename var val_1 body)
--   jmp while_cond

--   -- POST
--   setBlock while_post
--   pure (Reference val_1)
    
compile (MkVar (id ::: _)) = 
  pure (Reference id)

-- TODO: Constant fold this before passing to compile.
compile (Len (Arr len _ _)) = do
  compile len

compile (UnOp (Un operator _) a) = do
  reg ← compile a
  compileUnop operator reg

compile (BinOp (Bin operator _) a b) = do
  reg₁ ← compile a
  reg₂ ← compile b

  compileBinop operator reg₁ reg₂

-- http://www.stephendiehl.com/llvm/#if-expressions

compile _ = error "compile: ..."
-- -- compile (Lam n body) = 
-- --   error "compile (Lam n body)

compileExpression :: forall ty. Exp ty -> CodegenState
compileExpression exp = execCodegen $ do
  let returnType :: Ty ty
      returnType = getType' exp

  reg <- compile exp
  -- Return array through `out' parameter
  when (toLLVMType returnType == "%Arr*") $ do
    instr_ ("store %Arr* " %sh% ", %Arr** %out") reg

  terminate ("ret "%s%" "%op) (toLLVMType returnType) reg
  undefined 

-- foobarDef :: forall retty. ARGS _ retty -> Writer [String] ()
-- foobarDef args = do
--   let exp :: Exp retty
--       exp = getExpression args

--       returnType :: Type retty
--       returnType = getType' exp

--       argList :: [String]
--       argList = getFormattedArgs args
--         -- | showTy returnType == "%Arr*" 
--         -- = getArgs' (ADDARGS (Variable "out" 0) (Type INT8) args)
--         -- | otherwise 
--         -- = getArgs' args

--   emit ("define "%s%" @foobar("%comma%") {") (showTy returnType) argList
--   genBody (compileExpression exp)
--   emit "}" where

--     genBody :: CodegenState -> WriterT [String] Identity ()
--     genBody code = let
    
--       sortedCode ∷ [(String, BasicBlock)]
--       sortedCode = 
--         M.toList (code^.blocks)
--           & sortOn (view (_2.index'))
--           & map (first show)
    
--       genBasicBlock ∷ (String, BasicBlock) → Writer [String] ()
--       genBasicBlock (label, basicBlock) = do
--         emit (string%":") label
--         for_ (basicBlock^.instructions) 
--           (indented string)
--         indented string 
--           (basicBlock^.terminator)
    
--       in for_ sortedCode 
--            genBasicBlock

-- initialiseVars :: ARGS args retTy -> Writer [String] ()
-- initialiseVars = \case
--   NOARGS _ -> 
--     pure ()

--   ADDARGS var rest -> do
--     initialiseVar (Ex var)
--     initialiseVars rest

-- initialiseVar :: Ex V -> Writer [String] ()
-- initialiseVar (Ex (varName ::: Type varTy)) = case varTy of

--   INT8 -> 
--     indented (shown%" = add i8 0, " %shown) varName (8::Int)

--   INT32 -> 
--     indented (shown%" = add i32 0, " %shown) varName (32::Int)

--   TArr INT8 -> do
--     indented (shown%"_mem  = call i8* @malloc(i32 80000)") varName
--     indented (shown%"  = bitcast i8* "%shown%"_mem to %Arr*") varName varName
--     indented (shown%"_mem2 = call i8* @malloc(i32 80000)") varName
--     indented (shown%"_buf_ptr  = getelementptr %Arr* "%shown%", i32 0, i32 0") varName varName
      
--     indented (shown%"_len_ptr  = getelementptr %Arr* "%shown%", i32 0, i32 1") varName varName
--     indented ("store i8* "%shown%"_mem2, i8** "%shown%"_buf_ptr") varName varName
--     indented ("store i32 5, i32* "%shown%"_len_ptr") varName 
      
--     indented ""

--     case varName of
--       Id "arg" 2 -> do
--         indented (shown%"_ptr_a = getelementptr i8* "%shown%"_mem2, i32 0") varName varName
--         indented ("store i8 1, i8* " %shown%"_ptr_a") varName 
--         indented (shown%"_ptr_b = getelementptr i8* "%shown%"_mem2, i32 1") varName varName
--         indented ("store i8 2, i8* " %shown%"_ptr_b") varName 
--         indented (shown%"_ptr_c = getelementptr i8* "%shown%"_mem2, i32 2") varName varName
--         indented ("store i8 3, i8* " %shown%"_ptr_c") varName 
--         indented (shown%"_ptr_d = getelementptr i8* "%shown%"_mem2, i32 3") varName varName
--         indented ("store i8 4, i8* " %shown%"_ptr_d") varName 
--         indented ""
--       Id "arg" 3 -> do
--         indented (shown%"_ptr_a = getelementptr i8* "%shown%"_mem2, i32 0") varName varName
--         indented ("store i8 10, i8* " %shown%"_ptr_a") varName 
--         indented (shown%"_ptr_b = getelementptr i8* "%shown%"_mem2, i32 1") varName varName
--         indented ("store i8 20, i8* " %shown%"_ptr_b") varName 
--         indented (shown%"_ptr_c = getelementptr i8* "%shown%"_mem2, i32 2") varName varName
--         indented ("store i8 30, i8* " %shown%"_ptr_c") varName 
--         indented (shown%"_ptr_d = getelementptr i8* "%shown%"_mem2, i32 3") varName varName
--         indented ("store i8 40, i8* " %shown%"_ptr_d") varName 
  
--   varType -> 
--     error (show varName ++ " " ++ show varType)

-- mainDef :: ARGS args ty -> WriterT [String] Identity ()
-- mainDef args = do
--   let exp :: Exp _
--       exp = getExpression args

--       returnType :: Type _
--       returnType = getType' exp

--       isArray :: Bool
--       isArray 
--         | Type TArr{} <- returnType 
--         = True
--         | otherwise
--         = False

--       argList :: [String]
--       argList = getFormattedArgs args
--         -- | showTy returnType == "%Arr*" 
--         -- = getArgs' (ADDARGS (Variable "out" 0) (Type INT8) args)
--         -- | otherwise 
--         -- = getArgs' args

--   emit "define i32 @main(i32 %argc, i8** %argv) {"

--   initialiseVars args

--   indentedWhen isArray
--     "%arrmem = alloca %Arr*"

--   indented ("%1 = call "%s%" @foobar("%comma%")") (showTy returnType) argList

--   indentedWhen isArray
--     "%arr = load %Arr** %arrmem"

--   indentedWhen isArray
--     "call void @printArr(%Arr* %arr)"

--   tell [dispatch' returnType,
--         "  ret i32 0",
--         "}"]

-- -- Run
-- run :: GetArgs a => a -> IO ()
-- run = getOutput >=> putStrLn

-- run8 ∷ Exp Int8 → IO ()
-- run8 = run

-- run32 ∷ Exp Int32 → IO ()
-- run32 = run

-- runRead :: (GetArgs a, Read (Ret a)) => a -> IO (Ret a)
-- runRead exp = getOutput exp
--   <&> read.last.lines

-- code :: GetArgs a => a -> IO ()
-- code exp = getArgs exp
--   & foobarDef
--   & execWriter
--   & traverse_ putStrLn

-- code8 ∷ Exp Int8 → IO ()
-- code8 = code

-- code88 ∷ (Exp Int8 → Exp Int8) → IO ()
-- code88 = code

-- code888 ∷ (Exp Int8 → Exp Int8 → Exp Int8) → IO ()
-- code888 = code

-- code32 ∷ Exp Int32 → IO ()
-- code32 = code

-- msg :: GetArgs exp => exp -> IO ()
-- msg exp = do
--   getOutput exp

--   system 
--     (intercalate " && " 
--       ["llc-3.6 -filetype=obj /tmp/foo.ll -o /tmp/foo.o", 
--        "gcc -o /tmp/foo /tmp/foo.o -L/usr/lib/i386-linux-gnu -lstdc++", 
--        "/tmp/foo"])
--     & void

-- msg8 ∷ Exp Int8 → IO ()
-- msg8 = msg

-- msg88 ∷ (Exp Int8 → Exp Int8) → IO ()
-- msg88 = msg

-- msg3232 ∷ (Exp Int32 → Exp Int32) → IO ()
-- msg3232 = msg

-- msg888 ∷ (Exp Int8 → Exp Int8 → Exp Int8) → IO ()
-- msg888 = msg

-- msg32 ∷ Exp Int32 → IO ()
-- msg32 = msg

-- -- To use, run 'msg'
-- runPure' :: forall a. GetArgs a => a -> Writer [String] ()
-- runPure' exp_fn = do
--   let args :: ARGS (Args a) (Ret a)
--       args  = getArgs exp_fn

--   tell constants
--   tell declarations
--   tell definitions

--   foobarDef args
--   mainDef   args

-- getOutput :: GetArgs a => a -> IO String
-- getOutput exp_fn = do
--   runPure' exp_fn
--     & execWriter
--     & unlines
--     & writeFile "/tmp/foo.ll"

--   readProcessWithExitCode "lli-3.6" ["/tmp/foo.ll"] "" <&> \case
--       Stdout output → output
--       foo           → show foo

-- test :: IO Bool
-- test = runRead @(Exp I8) (If Tru 42 0)  
--   <&> (== 42)

-- otpXor :: Exp [I8] -> Exp [I8] -> Exp [I8]
-- otpXor xs ys = arr 10 (\i -> xs!i + ys!i)

-- map2 :: (GetType a, GetType b, GetType c) 
--      => (Exp a -> Exp b -> Exp c) 
--      -> (Exp [a] -> Exp [b] -> Exp [c])
-- map2 (¤) xs ys = arr (Len xs) (\i -> (xs!i) ¤ (ys!i))

-- add :: Exp I8 -> _
-- add = (+)

-- foo :: forall a. [a] -> forall b. [b] -> Int
-- foo xs ys = length xs + length ys
