{-# LANGUAGE FlexibleContexts, RankNTypes #-}
{-# LANGUAGE KindSignatures, TypeApplications, DataKinds, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE UnicodeSyntax, RankNTypes, LambdaCase #-}
{-# LANGUAGE UndecidableInstances, AllowAmbiguousTypes, RecursiveDo, ScopedTypeVariables, ViewPatterns #-}
{-# Language OverloadedStrings, GADTs #-}

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

import Data.Kind
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

import Control.Lens hiding (op, index, (<.), Indexed, (<|), (|>))

import Data.Type.Equality

import Codegen
import Exp
import Repr
import Util
import Vect
import Types
import Variable
import Declarations
import Operators

-- `compile' has to deal with more than just registers so the return
-- works with operands `Op' that are either references (`Name') or
-- constants (`ConstTru', `ConstFls', `ConstNum Int').
compile ∷ ∀a. Exp a → Codegen Op
compile (ArrIx (arr :: Exp (Arr elt)) index) = do
  let 
      elementType :: Ty a
      elementType = getTy @a

  array_val ← compile arr
  index_val ← {- i32toi64 =<< -} compile index

  buffer   ← getBuffer @elt array_val

  elt_ptr ← namedInstr "ptr" ("getelementptr "%string%" "%sh%", i32 "%op) (bufferType @elt) buffer index_val
  -- namedOp "length" ("load i32* "%sh) elt_ptr
  namedOp "val" ("load "%string%" "%sh) (bufferType @elt) elt_ptr

compile (MkArr len var (ixf :: Exp (Sca elt))) = mdo
  entry   ← getBlock
  loop_1  ← newBlock "arr.loop1"
  loop_2  ← newBlock "arr.loop2"
  post    ← newBlock "arr.post"

  arrLength ← compile len
  after_if  ← getBlock

  arrMem    ← mallocStr @elt arrLength
  buffer    ← getBuffer @elt (Reference arrMem)

  jmp loop_1

  -- | arr.loop
  -- Increment from [0…len) 
  setBlock loop_1
  i₀  ← φ "i32" (ConstNum8 0,  after_if)
                (Reference i₁, loop_2')
  i₁  ← incr i₀

  keepGoing ← namedOp "slt"
    ("icmp slt i32 " %sh% ", " %sh) i₀ arrLength

  br keepGoing loop_2 post

  setBlock loop_2 

  ptr ← namedInstr "ptr" 
    ("getelementptr "%string%" " %sh% ", i32 " %sh) (bufferType @elt) buffer i₀

  value    ← compile (rename var i₀ ixf)
  loop_2'  ← getBlock

  ptr ◃(≔) @elt▹ value

  jmp loop_1

  -- | arr.post
  setBlock post

  pure (Reference arrMem)

compile (MkInt8  val) = 
  pure (ConstNum8 val)

compile (MkInt32 val) = 
  pure (ConstNum val)

compile Tru =
  pure ConstTru

compile Fls = 
  pure ConstFls

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
  val_1 ← φ (showExpType init) (init_val, entry)
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
    
compile (MkVar (id ::: _)) = 
  pure (Reference id)

-- TODO: Constant fold this before passing to compile.
compile (Len (MkArr len _ _)) = do
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
-- compile (Lam n body) = 
--   error "compile (Lam n body)

compileExpression :: forall ty. Exp ty -> CodegenState
compileExpression exp = execCodegen $ do
  let returnType :: Ty ty
      returnType = getType' exp

  reg <- compile exp

  -- Return array through `out' parameter
  case returnType of
    ArrRep (NotRep BoolRep) -> instr_ ("store %Arr1* "%sh%", %Arr1** %out_0") reg
    ArrRep (NumRep I32Rep)  -> instr_ ("store %Arr* " %sh%", %Arr** %out_0") reg
    ArrRep (NumRep I8Rep)   -> instr_ ("store %Arr8* "%sh%", %Arr8** %out_0") reg
    _                       -> pure ()

  terminate ("ret "%s%" "%op) (toLLVMType returnType) reg

foobarDef :: Ex Exp -> [Ex V] -> Writer [String] ()
foobarDef expression args = do
  let returnType :: String
      returnType = ex (toLLVMType . getType') expression

      argList :: [String]
      argList
        | returnType == "%Arr1*" 
        = "%Arr1** %out_0" : map (ex toLLVMVar) args
        | returnType == "%Arr*"
        = "%Arr** %out_0" : map (ex toLLVMVar) args
        | returnType == "%Arr8*"
        = "%Arr8** %out_0" : map (ex toLLVMVar) args
        | otherwise 
        = map (ex toLLVMVar) args

  emit ("define "%s%" @foobar("%comma%") {") returnType argList
  genBody (ex compileExpression expression)
  emit "}" where

    genBody :: CodegenState -> WriterT [String] Identity ()
    genBody code = let
    
      sortedCode ∷ [(String, BasicBlock)]
      sortedCode = 
        M.toList (code^.blocks)
          & sortOn (view (_2.index'))
          & map (first show)
    
      genBasicBlock ∷ (String, BasicBlock) → Writer [String] ()
      genBasicBlock (label, basicBlock) = do
        emit (string%":") label
        for_ (basicBlock^.instructions) 
          (indented string)
        indented string 
          (basicBlock^.terminator)
    
      in for_ sortedCode 
           genBasicBlock

initialiseVars :: [Ex V] -> Writer [String] ()
initialiseVars = traverse_ initialiseVar

initialiseVar :: Ex V -> Writer [String] ()
initialiseVar (Ex (varName ::: varTy)) =
  case varTy of

  ScaRep (NumRep I8Rep) -> 
    indented (shown%" = add i8 0, " %shown) varName (8::Int)

  ScaRep (NumRep I32Rep) -> 
    indented (shown%" = add i32 0, " %shown) varName (32::Int)

  ArrRep (NumRep I32Rep) -> do
    indented (shown%"_mem  = call i8* @malloc(i32 80000)") varName
    indented (shown%"  = bitcast i8* "%shown%"_mem to %Arr*") varName varName
    indented (shown%"_mem2 = call i8* @malloc(i32 80000)") varName
    indented (shown%"b  = bitcast i8* "%shown%"_mem2 to i32*") varName varName
    indented (shown%"_buf_ptr  = getelementptr %Arr* "%shown%", i32 0, i32 0") varName varName
      
    indented (shown%"_len_ptr  = getelementptr %Arr* "%shown%", i32 0, i32 1") varName varName
    indented ("store i32* "%shown%"b, i32** "%shown%"_buf_ptr") varName varName
    indented ("store i32 4, i32* "%shown%"_len_ptr") varName 
      
    indented ""

    case varName of
      Id "arg" 1 -> do
        -- First argument: [1,2,3,4]
        indented (shown%"_ptr_a = getelementptr i32* "%shown%"b, i32 0") varName varName
        indented ("store i32 1, i32* " %shown%"_ptr_a") varName 
        indented (shown%"_ptr_b = getelementptr i32* "%shown%"b, i32 1") varName varName
        indented ("store i32 2, i32* " %shown%"_ptr_b") varName 
        indented (shown%"_ptr_c = getelementptr i32* "%shown%"b, i32 2") varName varName
        indented ("store i32 3, i32* " %shown%"_ptr_c") varName 
        indented (shown%"_ptr_d = getelementptr i32* "%shown%"b, i32 3") varName varName
        indented ("store i32 4, i32* " %shown%"_ptr_d") varName 
        indented ""
      Id "arg" 0 -> do
        -- Second argument: [10,20,30,40]
        indented (shown%"_ptr_a = getelementptr i32* "%shown%"b, i32 0") varName varName
        indented ("store i32 10, i32* " %shown%"_ptr_a") varName 
        indented (shown%"_ptr_b = getelementptr i32* "%shown%"b, i32 1") varName varName
        indented ("store i32 20, i32* " %shown%"_ptr_b") varName 
        indented (shown%"_ptr_c = getelementptr i32* "%shown%"b, i32 2") varName varName
        indented ("store i32 30, i32* " %shown%"_ptr_c") varName 
        indented (shown%"_ptr_d = getelementptr i32* "%shown%"b, i32 3") varName varName
        indented ("store i32 40, i32* " %shown%"_ptr_d") varName 

      sh → error ("ERROR: initialiseVar: " ++ show sh)

  ArrRep (NumRep I8Rep) -> do
    indented (shown%"_mem  = call i8* @malloc(i32 80000)") varName
    indented (shown%"  = bitcast i8* "%shown%"_mem to %Arr8*") varName varName
    indented (shown%"_mem2 = call i8* @malloc(i32 80000)") varName
    indented (shown%"b  = bitcast i8* "%shown%"_mem2 to i8*") varName varName
    indented (shown%"_buf_ptr  = getelementptr %Arr8* "%shown%", i32 0, i32 0") varName varName
      
    indented (shown%"_len_ptr  = getelementptr %Arr8* "%shown%", i32 0, i32 1") varName varName
    indented ("store i8* "%shown%"b, i8** "%shown%"_buf_ptr") varName varName
    indented ("store i32 4, i32* "%shown%"_len_ptr") varName 
      
    indented ""

    case varName of
      Id "arg" 1 -> do
        -- First argument: [1,2,3,4]
        indented (shown%"_ptr_a = getelementptr i8* "%shown%"b, i32 0") varName varName
        indented ("store i8 1, i8* " %shown%"_ptr_a") varName 
        indented (shown%"_ptr_b = getelementptr i8* "%shown%"b, i32 1") varName varName
        indented ("store i8 2, i8* " %shown%"_ptr_b") varName 
        indented (shown%"_ptr_c = getelementptr i8* "%shown%"b, i32 2") varName varName
        indented ("store i8 3, i8* " %shown%"_ptr_c") varName 
        indented (shown%"_ptr_d = getelementptr i8* "%shown%"b, i32 3") varName varName
        indented ("store i8 4, i8* " %shown%"_ptr_d") varName 
        indented ""
      Id "arg" 0 -> do
        -- Second argument: [10,20,30,40]
        indented (shown%"_ptr_a = getelementptr i8* "%shown%"b, i32 0") varName varName
        indented ("store i8 10, i8* " %shown%"_ptr_a") varName 
        indented (shown%"_ptr_b = getelementptr i8* "%shown%"b, i32 1") varName varName
        indented ("store i8 20, i8* " %shown%"_ptr_b") varName 
        indented (shown%"_ptr_c = getelementptr i8* "%shown%"b, i32 2") varName varName
        indented ("store i8 30, i8* " %shown%"_ptr_c") varName 
        indented (shown%"_ptr_d = getelementptr i8* "%shown%"b, i32 3") varName varName
        indented ("store i8 40, i8* " %shown%"_ptr_d") varName 

      sh → error ("ERROR: initialiseVar: " ++ show sh)

  ArrRep (NotRep BoolRep) → do
    indented (shown%"_mem  = call i8* @malloc(i32 80000)") varName
    indented (shown%"  = bitcast i8* "%shown%"_mem to %Arr1*") varName varName
    indented (shown%"_mem2 = call i8* @malloc(i32 80000)") varName
    indented (shown%"b  = bitcast i8* "%shown%"_mem2 to i1*") varName varName
    indented (shown%"_buf_ptr  = getelementptr %Arr1* "%shown%", i32 0, i32 0") varName varName
      
    indented (shown%"_len_ptr  = getelementptr %Arr1* "%shown%", i32 0, i32 1") varName varName
    indented ("store i1* "%shown%"b, i1** "%shown%"_buf_ptr") varName varName
    indented ("store i32 4, i32* "%shown%"_len_ptr") varName 
      
    indented ""

    case varName of
      Id "arg" 1 -> do
        -- First argument: [1,2,3,4]
        indented (shown%"_ptr_a = getelementptr i1* "%shown%"b, i32 0") varName varName
        indented ("store i1 1, i1* " %shown%"_ptr_a") varName 
        indented (shown%"_ptr_b = getelementptr i1* "%shown%"b, i32 1") varName varName
        indented ("store i1 2, i1* " %shown%"_ptr_b") varName 
        indented (shown%"_ptr_c = getelementptr i1* "%shown%"b, i32 2") varName varName
        indented ("store i1 3, i1* " %shown%"_ptr_c") varName 
        indented (shown%"_ptr_d = getelementptr i1* "%shown%"b, i32 3") varName varName
        indented ("store i1 4, i1* " %shown%"_ptr_d") varName 
        indented ""
      Id "arg" 0 -> do
        -- Second argument: [10,20,30,40]
        indented (shown%"_ptr_a = getelementptr i1* "%shown%"b, i32 0") varName varName
        indented ("store i1 10, i1* " %shown%"_ptr_a") varName 
        indented (shown%"_ptr_b = getelementptr i1* "%shown%"b, i32 1") varName varName
        indented ("store i1 20, i1* " %shown%"_ptr_b") varName 
        indented (shown%"_ptr_c = getelementptr i1* "%shown%"b, i32 2") varName varName
        indented ("store i1 30, i1* " %shown%"_ptr_c") varName 
        indented (shown%"_ptr_d = getelementptr i1* "%shown%"b, i32 3") varName varName
        indented ("store i1 40, i1* " %shown%"_ptr_d") varName 

      sh → error ("ERROR: initialiseVar: " ++ show sh)
  
  varType -> 
    error ("ERROR2: initialiseVar: " ++ show varName ++ " " ++ show varType)

mainDef :: Ex Exp -> [Ex V] -> WriterT [String] Identity ()
mainDef expression args = do
  let returnType :: String
      returnType = ex (toLLVMType . getType') expression

      isArray :: Bool
      isArray = ex ((\case ArrRep{} -> True; _ -> False) . getType') expression

      argList :: [String]
      argList 
        | returnType == "%Arr1*" 
        = "%Arr1** %out_0" : map (ex toLLVMVar) args
        | returnType == "%Arr*"
        = "%Arr** %out_0" : map (ex toLLVMVar) args
        | returnType == "%Arr8*"
        = "%Arr8** %out_0" : map (ex toLLVMVar) args
        | otherwise 
        = map (ex toLLVMVar) args

  emit "define i32 @main(i32 %argc, i8** %argv) {"

  initialiseVars args

  case expression of
    Ex (getType' → ArrRep (NotRep BoolRep))  → do
      indented "%out_0 = alloca %Arr1*"
    Ex (getType' → ArrRep (NumRep I32Rep))  → do
      indented "%out_0 = alloca %Arr*"
    Ex (getType' → ArrRep (NumRep I8Rep)) → do
      indented "%out_0 = alloca %Arr8*"
    _                    → pure ()

  indented ("%1 = call "%s%" @foobar("%comma%")") returnType argList

  case expression of
    Ex (getType' → ArrRep (NotRep BoolRep))  → do
      indented "%arr1 = load %Arr1** %out_0"
      indented "call void @printArr1(%Arr1* %arr1)"
    Ex (getType' → ArrRep (NumRep I32Rep))  → do
      indented "%arr = load %Arr** %out_0"
      indented "call void @printArr(%Arr* %arr)"
    Ex (getType' → ArrRep (NumRep I8Rep)) → do
      indented "%arr8 = load %Arr8** %out_0"
      indented "call void @printArr8(%Arr8* %arr8)"
    _                    → pure ()

  tell [dispatch returnType,
        "  call void @nl()",
        "  ret i32 0",
        "}"]

-- -- Run
run :: GetArgs a => a -> IO ()
run = getOutput >=> putStr

run8 ∷ Exp TInt8 → IO ()
run8 = run

run32 ∷ Exp TInt → IO ()
run32 = run

runRead :: (Read b, GetArgs a) => a -> IO b
runRead exp = getOutput exp
  <&> read.head.lines

code :: GetArgs a => a -> IO ()
code exp = getArgs exp
  & uncurry foobarDef
  & execWriter
  & traverse_ putStrLn

msg :: GetArgs exp => exp -> IO ()
msg exp = do
  getOutput exp

  system 
    (intercalate " && " 
      ["llc-3.6 -filetype=obj /tmp/foo.ll -o /tmp/foo.o", 
       "gcc -o /tmp/foo /tmp/foo.o -L/usr/lib/i386-linux-gnu -lstdc++", 
       "/tmp/foo"])
    & void

-- code8   = code @(Exp Int8)
-- code88  = code @(Exp Int8 → Exp Int8)
-- code888 = code @(Exp Int8 → Exp Int8 → Exp Int8)
-- code32  = code @(Exp Int)
-- msg8    = msg  @(Exp Int8)
-- msg88   = msg  @(Exp Int8 → Exp Int8)
-- msgII   = msg  @(Exp Int → Exp Int)
-- msg888  = msg  @(Exp Int8 → Exp Int8 → Exp Int8)
-- msg32   = msg  @(Exp Int)

-- To use, run 'msg'
runPure' :: forall a. GetArgs a => a -> Writer [String] ()
runPure' exp_fn = do
  let exp  :: Ex Exp
      args :: [Arg]
      (exp, args) = getArgs exp_fn

  tell constants
  tell declarations
  tell definitions

  foobarDef exp args
  mainDef   exp args

getOutput :: GetArgs a => a -> IO String
getOutput exp_fn = do
  runPure' exp_fn
    & execWriter
    & unlines
    & writeFile "/tmp/foo.ll"

  readProcessWithExitCode "lli-3.6" ["/tmp/foo.ll"] "" <&> \case
    Stdout output → output
    foo           → show foo

map2 :: (GetSca a, GetSca b, GetSca c) 
     => (Exp (Sca a) -> Exp (Sca b) -> Exp (Sca c)) 
     -> (Exp (Arr a) -> Exp (Arr b) -> Exp (Arr c))
map2 (¤) xs ys = arr (Len xs `min'` Len ys) (\i -> (xs!i) ¤ (ys!i))

otp :: (GetSca sca, B.Bits (ScaToType sca)) => Exp (Arr sca) -> Exp (Arr sca) -> Exp (Arr sca)
otp = map2 Xor

-- -- otp' :: (GetTy c, B.Bits c) => Exp [c] -> Exp [c] -> Exp [c]
-- -- otp' = map2 Xor

-- -- add :: Exp Int8 -> _
-- -- add = (+)

-- -- foo :: forall a. [a] -> forall b. [b] -> Int
-- -- foo xs ys = length xs + length ys

-- -- arr342 :: Exp [Int]
-- -- arr342 = 
-- --   arr 3 $ \ix → If (0 `Equal` ix) 3
-- --         $       If (1 `Equal` ix) 4 
-- --         $                         2

-- -- id' :: forall a. GetTy a => Exp a -> Exp a
-- -- id' x = 
-- --   case getTy @a of
-- --     I -> If (42 ◃Equal @_ @Int▹ 5 ◃Equal▹ Fls) x 42
-- --     _ -> If Fls x x

-- -- (≟) :: forall ty₁ ty₂. (GetTy ty₁, GetTy ty₂) => Maybe (ty₁ :~: ty₂)
-- -- (≟) = 
-- --   case (getTy @ty₁, getTy @ty₂) of
-- --     (I8, I8) -> Just Refl
-- --     (I, I) -> Just Refl
-- --     (F, F) -> Just Refl
-- --     (D, D) -> Just Refl
-- --     (B, B) -> Just Refl
-- --     (C, C) -> Just Refl
-- --     -- (A (a1 :: Ty t1), A (a2 :: Ty t2)) -> do
-- --     --   Refl ← (≟) @t1 @t2
-- --     --   pure Refl
-- --     (P x1 y1, P x2 y2) -> do
-- --       Refl ← (≟) @ty₁ @ty₂
-- --       pure Refl

-- -- (·≟·) :: Ty (ty₁ :: Type) → Ty (ty₂ :: Type) → Maybe (ty₁ :~: ty₂)
-- -- I8  ·≟· I8  = pure Refl
-- -- I   ·≟· I   = pure Refl
-- -- F   ·≟· F   = pure Refl
-- -- D   ·≟· D   = pure Refl
-- -- B   ·≟· B   = pure Refl
-- -- C   ·≟· C   = pure Refl
-- -- A x ·≟· A y = do
-- --   Refl ← x ·≟· y
-- --   pure Refl
-- -- -- P (x1 :: Ty a1) (x2 :: Ty a2) ·≟· P (y1 :: Ty b1) (y2 :: Ty b2) = do
-- -- --   Refl ← x1 ·≟· y1
-- -- --   Refl ← x2 ·≟· y2 
-- -- --   undefined 

-- -- equal :: forall ty₁ ty₂. (GetTy ty₁, GetTy ty₂) => Exp ty₁ -> Exp ty₂ → Exp Bool
-- -- equal exp₁ exp₂ = fromMaybe Fls $ do
-- --   case (getTy @ty₁, getTy @ty₂) of

-- -- u :: Exp Int -> Exp [Int]
-- -- u n = arr n id

-- -- test :: IO Bool
-- -- test = runRead @(Exp Int) (If Tru 42 0)  
-- --   <&> (== 42)

-- -- uu :: Exp [Int] -> Exp [Int]
-- -- uu xs = 
-- --     xs
-- --   ◃map2 (+)▹
-- --     fromList [If Fls 1 666,If (id' Tru) 353 2,If (id' Fls) (id' 3) (id' 555), 5]
-- --   ◃map2 (+)▹
-- --     fromList [id' 10,id' 20,id' 30,id' 40, 50]

