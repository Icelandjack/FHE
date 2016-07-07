{-# Language OverloadedStrings #-}

import Debug.Trace
import IR2
import Exp
import Data.Functor.Identity
import Control.Monad.Gen
import Control.Monad.Writer
import Control.Monad.Cont
import qualified Data.Map as M
import Bound.Scope.Simple
import Operators
import Types
import Funcs
import Codegen
import Variable
import Control.Lens hiding (assign, op)
import Data.List
import Data.Bifunctor
import Data.Foldable

import Formatting
import Formatting.Internal
import Formatting.ShortFormatters

a = 1 + 2 + 3 :: Exp TInt8

þýða :: Exp a -> HAHA (Identity Op)
þýða = \case
  MkInt8 val -> assign $
    Int 8  (fromIntegral val)

  MkInt32 val -> assign $
    Int 32 (fromIntegral val)

  Tru -> assign ETru

  Fls -> assign EFls

  BinOp (Bin OpAdd _fn) a b -> do
    var₁ <- þýða a
    var₂ <- þýða b
    mk (Binop Add var₁ var₂)

  BinOp (Bin OpMul _fn) a b -> do
    var₁ <- þýða a
    var₂ <- þýða b
    mk (Binop Mul var₁ var₂)

  -- MkArr 
  --  (Constant Get32 10)
  --  V₀
  --  (MkMul (MkVar V₀) (MkVar V₀))
  MkArr len id body -> do
    len' <- þýða len
    uuu  <- þýða body

    -- Exp (Sca sca)
    mk (For len' undefined)

  (traceShowId -> foo) -> error (show foo)

co :: Prog Identity Op -> Codegen Op
co = \case
  Ret (Identity a) -> do
    terminate ("ret i32 "%op) a
    pure a    

  Assign ETru rest -> co $
    Identity ConstTru `inst1` rest

  Assign EFls rest -> co $
    Identity ConstFls `inst1` rest

  Assign (Int 32 n) rest -> co $
    Identity (ConstNum (fromIntegral n)) `inst1` rest

  Assign (Int 8 n) rest -> co $
    Identity (ConstNum8 (fromIntegral n)) `inst1` rest

  Binop Add (Identity a) (Identity b) rest -> do
    x <- namedOp "add" ("add i32 "%sh%", "%sh) a b
    co $ 
      Identity x `inst1` rest

compileAll :: Exp a -> IO ()
compileAll exp = let
  haha :: Prog Identity Op
  haha = runProgm (þýða exp)

  in putStrLn $ unlines $ execWriter $ genBody (execCodegen (co haha))

genBody :: CodegenState -> WriterT [String] Identity ()
genBody code = let
  sortedCode :: [(String, BasicBlock)]
  sortedCode = 
    M.toList (code^.blocks)
    & sortOn (view (_2.index'))
    & map (first show)
    
  genBasicBlock :: (String, BasicBlock) -> Writer [String] ()
  genBasicBlock (label, basicBlock) = do
    emit (string%":") label
    for_ (basicBlock^.instructions) 
      (indented string)
    indented string 
      (basicBlock^.terminator)
    
  in for_ sortedCode 
     genBasicBlock


    -- namedOp "add" (s% " " %s% " " %sh% ", " %sh) "add" "i32"

  -- compileBinop operator reg₁ reg₂

-- createBinop :: a. GetTy a => String -> Op -> Op -> Codegen Op
-- createBinop op =  
--   namedOp (last (words op))
--     (s% " " %s% " " %sh% ", " %sh) op (toLLVMType (getTy @a))

-- compileBinop :: forall a b c. BinOp a b c -> Op -> Op -> Codegen Op
-- compileBinop = \case
--   OpAdd -> 
--     createBinop @a "add" 
--   OpSub -> 
--     createBinop @a "sub"
--   OpMul -> 
--     createBinop @a "mul" 

--   OpEqual -> 
--     createBinop @a "icmp eq" 
--   OpNotEqual -> 
--     createBinop @a "icmp ne"
--   OpLessThan -> 
--     createBinop @a "icmp slt"
--   OpLessThanEq -> 
--     createBinop @a "icmp sle" 
--   OpGreaterThan -> 
--     createBinop @a "icmp sgt" 
--   OpGreaterThanEq -> 
--     createBinop @a "icmp sge"

--   -- a /\ b = a * b
--   OpAnd 
--     createBinop @TBool "mul" 
--   -- a \/ b = a + b + ab
--   OpOr -> \a b -> do
--     a_plus_b <- createBinop @TBool "add" a b
--     a_mult_b <- createBinop @TBool "mul" a b
--     createBinop @TBool "add" a_plus_b a_mult_b

--   OpXor ->
--     createBinop @c "xor" 

--   OpPair -> let
--     insNum ∷ Op -> Op -> Int -> Codegen Op
--     insNum = 
--       namedOp "updated" 
--        ("insertvalue %pairi32i32 "%op%", i32 "%op%", "%d) 

--     mkPair ∷ Op -> Op -> Codegen Op
--     mkPair x y = do
--      let initVal = Struct [Undef "i32", Undef "i32"]
--      retVal₁ ← insNum initVal x 0
--      retVal₂ ← insNum retVal₁ y 1
--      return retVal₂

--     in mkPair

--   foo -> error (show foo ++ " ndefined shit")
