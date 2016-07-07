{-# LANGUAGE 
    FlexibleContexts, KindSignatures, TypeApplications, DataKinds, 
    StandaloneDeriving, TypeOperators, ExplicitNamespaces, UnicodeSyntax, 
    RankNTypes, LambdaCase, UndecidableInstances, AllowAmbiguousTypes, 
    FlexibleInstances, TypeFamilyDependencies, ConstraintKinds, 
    BangPatterns, DataKinds, DeriveDataTypeable, DeriveFoldable, 
    DeriveFunctor, DeriveGeneric, DeriveTraversable, DefaultSignatures, 
    DisambiguateRecordFields, EmptyCase, FunctionalDependencies, GADTs, 
    GeneralizedNewtypeDeriving, InstanceSigs, ImplicitParams, ImpredicativeTypes, 
    LambdaCase, LiberalTypeSynonyms, MagicHash, MultiParamTypeClasses, MultiWayIf, 
    MonadComprehensions, NamedFieldPuns, NamedWildCards, NumDecimals, 
    NoMonomorphismRestriction, ParallelListComp, PartialTypeSignatures, 
    PatternSynonyms, PolyKinds, PostfixOperators, RankNTypes, RecordWildCards, 
    RecursiveDo, RoleAnnotations, ScopedTypeVariables, StandaloneDeriving, 
    TemplateHaskell, TupleSections, TypeFamilies, TypeOperators, UnboxedTuples, 
    UnicodeSyntax, ViewPatterns, QuasiQuotes, TypeInType, ApplicativeDo, UndecidableSuperClasses #-}

module Util where

import Debug.Trace
import Control.Exception (evaluate)
-- import Codegen
import Control.Monad.Writer
import Text.Read (readMaybe)
import System.Exit
import Data.Kind
import GHC.TypeLits

bind2 ∷ Monad m ⇒ (a → b → m c) → m a → m b → m c
bind2 f m1 m2 = do
    x1 ← m1
    x2 ← m2
    f x1 x2

dbg ∷ (Monad m, Show a) ⇒ a → m ()
dbg a = 
  return $! traceShow a ()

-- debugBlock ∷ Codegen ()
-- debugBlock = dbg =<< getBlock

a ∷ IO ()
a = putStrLn =<< readFile "/tmp/foo.ll"

-- Why aren't these in Control.Monad.Writer?

-- Passes a Kleisli-arrow that makes use of the accumulated log
useOutput ∷ MonadWriter w m ⇒ (w → m a) → m b → m b
useOutput f action = do
  ~(ret, action') ← listens f action
  action'
  return ret

evalWriterT ∷ Functor m ⇒ WriterT w m a → m a
evalWriterT c = fst <$> runWriterT c

evalWriter ∷ Writer w a → a
evalWriter = fst . runWriter 

pattern Stdout a ← (ExitSuccess, a, _)
pattern Stderr b ← (ExitFailure _, _, b)

pattern ReadInt ∷ Int → String
pattern ReadInt n ← (readMaybe → Just (n ∷ Int)) where
        ReadInt n = show n

type TypeClass = Type -> Constraint

-- Taken from 'servant'
-- | If either a or b produce an empty constraint, produce an empty constraint.
type family (a :: Constraint) ∨ (b :: Constraint) :: Constraint where
  () ∨ b  = ()
  a  ∨ () = ()
  a  ∨ b  = TypeError (Text "∨: " :<>: ShowType a :<>: ShowType b)

-- | If both a or b produce an empty constraint, produce an empty constraint.
type family (a :: Constraint) ∧ (b :: Constraint) :: Constraint where
  () ∧ () = ()
  a  ∧ b  = TypeError (Text "∨: " :<>: ShowType a :<>: ShowType b)

infixl 0 ◃, ▹, <|, |>
(◃) = flip ($)
(<|) = flip ($)
(▹) = ($)
(|>) = ($)

type x ◃ f = f x
type f ▹ x = f x

infixr 9 `Compose`
class    (f (g x)) => (f `Compose` g) x
instance (f (g x)) => (f `Compose` g) x

infixl 7 `And`
class    (f x, g x) => (f `And` g) x
instance (f x, g x) => (f `And` g) x

