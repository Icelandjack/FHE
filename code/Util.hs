module Util where

import Debug.Trace
import Control.Exception (evaluate)
-- import Codegen
import Control.Monad.Writer

bind2 ∷ (Monad m) ⇒ (a → b → m c) → m a → m b → m c
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
