module Util where

import Debug.Trace
import Control.Exception (evaluate)
import Codegen

bind2 ∷ (Monad m) ⇒ (a → b → m c) → m a → m b → m c
bind2 f m1 m2 = do
    x1 ← m1
    x2 ← m2
    f x1 x2

dbg ∷ (Monad m, Show a) ⇒ a → m ()
dbg a = 
  return $! traceShow a ()

debugBlock ∷ Codegen ()
debugBlock = dbg =<< getBlock

a ∷ IO ()
a = putStrLn =<< readFile "/tmp/foo.ll"
