module SimplePull where

import Data.Bits
import Control.Applicative

-- void RC4_set_key(RC4_KEY *key,
--                  int len,
--                  const unsigned char *data);

-- void RC4(RC4_KEY *key,
--          unsigned long len,
--          const unsigned char *indata,
--          unsigned char *outdata);

instance Num Exp where
  (+)         = Add
  fromInteger = Lit . fromInteger

data Exp
  = Var String
  | Lit Int
  | Add Exp Exp
  | Min Exp Exp
  | Xor Exp Exp
  deriving Show

data Pull a = P (Exp → a) Exp

instance Functor Pull where
  fmap f (P ixf len) = P (f . ixf) len

(⊔) = Min
(⊕) = Xor
var = Var

map₂ ∷ (a → b → c) → (Pull a → Pull b → Pull c)
map₂ f (P ixf₁ len₁) (P ixf₂ len₂) =
  P (\index → f (ixf₁ index) (ixf₂ index)) (len₁ ⊔ len₂)

foo ∷ Int → Pull Exp
foo len = P id (Lit len)

eval ∷ Exp → Int
eval = \case
  Lit i → i
  Add a b → eval a + eval b
  Min a b → min (eval a) (eval b)
  Xor a b → xor (eval a) (eval b)
  Var{}   → error "var"

compile ∷ Pull Exp → IO ()
compile (P ixf (eval → len)) = do
  mapM_ print [ ixf (Lit index) | index ← [0..len-1] ]

compileExp ∷ Exp → String
compileExp = \case
  Var x   → x
  Lit i   → show i
  Add a b → "(" ++ compileExp a ++ " + " ++ compileExp b ++ ")"
  Min a b → "min(" ++ compileExp a ++ ", " ++ compileExp b ++ ")"
  Xor a b → "(" ++ compileExp a ++ " ^ " ++ compileExp b ++ ")"

compile' ∷ Pull Exp → IO ()
compile' (P ixf (eval → len)) = do {
  putStrLn("for (int i = 0; i < " ++ show len ++ "; ++i) {");
  putStr("  ");
  
  putStrLn(compileExp(ixf(var"i")));
  
  putStrLn("}");
}

example₁ ∷ Pull Exp
example₁ = example₂ (foo 10)

example₂ ∷ Pull Exp → Pull Exp
example₂ = map₂ (⊕) ((+ 1) <$> foo 53) 
