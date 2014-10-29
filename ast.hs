import Data.List

type AST = [Statement]

data Statement = S [Expr]

instance Show Statement where
  show (S exprs) = intercalate "; " (map show exprs)

data Expr = I Double | Add Expr Expr
  deriving Show

eval ∷ AST → IO ()
eval = mapM_ statement

statement ∷ Statement → IO ()
statement (S exprs) = mapM_ print exprs

expr ∷ Expr → Double
expr = \case
  I d     → d
  Add a b → expr a + expr b
