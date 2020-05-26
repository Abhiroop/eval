{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module SECD where

import Panic
import Prelude hiding (lookup)

type Identifier = Char

data Exp = Id Identifier
         | Lam Char Exp
         | App Exp Exp
         | Cond  Exp   Exp   Exp
--              then  else  predicate
         | At
         deriving (Eq)

instance Show Exp where
  show (Id i) = show i
  show (Lam c exp) = "λ " <> show c <> "." <> show exp
  show (App e1 e2) = "(" <> show e1 <> " " <> show e2 <> ")"
  show (Cond e1 e2 e3) =
    "if " <> (show e1) <> "then " <> (show e2) <> "else " <> (show e3)
  show At = "@"

data WHNF = Int Int
          | Prim (WHNF -> WHNF)
          | Closure Exp Identifier Environment
          | TRUE

instance Eq WHNF where
  (Int i) == (Int j) = i == j
  TRUE == TRUE = True
  (Closure exp1 id1 env1) == (Closure exp2 id2 env2) =
    (exp1 == exp2) && (id1 == id2) && (env1 == env2)
  x == y = False

instance Show WHNF where
  show (Int i) = "(I " <> show i <> ")"
  show (Prim _) = panic $! "A primop doesn't occur unapplied"
  show (Closure exp id env) =
    "Γ " <> show env <> " ⊢ λ " <> show id <> "." <> show exp
  show TRUE = "True"

type Stack = [WHNF]
type Environment = [(Identifier, WHNF)]
type Control = [Exp]
type Dump = [(Stack, Environment, Control)]

type State = (Stack, Environment, Control, Dump)

lookup :: Identifier -> Environment -> WHNF
lookup _ [] = panic "Id not in environment"
lookup i1 ((i2,w):env')
  | i1 == i2 = w
  | otherwise = lookup i1 env'

evaluate :: State -> WHNF
evaluate (s, _, [], []) =
  case s of
    [] -> panic "No value in stack"
    _ -> head s
evaluate ([], _, [], (s1,e1,c1):d1) = evaluate (s1, e1, c1, d1) -- this step will never occur
evaluate (x:s, _, [], (s1,e1,c1):d1) = evaluate (x:s1, e1, c1, d1)
evaluate (s, e, (Id x):c, d) = evaluate (lookup x e : s, e, c, d)
evaluate (s, e, (Lam bv body):c, d) = evaluate ((Closure body bv e) : s, e, c, d)
evaluate (pred:s, e, (Cond th els _):At:c, d) =
  if pred == TRUE
  then evaluate (s, e,  th:c, d)
  else evaluate (s, e, els:c, d)
evaluate (s, e, At:c, d) =
  case s of
    Closure body bv env : arg : s' ->
      evaluate ([], (bv, arg) : env, [body], (s', e, c) : d)
    Prim f : arg : s' -> evaluate (f arg : s', e, c , d)
    _ -> panic "Control string has @ any other constructors cannot arise"
evaluate (s, e, (App fun arg) : c, d) = evaluate (s, e, arg : fun : At : c, d)
evaluate (s, e, (Cond th els pred):c, d) = evaluate (s, e, pred : (Cond th els pred) : At : c, d)


-- Test
-- Identity applied to Church Numeral zero
foo = evaluate ([], [], [(App (Lam 'x' (Id 'x')) (Lam 'f' (Lam 'y' (Id 'y'))))], [])
