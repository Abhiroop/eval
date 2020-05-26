{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module SECD where

import Panic
import Prelude hiding (lookup)

type Identifier = Char

data Exp = Id Identifier
         | Lam Char Exp
         | App Exp Exp
         | At

data WHNF = Int Int
          | Prim (WHNF -> WHNF)
          | Closure Exp Identifier Environment

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
evaluate (x:s, _, [], (s1,e1,c1):d1) = evaluate (x:s1, e1, c1, d1)
evaluate (s, e, (Id x):c, d) = evaluate (lookup x e : s, e, c, d)
evaluate (s, e, (Lam bv body):c, d) = evaluate ((Closure body bv e) : s, e, c, d)
evaluate (s, e, At:c, d) =
  case s of
    Closure body bv env : arg : s' -> evaluate ([], (bv, arg) : env, [body], (s', e, c) : d)
    Prim f : arg : s' -> evaluate (f arg : s', e, c , d)
    _ -> panic "Control string has @ any other constructors cannot arise"
evaluate (s, e, (App fun arg) : c, d) = evaluate (s, e, arg : fun : c, d)
evaluate ([], _, [], d) = panic "undefined state"
