{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SECD_Lazy where

import Panic
import Prelude hiding (lookup)
import qualified Control.Monad.State.Lazy as S
import qualified Data.Map.Strict as M

import Debug.Trace

type Identifier = Char

data Exp = Id Identifier
         | Lam Identifier Exp
         | App Exp Exp
         | At
         deriving (Eq)

instance Show Exp where
  show (Id i) = show i
  show (Lam c exp) = "λ " <> show c <> "." <> show exp
  show (App e1 e2) = "(" <> show e1 <> " " <> show e2 <> ")"
  show At = "@"

data WHNF = Int Int
          | Prim (WHNF -> WHNF)
          | Closure Exp Identifier Environment
          | Suspension Exp Environment

instance Eq WHNF where
  (Int i) == (Int j) = i == j
  (Closure exp1 id1 env1) == (Closure exp2 id2 env2) =
    (exp1 == exp2) && (id1 == id2) && (env1 == env2)
  (Suspension exp1 env1) == (Suspension exp2 env2) =
    (exp1 == exp2) && (env1 == env2)
  _ == _ = False

instance Show WHNF where
  show (Int i) = "(I " <> show i <> ")"
  show (Prim _) = panic $! "A primop doesn't occur unapplied"
  show (Closure exp id env) =
    "Γ " <> show env <> " ⊢ λ " <> show id <> "." <> show exp
  show (Suspension _ _) = "_"

type Environment = [(Identifier, WHNF')]
type Control = [Exp]
type Dump = [(Stack, Environment, Control)]

type State = (Stack, Environment, Control, Dump)

type Heap = M.Map Pointer WHNF
type Pointer = String

data WHNF' = WHNF WHNF
           | Pointer Pointer
           deriving (Show, Eq)

type Stack = [WHNF']

data EvaluatorState =
  EvaluatorState
    { heap :: Heap
    , count :: Int
    }

newtype Evaluator a =
  Evaluator
    { runEvaluator :: S.State EvaluatorState a
    }
  deriving (Functor, Applicative, Monad, S.MonadState EvaluatorState)

lookup :: Identifier -> Environment -> WHNF'
lookup _ [] = panic "Id not in environment"
lookup i1 ((i2,w):env')
  | i1 == i2 = w
  | otherwise = lookup i1 env'

derefPointer :: Pointer -> Heap -> WHNF
derefPointer p heap =
  case M.lookup p heap of
    Just whnf -> whnf
    Nothing -> panic "Dangling pointer"

freshPointer :: Evaluator String
freshPointer = do
  i <- S.gets count
  S.modify $ \s -> s {count = 1 + i}
  return $ "p_" <> (show i)

eval :: Exp -> WHNF
eval e = (S.evalState (runEvaluator $ evaluate s)
                      (EvaluatorState { heap = M.empty
                                      , count = 0}))
         where
           s = ([], [], [e], [])

evaluate :: State -> Evaluator WHNF
evaluate (s, e, [], []) =
  case s of
    [] -> panic "No value in stack"
    _ -> case head s of
           WHNF whnf -> pure whnf
           Pointer p -> do
             h <- S.gets heap
             let whnf = derefPointer p h
             case whnf of
               Suspension exp env' -> evaluate ([], env', [exp], (s, e, []) : [])
               _ -> pure whnf
evaluate ([], _, [], (s1,e1,c1):d1) = evaluate (s1, e1, c1, d1) -- this step will never occur
evaluate (x:s, _, [], (s1,e1,c1):d1) = evaluate (x:s1, e1, c1, d1)
evaluate (s, e, (Id x):c, d) = evaluate (lookup x e : s, e, c, d)
evaluate (s, e, (Lam bv body):c, d) = evaluate (WHNF (Closure body bv e) : s, e, c, d)
-- in call-by-name and call-by-need  the conditional expression is lazily evaluated by default
evaluate (s, e, At:c, d) =
  case s of
    WHNF (Closure body bv env) : arg : s' ->
      evaluate ([], (bv, arg) : env, [body], (s', e, c) : d)
    WHNF (Prim f) : arg : s' ->
      case arg of
        Pointer p -> do
          h <- S.gets heap
          let whnf = derefPointer p h
          case whnf of
            Suspension exp env' -> do
              res <- evaluate ([], env', [exp], (s, e, c) : d)
              S.modify $ \s -> s {heap = M.insert p res h}
              pure res
            whnf' -> evaluate (WHNF (f whnf') : s', e, c , d)
        WHNF a -> evaluate (WHNF (f a) : s', e, c , d) -- (WHNF a) is an entity on the stack it can never be a suspension because suspensions are never loaded on the stack they stay within the heap
    _ -> panic "Control string has @ any other constructors cannot arise"
evaluate (s, e, (App fun arg) : c, d) = do
  -- heap allocation begin
  p <- freshPointer
  h <- S.gets heap
  S.modify $ \s -> s {heap = M.insert p (Suspension arg e) h}
  -- heap allocation end with pointer p
  evaluate (Pointer p : s, e, fun : At : c, d)

-- Test
-- Identity applied to Church Numeral zero
foo = eval (App (Lam 'x' (Id 'x')) (Lam 'f' (Lam 'y' (Id 'y'))))
