type identifier = char

type exp = Id of identifier
         | Lam of identifier * exp
         | App of exp * exp
         | Cond of exp * exp * exp
         | At
         | Label of identifier * identifier * exp


type whnf = Int of int
          | Prim of (whnf -> whnf)
          | Closure of exp * identifier * environment
          | TRUE
          | Suspension of exp * environment

and environment = (identifier * whnf) list

type stack = whnf list

type control = exp list

type dump = (stack * environment * control) list

type state = stack * environment * control * dump

let rec lookup id env =
  match env with
  | [] -> failwith "id not in environment"
  | (i,w)::env' when id = i -> w
  | _ :: env' -> lookup id env';;
