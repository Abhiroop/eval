type identifier = char

type pointer = string

type exp = Id of identifier
         | Lam of identifier * exp
         | App of exp * exp
         | At

type whnf = Int of int
          | Prim of (whnf -> whnf)
          | Closure of exp * identifier * environment
          | Suspension of exp * environment

and whnf' = WHNF of whnf
          | Pointer of pointer

and environment = (identifier * whnf') list

type stack = whnf' list

type control = exp list

type dump = (stack * environment * control) list

type state = stack * environment * control * dump

let heap : (pointer * whnf) list ref = ref []

let rec lookup key kv =
  match kv with
  | [] -> failwith "Key not found"
  | (k,v)::_ when key = k -> v
  | _ :: kv' -> lookup key kv';;

let freshPointer = "p_" ^ string_of_int (Random.int 10000)

let rec evaluate (s, e, c, d) =
  match (s, e, c, d) with
    | ([], _, [], []) -> failwith "No final value in stack"
    | (h :: _, e, [], []) ->
        begin
        match h with
          | WHNF whnf -> whnf
          | Pointer p ->
              match (lookup p !heap) with
                | Suspension (exp, env') -> evaluate ([], env', [exp], (s, e, []) :: [])
                | whnf -> whnf
        end
    | ([], _, [], (s1,e1,c1)::d1) -> evaluate (s1, e1, c1, d1) (* this step will never occur *)
    | (x::s, _, [], (s1,e1,c1)::d1) -> evaluate (x::s1, e1, c1, d1)
    | (s, e, (Id x)::c, d) -> evaluate ((lookup x e) :: s, e, c, d)
    | (s, e, (Lam (bv, body))::c, d) -> evaluate (WHNF (Closure (body,bv,e)) :: s, e, c, d)
    | (s, e, (App (func, arg))::c, d) ->
        let p = freshPointer in
        let () = heap := (p, Suspension (arg,e)) :: !heap in
        evaluate (Pointer p :: s, e, func :: At :: c, d)
    | (s, e, At :: c, d) ->
        match s with
          | WHNF (Closure (body, bv, env)) :: arg :: s' ->
              evaluate ([], (bv, arg) :: env, [body], (s', e, c) :: d)
          | (WHNF (Prim f)) :: arg :: s' ->
              match arg with
                | Pointer p ->
                    begin
                    match (lookup p !heap) with
                      | Suspension (exp, env') ->
                          let res = evaluate ([], env', [exp], (s, e, c) :: d) in
                          let () = heap := (p,res) :: !heap in
                          res
                      | whnf' -> evaluate (WHNF (f whnf') :: s', e, c , d)
                    end
                | WHNF a -> evaluate (WHNF (f a) :: s', e, c , d)
          | _ -> failwith "Control string has @ any other constructors cannot arise"

let eval e = evaluate ([], [], [e], [])

(*       Test       *)

let rec exp_to_string exp =
  match exp with
    | Id i -> String.make 1 i
    | Lam (c, exp) -> "λ " ^ (String.make 1 c) ^ "." ^ (exp_to_string exp)
    | App (exp1, exp2) -> "(" ^ (exp_to_string exp1) ^ " " ^ (exp_to_string exp) ^ ")"
    | At -> "@"

(* Print only closed expressions i.e. assuming no free variables *)
let rec whnf_to_string whnf =
  match whnf with
    | Int i -> string_of_int i
    | Prim _ -> failwith "A primop doesn't occur unapplied"
    | Closure (exp, id, _) ->
       "Γ  ⊢ λ " ^ (String.make 1 id) ^ "." ^ exp_to_string exp
    | Suspension _ -> "_"

let test = eval
            (App
              ( Lam ('x', Id 'x')
              , Lam ('f', Lam ('y', Id 'y'))
              )
            )

let () = print_endline (whnf_to_string test)
(* Outputs - Γ  ⊢ λ f.λ y.y *)
