(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing
open System.Collections.Generic
open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

let rec apply_subst (s : subst) (t : ty) : ty =
    match t with
        | TyName _ -> t
        | TyArrow (t1, t2) -> TyArrow (apply_subst s t1, apply_subst s t2)
        | TyVar tv ->
            try
                let _, t1 = List.find(fun (tv1, _) -> tv1 = tv) s
                t1
            with :? KeyNotFoundException -> t

        |TyTuple ts -> TyTuple (List.map (apply_subst s) ts)
// I am adding
let apply_subst_scheme (s : subst) (Forall (tvs, t)) : scheme =
    let s' = Set.toList(Set.ofList(s) - Set.ofList(List.filter(fun (tv, _) -> Set.contains tv tvs) s)) // lists dont have set-minus
    Forall(tvs, apply_subst s' t)

let apply_subst_env_scheme (s : subst) (env : scheme env) : scheme env =
    List.map (fun (x, sch) -> (x, apply_subst_scheme s sch)) env

let compose_subst (s1: subst) (s2: subst) : subst =
    let s2' = List.map (fun (v, t) -> (v, apply_subst s1 t)) s2
    s2' @ s1

let ($) = compose_subst

let rec circularity (tv: tyvar) (t: ty) : bool =
    match t with
        | TyName s         -> false
        | TyArrow (t1, t2) -> circularity tv t1 || circularity tv t2
        | TyVar v          -> v = tv
        | TyTuple ts       -> List.length (List.filter (fun t -> circularity tv t) ts) > 0

let rec unify (t1 : ty) (t2 : ty) : subst =
    match (t1, t2) with
        | TyName s1, TyName s2 when s1=s2 -> []
        | TyVar tv, t
        | t, TyVar tv -> if circularity tv t then unexpected_error "the tuning prize's owener is mad at you: circularity"
                         else [tv, t] // added by me
        | TyArrow (t1, t2), TyArrow(t3,t4) -> (unify t1 t3) $ (unify t2 t4)
        | TyTuple ts1, TyTuple ts2 when List.length ts1 = List.length ts2 ->
            List.fold(fun s (t1, t2) -> s $ (unify t1 t2)) [] (List.zip ts1 ts2)
        | _ -> type_error "cannot unify %O and %O" t1 t2
// I am adding

let rec freevars_ty t =
    match t with
        | TyName s -> Set.empty
        | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
        | TyVar tv -> Set.singleton tv
        | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts


let freevars_scheme (Forall (tvs, t)) = freevars_ty t - tvs


let freevars_scheme_env env =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env

let FreshVar =
    let counter = ref 0
    fun () -> incr counter; TyVar !counter

let rec re (tvs: tyvar Set) (t: ty) : ty =
    match t with
        | TyName c -> TyName c // | _ -> t
        | TyVar tv -> if Set.contains tv tvs then FreshVar() else TyVar tv
        | TyArrow (t1, t2) -> TyArrow (re tvs t1, re tvs t2)
        | TyTuple ts -> TyTuple (List.map (re tvs) ts) // (List.map (fun x -> re tvs x) ts) 
         
let instantiate (Forall (tvs, t)) : ty = re tvs t

let gen (env: scheme env) (t: ty) : scheme =
    Forall (freevars_ty t - freevars_scheme_env env, t)

// basic environment: add builtin operators at will
//

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("*", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("/", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("<", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
]
let gamma1 = [
    ("+", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))) )
    ("-", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))) )
    ("*", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))) )
    ("/", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))) )
    ("<", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))) )
]

// type inference
//

let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, []
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []

    | Var x -> 
        let sch = lookup env x
        instantiate(sch), []

    | Lambda (x, tyo, e) -> 
        let tv = FreshVar ()
        let env' = (x, Forall (Set.empty, tv)) :: env 
        let t2, s1 = typeinfer_expr env' e
        
        let t1 = apply_subst s1 tv
        let out = TyArrow (t1, t2), s1
        match tyo with
            | Some t -> if t1 <> t then type_error "type mismatch %O and %O" t1 t else out
            | None   -> out

    | App (e1, e2) -> 
        let tv = FreshVar ()
        let t1, s1 = typeinfer_expr env e1

        let t2, s2 = typeinfer_expr  (apply_subst_env_scheme s1 env) e2

        let s3 = unify (t1) (TyArrow (t2, tv))
    
        apply_subst s3 tv, s3 $ s2

    | IfThenElse (e1, e2, Some e3) -> 
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify t1 TyBool
        let s3 = s2 $ s1
        let t2, s4 = typeinfer_expr (apply_subst_env_scheme s3 env) e2
        let s5 = s4 $ s3
        let t3, s6 = typeinfer_expr (apply_subst_env_scheme s5 env) e3
        let s7 = s6 $ s5
        let s8 = unify (apply_subst s7 t2) (apply_subst s7 t3)
        apply_subst s8 t2, s8 $ s7

    | Let (x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        //match t1 with
        //    | TyArrow (_, _) -> unexpected_error "%O is a lambda. Use let Rec" e1
        //    | _ ->
        let sch = gen (apply_subst_env_scheme s1 env) t1
        let t2, s2 = typeinfer_expr ((x, sch) :: apply_subst_env_scheme s1 env) e2
        let out = t2, s2 $ s1
        match tyo with
            | Some t -> if t1 <> t then type_error "type mismatch %O and %O" t1 t else out
            | None   -> out


    | LetRec (x, tyo, e1, e2) ->
        let tv = FreshVar()
        let t1, s1 = typeinfer_expr ((x, Forall (Set.empty, tv)) :: env) e1
        match t1 with
            | TyArrow (_, _) ->
                    let env1 = apply_subst_env_scheme s1 env
                    
                    let scheme1 = gen env1 t1
                    let t2, s2 = typeinfer_expr ((x, scheme1) :: env1) e2
                    let s3 = unify tv (apply_subst s1 t1)
                    let out = t2, s3 $ s2 $ s1
                    match tyo with
                        | Some t -> if t1 <> t then type_error "type mismatch %O and %O" t1 t else out
                        | None   -> out
            | _ -> unexpected_error "%O is not a lambda. Use let" e1


    | BinOp (e1, ("+" | "-" | "*" | "/" as op), e2) -> 
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify t1 TyInt
        
        let s3 = s2 $ s1
        let t2, s4 = typeinfer_expr (apply_subst_env_scheme s3 env) e2 // wrong in slides
        let s5 = unify t2 TyInt
        TyInt, s5 $ s4 $ s3 // omitted in slides


    | UnOp ("not", e) ->
        let t, s1 = typeinfer_expr env e
        let s2 = unify t TyBool
        TyBool, s2 $ s1
        
    | BinOp (e1, "=", e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let s3 = unify t1 t2
        TyBool, s3 $ s2 $ s1

    | BinOp (e1, ("<" | ">" | "<=" | ">=" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify t1 TyInt
        let s3 = s2 $ s1
        let t2, s4 = typeinfer_expr (apply_subst_env_scheme s3 env) e2 // wrong in slides
        let s5 = unify t2 TyInt
        TyBool, s5 $ s4 $ s3 // omitted in slides


    | Tuple es -> 
        let ts, subs = List.unzip (List.map (typeinfer_expr env) es)
        let subs_all = List.fold compose_subst [] subs
        TyTuple (List.map (apply_subst subs_all) ts), subs_all

    
    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e


// type checker
//

let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x -> lookup env x

    | Let (x, None, e1, e2) ->
        let t1 = typecheck_expr env e1
        let env' = (x, t1) :: env
        typecheck_expr env' e2

    | Let (x, Some t, e1, e2) ->
        let t1 = typecheck_expr env e1
        if t <> t1 then type_error "type %O differs from type %O in let-binding" t1 t
        let env' = (x, t1) :: env
        typecheck_expr env' e2

    | Lambda (x, Some t, e) ->
        let env' = (x, t) :: env
        let te = typecheck_expr env' e
        TyArrow (t, te)

    | Lambda (x, None, e) ->
        type_error "unannotated lambdas are not supported by the type checker"

    // I am adding
    | LetRec (x, Some t, e1, e2) -> // prof's clarification. t must be arrow typed
        let env' = (x, t) :: env
        let arrow = typecheck_expr env e1
        if arrow = t then typecheck_expr env e2
        else type_error "type mismatch between %O and %O" arrow t

    | LetRec (x, None, e1, e2) -> // this is a like a loop. We are using f inside e1, so 'typecheck_expr env e1' leads to a loop
        type_error "e1 must be annotated"
    // I am adding
    

    | App (e1, e2) ->
        let t2 = typecheck_expr env e2
        match typecheck_expr env e1 with
        | TyArrow (ta, tb) -> 
            if ta <> t2 then type_error "argument has type %O while function parameter has type %O in application" t2 ta
            tb
        | t1 -> type_error "left hand of application is not an arrow type: %O" t1

    | IfThenElse (e1, e2, Some e3) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "bool expected in if guard, but got %O" t1
        let t2 = typecheck_expr env e2
        let t3 = typecheck_expr env e3
        if t2 <> t3 then type_error "then and else branches have different types: %O and %O" t2 t3
        t2

    | BinOp (e1, ("+" | "-" | "*" | "/" as op), e2) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyInt then type_error "left hand of (%s) operator is not an int: %O" op t1
        let t2 = typecheck_expr env e2
        if t2 <> TyInt then type_error "right hand of (%s) operator is not an int: %O" op t2
        TyInt

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "operand of not-operator is not a bool: %O" t
        TyBool
        
    | BinOp (e1, "=", e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        if t1 <> t2 then type_error "left and right hands of equality operator are different: %O and %O" t1 t2
        TyBool

    | BinOp (e1, ("<" | ">" | "<=" | ">=" as op), e2) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyInt then type_error "left hand of (%s) operator is not an int: %O" op t1
        let t2 = typecheck_expr env e2
        if t2 <> TyInt then type_error "right hand of (%s) operator is not an int: %O" op t2
        TyBool

    | Tuple es -> TyTuple (List.map (typecheck_expr env) es)


    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
