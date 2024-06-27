(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

// evaluator
//


let rec eval_expr (venv : value env) (e : expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Lambda (x, _, e) -> Closure (venv, x, e)

    | App (e1, e2) -> 
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        match e1 with
            | Var s ->
                    match v1 with
                        | RecClosure (venv', f, x, e) ->
                            let venv' = (x, v2) :: (f, v1) :: venv'
                            eval_expr venv' e
                        | Closure (venv', x, e) ->
                            let venv' = (x, v2) :: venv'
                            eval_expr venv' e
                        | _ -> unexpected_error "non-recClosure on left hand of application"
            | Lambda (_, _, _) ->
                    match v1 with
                        | Closure (venv', x, e) ->
                            let venv' = (x, v2) :: venv'
                            eval_expr venv' e

                        | _ -> unexpected_error "non-closure on left hand of application"

            | _ -> unexpected_error "e1 must be an arrow typed"


    | Var x -> lookup venv x

    // I am adding
    | Let (x, tyo, e1, e2) -> // can be checkec
        let v1 = eval_expr venv e1
        let venv' = (x, v1) :: venv
        let v2 = eval_expr venv' e2
        v2

    | LetRec (x, tyo, e1, e2) -> // can be checkec
        
        match e1 with
            | Lambda (x', _, e) ->
                let v1 = RecClosure(venv, x, x', e)
                let venv' = (x, v1) :: venv
                eval_expr venv' e2
            | App (_, _) ->
                let partial_app = eval_expr venv e1
                match partial_app with
                    | Closure(venv, x', e) ->
                        let venv' = (x, partial_app) :: venv
                        eval_expr venv' e2
                    | _ -> unexpected_error "result of partial app must be a closure"
                


                //let v1 = RecClosure(venv, x, x', e)
                //let venv' = (x, v1) :: venv
                //eval_expr venv' e2
            | _ -> unexpected_error "e1 must be a lambda abstraction"
        

    | IfThenElse (e1, e2, Some e3) ->
        match e1 with
        | Lit (LBool true) -> eval_expr venv e2
        | _ -> eval_expr venv e3 

    | BinOp (e1, ("+" | "-" | "*" | "/" as op), e2) -> 
        let v1 = eval_expr venv e1 //type:value
        let v2 = eval_expr venv e2 //type:value
        value.Basic_Ops(v1, op, v2)
        
    | UnOp ("not", e) ->
        let v = eval_expr venv e //type:value
        value.not v
        
    | BinOp (e1, "=", e2) ->
        let v1 = eval_expr venv e1 //type:value
        let v2 = eval_expr venv e2 //type:value
        v1 == v2

    | BinOp (e1, ("<" | ">" | "<=" | ">=" as op), e2) ->
        let v1 = eval_expr venv e1 //type:value
        let v2 = eval_expr venv e2 //type:value
        value.Basic_Comps(v1, op, v2)

    | Tuple es -> VTuple (List.map (eval_expr venv) es)
    // I am adding

    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
