#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;
exception X_missing;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val macro_expand : sexpr -> sexpr
  val somesome : sexpr -> sexpr list
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let somesome expr = 
  match expr with
 | ScmPair (ScmSymbol("cond"),ribs) -> scm_list_to_list ribs

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 
(* Implement tag parsing here *)

(*const*)
| ScmNil -> ScmConst ScmNil (* it should be with or without the const* *)
| ScmSymbol (str) -> if List.mem str reserved_word_list then raise (X_syntax_error(sexpr, "Sexpr structure not recognized")) else ScmVar(str)
| ScmBoolean(flag) -> ScmConst(sexpr)
| ScmNumber (num) -> ScmConst (sexpr) 
| ScmChar (ch) -> ScmConst (sexpr)
| ScmString (s) -> ScmConst(sexpr)
| ScmVector(v) -> ScmConst(sexpr)
| ScmVoid -> ScmConst(ScmVoid)


(*quotes*)
| ScmPair(ScmSymbol("quote"), ScmPair(a, ScmNil)) -> ScmConst(a)


(*if*)
| ScmPair(ScmSymbol("if"),ScmPair(test,ScmPair(dit,ScmNil)))-> ScmIf(tag_parse_expression test,tag_parse_expression dit,ScmConst(ScmVoid))
| ScmPair(ScmSymbol("if"),ScmPair(test,ScmPair(dit,ScmPair(dif,ScmNil))))-> ScmIf(tag_parse_expression test,tag_parse_expression dit,tag_parse_expression dif)

(*or*)
| ScmPair(ScmSymbol ("or"), ScmNil) ->  ScmConst(ScmBoolean (false))
| ScmPair (ScmSymbol ("or"), ScmPair(expr,ScmNil))->  tag_parse_expression expr
| ScmPair (ScmSymbol ("or"), preds)-> ScmOr (macro_or preds)


(*lambdas*)

 | ScmPair (ScmSymbol("lambda"),ScmPair(ScmSymbol(a), ScmPair(b,c)))-> if List.mem a reserved_word_list
  then raise (X_syntax_error(sexpr, "No symbols good. english bad"))
    else ScmLambdaOpt([],a,do_ScmSeq (ScmPair(b,c)))

    
  (*with arguments*)
| ScmPair (ScmSymbol("lambda"),ScmPair(args, ScmPair(a,b)))-> if is_implict_pair args
    then ScmLambdaOpt(make_string_list args, get_last_ele args, do_ScmSeq (ScmPair(a,b)))
      else ScmLambdaSimple(make_string_list args, do_ScmSeq(ScmPair(a,b)))



(*define
 ScmPair(ScmSymbol("define"),ScmPair(ScmSymbol(x),ScmPair(_,Nil)))   *)
| ScmPair(ScmSymbol("define"),ScmPair(ScmSymbol(x),ScmPair(a,ScmNil))) -> ScmDef(tag_parse_expression(ScmSymbol(x)), tag_parse_expression(a))

(*set!*)
|ScmPair(ScmSymbol("set!"),ScmPair(ScmSymbol(x), ScmPair (value, ScmNil)))-> ScmSet(tag_parse_expression (ScmSymbol(x)),tag_parse_expression(value))

(*SimSeq*)
| ScmPair(ScmSymbol("begin"),ScmPair(a,b))->do_ScmSeq (ScmPair(a,b))



(*Application*)
| ScmPair(ScmSymbol(x),ScmNil)->ScmApplic(tag_parse_expression (ScmSymbol(x)),[])
| ScmPair(ScmSymbol(x),ls)->ScmApplic(tag_parse_expression(ScmSymbol(x)), make_exp_list ls)
| ScmPair(x,ScmNil) -> ScmApplic((tag_parse_expression x), [])
| ScmPair(x,ls)-> ScmApplic((tag_parse_expression x), (List.map (tag_parse_expression) (scm_list_to_list ls)))


and do_ScmSeq body = 
match body with
| ScmNil->raise (X_syntax_error(body,"IM NOT RUNNING!"))
| ScmPair(ScmNil,_)->raise (X_syntax_error(body,"IM NOT RUNNING!"))
| ScmPair(a,ScmNil) -> tag_parse_expression a
| ScmPair(a,b)-> ScmSeq(make_exp_list (ScmPair(a,b)))


and macro_or sexpr = 
match sexpr with
| ScmPair(expr,ScmNil)-> [tag_parse_expression(expr)] 
| ScmPair(first,rest)-> ([tag_parse_expression(first)]@(macro_or(rest)))
(*return true is last element is not nil, flase otherwise*)
and is_implict_pair imp = 
match imp with
| ScmPair(_,ScmNil)-> false
| ScmPair(_,ScmPair(a,b))->is_implict_pair(ScmPair(a,b))
| ScmPair(_,_) -> true
| ScmNil -> false
and make_string_list ls = 
match ls with
| ScmNil -> [](*raise (X_syntax_error(ls, "again, why are you running??"))ls should never be nil since we check if in pair (a,b) b is nil) *)
| ScmPair(ScmNil,ScmNil) ->[]
| ScmPair(ScmSymbol(a),ScmNil)-> if List.mem a reserved_word_list then raise (X_syntax_error(ls, "Sexpr structure not recognized")) else [a]
| ScmPair(ScmSymbol(a),ScmSymbol(b)) -> if List.mem a reserved_word_list then raise (X_syntax_error(ls, "Sexpr structure not recognized")) else [a]
| ScmPair(ScmSymbol(a),rest) -> if List.mem a reserved_word_list then raise (X_syntax_error(ls, "Sexpr structure not recognized")) else ([a]@(make_string_list rest))

(*return last elemnt in ls/pair*)
and get_last_ele ele = 
match ele with
| ScmPair(_,ScmNil)-> raise (X_syntax_error(ele, "why are you running here?"))
| ScmPair(_,ScmPair(a,b))->get_last_ele(ScmPair(a,b))
| ScmPair(_,ScmSymbol(a)) -> if List.mem a reserved_word_list then raise (X_syntax_error(ele, "Sexpr structure not recognized")) else a

and make_exp_list ls = 
match ls with
| ScmNil->[]
| ScmPair(a,ScmNil) -> [tag_parse_expression a]
| ScmPair(a,b) -> [tag_parse_expression a]@(make_exp_list b)

and macro_expand sexpr =
let rec build_qq expr = 
  match expr with
  | ScmVector(lst) -> ScmPair(ScmSymbol("list->vector"),list_to_proper_list [build_qq (list_to_proper_list lst)])
  | ScmNil -> ScmPair(ScmSymbol("quote"), ScmPair(ScmNil,ScmNil))
  | ScmSymbol(sym) -> ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol(sym),ScmNil))
  | ScmPair(ScmSymbol("unquote"), ScmPair(ex, ScmNil)) -> ex
  | ScmPair(ScmSymbol("unquote-splicing"), ScmPair(ex, ScmNil)) -> 
          ScmPair(ScmSymbol("quote"),ScmPair(ScmPair(ScmSymbol("unquote-splicing"),ScmPair(ex,ScmNil)),ScmNil))
  | ScmPair(ScmPair(ScmSymbol("unquote-splicing"), ScmPair(ex,ScmNil)),x) -> ScmPair(ScmSymbol("append"),ScmPair(ex,ScmPair(build_qq x,ScmNil)))
  | ScmPair(x,y) -> ScmPair(ScmSymbol("cons"),ScmPair(build_qq x,ScmPair(build_qq y, ScmNil)))
  | ex -> ex
in match sexpr with
(* Handle macro expansion patterns here *)

(*QQ*)

| ScmPair (ScmSymbol("quasiquote"), ScmPair(ex, ScmNil)) -> build_qq ex



(*MIT_DEF*)
| ScmPair(ScmSymbol("define"),ScmPair(ScmPair(ScmSymbol(id), args),body))-> ScmPair(ScmSymbol("define"),ScmPair(ScmSymbol(id),ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(args,body)),ScmNil)))


(*and*)
| ScmPair(ScmSymbol("and"),ScmPair(ScmNil,ScmNil))-> ScmBoolean(true)
| ScmPair(ScmSymbol("and"),ScmPair(cond,ScmNil))-> cond
| ScmPair(ScmSymbol("and"),ScmPair(ScmNil,cond))-> cond
| ScmPair(ScmSymbol("and"),ScmPair(cond,condls))-> ScmPair(ScmSymbol("if"),ScmPair(macro_expand cond,ScmPair(macro_expand (make_andls_to_if condls), ScmPair(ScmBoolean(false),ScmNil))))


(*cond*)
| ScmPair(ScmSymbol("cond"), ScmPair(ScmPair(ScmSymbol("else"),dit),_)) -> ScmPair(ScmSymbol("begin"), dit)
| ScmPair(ScmSymbol("cond"), ScmPair(ScmPair(test, ScmPair(ScmSymbol("=>"), exprs)),rest)) -> build_arrow_cond test exprs rest


| ScmPair(ScmSymbol("cond"),ScmPair(ScmPair(test,dit),ScmNil))->
      ScmPair(ScmSymbol "if", ScmPair(test,ScmPair(ScmPair(ScmSymbol("begin"),dit),ScmNil)))

| ScmPair(ScmSymbol("cond"),ScmPair(ScmPair(test,dit),dif))-> 
    ScmPair(ScmSymbol("if"), ScmPair(test,ScmPair(ScmPair(ScmSymbol("begin"),dit),ScmPair(macro_expand(ScmPair(ScmSymbol("cond"),dif)),ScmNil))))


(*let*)
| ScmPair(ScmSymbol("let"),ScmPair(args,body))-> build_let args body 0
| ScmPair(ScmSymbol("let*"), ScmPair(ScmNil,body))->  build_let (ScmPair(ScmNil,ScmNil)) body 0
| ScmPair(ScmSymbol("let*"),ScmPair(args,body))-> let_kohvit args body
| ScmPair(ScmSymbol("letrec"), ScmPair(ScmNil,body))->  build_let (ScmPair(ScmNil,ScmNil)) body 0
| ScmPair(ScmSymbol("letrec"),ScmPair(args,body))-> build_let args body 1



| _ -> sexpr



and build_let args body is_rec = 
  match is_rec with
  | 0 -> ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(build_args_for_let args, body)),get_values_from_args args)
  | 1 -> 
          let temp_args = build_args_for_let args in
          let temp_vals = get_values_from_args args in
          let new_args = build_qq_whatever temp_args in
          let new_body = build_new_body_for_letrec temp_args temp_vals body in
          build_let new_args new_body 0


and build_qq_whatever args = 
match args with
| ScmPair(arg,ScmNil)-> ScmPair(ScmPair(arg, ScmPair(ScmPair(ScmSymbol("quote"),ScmPair(ScmSymbol("whatever"),ScmNil)),ScmNil)),ScmNil)
| ScmPair(arg,arg2) -> ScmPair(ScmPair(arg, ScmPair(ScmPair(ScmSymbol("quote"),ScmPair(ScmSymbol("whatever"),ScmNil)),ScmNil)),build_qq_whatever arg2)

and build_new_body_for_letrec args vals body =
let temp = build_set_letrec args vals in
scm_append temp body

and build_set_letrec args vals = 
match args, vals with
| (ScmPair(arg,ScmNil)), (ScmPair(q,ScmNil)) -> ScmPair(ScmPair(ScmSymbol("set!"),ScmPair(arg,ScmPair(q,ScmNil))),ScmNil)
| ScmPair(arg,arg2), ScmPair(q,val2) ->ScmPair(ScmPair(ScmSymbol("set!"),ScmPair(arg,ScmPair(q,ScmNil))), build_set_letrec arg2 val2)

and build_arrow_cond test exprs rest = 
let value = ScmPair(ScmSymbol("value"),ScmPair(test,ScmNil)) in
match rest with
| ScmNil-> 
          let f = ScmPair(ScmSymbol("f"),ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,ScmPair(exprs,ScmNil))),ScmNil)) in
          let body = ScmPair(ScmSymbol("if"),ScmPair(ScmSymbol("value"),ScmPair(ScmPair(ScmSymbol("f"),ScmPair(ScmSymbol("value"),ScmNil)),ScmNil))) in
          build_let (ScmPair(value,ScmPair(f,ScmNil))) (list_to_proper_list [body]) 0
| _-> 
          let f = ScmPair(ScmSymbol("f"),ScmPair(ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, exprs)),ScmNil)) in
          let new_rest = ScmPair(ScmSymbol("rest"),ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,ScmPair(macro_expand (ScmPair(ScmSymbol("cond"),rest)),ScmNil))),ScmNil)) in      
          let body = ScmPair(ScmSymbol("if"),ScmPair(ScmSymbol("value"),ScmPair(ScmPair(ScmPair(ScmSymbol("f"),ScmNil),ScmPair(ScmSymbol("value"),ScmNil)),ScmPair(ScmPair(ScmSymbol("rest"),ScmNil),ScmNil)))) in          
          build_let (ScmPair(value,ScmPair(f,ScmPair(new_rest,ScmNil)))) (list_to_proper_list [body]) 0

and let_kohvit args body = 
match args with
| ScmNil -> build_let args body 0
| ScmPair(arg,ScmNil)-> build_let args body 0
| ScmPair(arg,nxt)-> build_let (ScmPair(arg,ScmNil)) (list_to_proper_list [let_kohvit nxt body]) 0


and make_andls_to_if ls = 
match ls with
| ScmNil-> ScmVoid (*Should not happen*)
| ScmPair(ScmNil,_)-> ScmVoid (*Should no happen*)
| ScmPair(cond,ScmPair(ScmNil,_))-> ScmVoid (*Should no happen*)
| ScmPair(cond, ScmPair(dit,ScmNil))->ScmPair(ScmSymbol("if"),ScmPair(cond,ScmPair(dit,ScmPair(ScmBoolean(false),ScmNil))))
| ScmPair(cond, ScmPair(condls, nxt)) -> ScmPair(ScmSymbol("if"),ScmPair(cond,ScmPair(make_andls_to_if (ScmPair(condls, nxt)), ScmPair(ScmBoolean(false), ScmNil))))
| ScmPair(cond,ScmNil) -> cond
and build_args_for_let args =
match args with
| ScmPair(ScmNil,ScmNil)->args
| ScmPair(ScmPair(arg,_),ScmNil)->ScmPair(arg,ScmNil)
| ScmPair(ScmPair(arg,_),arg2)-> ScmPair(arg,build_args_for_let arg2)
| _ -> ScmPair(ScmNil, ScmNil)
and get_values_from_args args = 
match args with
| ScmPair(ScmNil,ScmNil)-> ScmNil
| ScmPair(ScmPair(_,ScmPair(vel,ScmNil)),ScmNil)->ScmPair(vel,ScmNil)
| ScmPair(ScmPair(_,ScmPair(vel,ScmNil)),nxt)->ScmPair(vel, get_values_from_args nxt)
| _ -> ScmNil
and ends_with_nil ls =
match ls with
| ScmNil -> raise (X_syntax_error(ls,"should not be nil"))
| ScmPair(ScmNil,_)-> raise (X_syntax_error(ls,"unexpcted nil"))
| ScmPair(_,ScmNil)->true
| ScmPair(_,ScmPair(a,b)) -> ends_with_nil (ScmPair(a,b))
| ScmPair(_,_) -> false
 
end;; 
