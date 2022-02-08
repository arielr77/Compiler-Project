(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
exception X_why_are_you_running;;
exception X_why_are_you_running_1;;
exception X_why_are_you_running_2;;
exception X_why_are_you_running_3;;
exception X_why_are_you_running_4;;
exception X_why_are_you_running_5;;
exception X_check_names of string*string;;



type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;

  exception X_syntax_error_tester of expr*expr'*expr';;

  let var_eq v1 v2 =
    match v1, v2 with
      | VarFree (name1), VarFree (name2) -> String.equal name1 name2
      | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
        major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
      | VarParam (name1, index1), VarParam (name2, index2) ->
           index1 = index2 && (String.equal name1 name2)
      | _ -> false
    
    let list_eq eq l1 l2 = (List.length l1) = (List.length l2) && List.for_all2 eq l1 l2;;
    
    let rec expr'_eq e1 e2 =
      match e1, e2 with
      | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
      | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
      | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                                (expr'_eq dit1 dit2) &&
                                                  (expr'_eq dif1 dif2)
      | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
            list_eq expr'_eq exprs1 exprs2
      | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
            (var_eq var1 var2) && (expr'_eq val1 val2)
      | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
         (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
      | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
         (String.equal var1 var2) &&
           (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
      | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
         (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
      | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
          (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
      | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
      | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
      | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
      | _ -> false;;
    
    let unannotate_lexical_address = function
    | (VarFree name | VarParam (name, _) | VarBound (name, _, _)) -> ScmVar name
    
    let rec unanalyze expr' =
    match expr' with
      | ScmConst' s -> ScmConst(s)
      | ScmVar' var -> unannotate_lexical_address var
      | ScmBox' var -> ScmApplic(ScmVar "box", [unannotate_lexical_address var])
      | ScmBoxGet' var -> unannotate_lexical_address var
      | ScmBoxSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
      | ScmIf' (test, dit, dif) -> ScmIf (unanalyze test, unanalyze dit, unanalyze dif)
      | ScmSeq' expr's -> ScmSeq (List.map unanalyze expr's)
      | ScmSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
      | ScmDef' (var, expr') -> ScmDef (unannotate_lexical_address var, unanalyze expr')
      | ScmOr' expr's -> ScmOr (List.map unanalyze expr's)
      | ScmLambdaSimple' (params, expr') ->
            ScmLambdaSimple (params, unanalyze expr')
      | ScmLambdaOpt'(params, param, expr') ->
            ScmLambdaOpt (params, param, unanalyze expr')
      | (ScmApplic' (expr', expr's) | ScmApplicTP' (expr', expr's)) ->
            ScmApplic (unanalyze expr', List.map unanalyze expr's);;
    
    let string_of_expr' expr' =
        string_of_expr (unanalyze expr');;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
  val test_eq: int -> bool
  val final_test: expr -> (string * (expr' list * expr' list)) list

end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
      match pe with
      | ScmConst ScmNil -> ScmConst' ScmNil
      | ScmConst(x) -> ScmConst'(x)

      | ScmIf(test,dit,dif) -> ScmIf'(run test params env,run dit params env, run dif params env)

      | ScmOr(ls) -> ScmOr'(List.map (fun s -> run s params env) ls)     (*ls is at least of size 2*)

      | ScmLambdaSimple(args,body)-> ScmLambdaSimple'(args,(run body args ([params]@env))) (*In this case body -> ScmSeq(ls)*)

      | ScmLambdaOpt(args,x,body) -> ScmLambdaOpt'(args,x, (run body (args@[x]) ([params]@env)))


      | ScmDef(ScmVar(var),body) -> ScmDef'((tag_lexical_address_for_var var params env), (run body params env))      (*var is always of type ScmVar(x)*)
      | ScmSet(ScmVar(var),value) -> ScmSet'((tag_lexical_address_for_var var params env), (run value params env))
      | ScmSeq(ls) -> ScmSeq'(List.map (fun s -> run s params env) ls)   (*ls is of size 2 at least*)

      | ScmApplic(expr, ls) -> ScmApplic'((run expr params env), (List.map (fun s->run s params env) ls)) 
      | ScmVar(x) -> ScmVar'(tag_lexical_address_for_var x params env)  
   in 
   run pe [] [];;

  
  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;(*s is not a list*)




  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail =
    match pe with
    | ScmApplic'(a,b)-> if in_tail then ScmApplicTP'(run a false, List.map (fun s-> run s false) b) else ScmApplic'(run a false, List.map (fun s-> run s false) b)

    | ScmLambdaSimple'(args, ScmSeq'(ls)) -> 
        let (rdc,rac) =  rdc_rac ls   
        in ScmLambdaSimple'(args,ScmSeq'((List.map (fun s-> run s false) rdc)@[run rac true]))(*Doesnt matter if true\false upon arrival. should be correct to all lambda calls*)
    | ScmLambdaSimple'(args, body) -> ScmLambdaSimple'(args,run body true)

    | ScmLambdaOpt'(args,arg,ScmSeq'(ls)) -> 
        let (rdc,rac) =  rdc_rac ls
        in ScmLambdaOpt'(args,arg,ScmSeq'((List.map (fun s-> run s false) rdc)@[run rac true]))
    | ScmLambdaOpt'(args,arg,body)-> ScmLambdaOpt'(args,arg, run body true)

    | ScmIf'(test,dit,dif) -> if in_tail then ScmIf'(run test false,run dit true, run dif true) else ScmIf'(run test false,run dit false, run dif false)

    | ScmOr'(ls)-> if in_tail 
                    then (let (rdc,rac) = rdc_rac ls
                         in ScmOr'((List.map (fun s -> run s false) rdc)@[run rac true])) 
                    else ScmOr'(List.map (fun s -> run s false) ls)

    | ScmSeq'(ls) -> if in_tail 
                      then (let (rdc,rac) =  rdc_rac ls
                      in ScmSeq'((List.map (fun s -> run s false)rdc)@[run rac true]))
                      else ScmSeq'((List.map (fun s -> run s false)) ls)
    | ScmSet'(var,pexpr)-> if in_tail then ScmSet'(var, run pexpr false) else ScmSet'(var, run pexpr false)
    | ScmDef'(var,pexpr)-> if in_tail then ScmDef'(var, run pexpr false) else ScmDef'(var, run pexpr false)
    | _ -> pe  
   in 
   run pe false;;


(*run this third*)
  let rec check_for_get_box name expr res curr_scope = 
    let rec get_from_ls name ls curr_scope res=
      match ls with 
      | [] -> raise X_this_should_not_happen
      | [ele] -> check_for_get_box name ele res curr_scope 
      | ele::eles -> (get_from_ls name eles curr_scope (check_for_get_box name ele res curr_scope))
      (*strat check_for_get_box*)
    in match expr with
    | ScmLambdaSimple'(args,body)-> if List.mem name args then res else check_for_get_box name body res expr
    | ScmLambdaOpt'(args,arg,body)-> if String.equal name arg then res else (if List.mem name args then res else check_for_get_box name body res expr)
    | ScmSet'(_,ex) -> check_for_get_box name ex res curr_scope
    | ScmBoxSet'(_,ex)-> check_for_get_box name ex res curr_scope
    | ScmApplic'(ex,ls)-> (get_from_ls name ([ex]@ls) curr_scope res)
    | ScmApplicTP'(ex,ls)-> get_from_ls name ([ex]@ls) curr_scope res
    | ScmSeq'(ls)-> get_from_ls name ls curr_scope res
    | ScmOr'(ls) -> get_from_ls name ls curr_scope res
    | ScmIf'(test,dit,dif)-> get_from_ls name [test;dit;dif] curr_scope res
    | ScmVar'(VarParam(x,minor))-> if String.equal x name 
                                      then (match res with
                                            | ((-1,-1),_) -> ((-1,minor),[curr_scope])
                                            | ((a,b),ls) -> ((a,b),ls@[curr_scope])
                                            ) else res
    | ScmVar'(VarBound(x,minor,major))-> if String.equal x name 
                                            then (match res with
                                                  | ((-1,-1),_) -> ((minor,major),[curr_scope])
                                                  | ((-1,b),ls) -> ((minor,b),ls@[curr_scope])
                                                  | ((a,b),ls) -> ((a,b),ls@[curr_scope])
                                                  ) else res
    | _ -> res



  let rec check_for_set_box name expr res curr_scope =
    let rec set_from_ls name ls curr_scope res=
      match ls with 
      | [] -> raise X_this_should_not_happen
      | [ele] -> check_for_set_box name ele res curr_scope 
      | ele::eles -> (set_from_ls name eles curr_scope (check_for_set_box name ele res curr_scope))
      (*start check_for_set_box*)
    in match expr with
    | ScmLambdaSimple'(args,body)-> if List.mem name args then res else check_for_set_box name body res expr
    | ScmLambdaOpt'(args,arg,body)-> if String.equal name arg then res else (if List.mem name args then res else check_for_set_box name body res expr)
    | ScmSet'(VarBound(x,minor,major),ex) ->  if String.equal x name then (
                                                  match res with
                                                  | ((-1,-1),_)-> check_for_set_box name ex ((minor,major),[curr_scope]) curr_scope
                                                  | ((-1,b),ls) -> check_for_set_box name ex ((minor,b),ls@[curr_scope]) curr_scope
                                                  | ((a,b),ls) ->  check_for_set_box name ex ((a,b),ls@[curr_scope]) curr_scope 
                                              ) else check_for_set_box name ex res curr_scope
    | ScmSet'(VarParam(x,minor),ex)->if String.equal x name then (
                                      match res with
                                      | ((-1,-1),_)-> check_for_set_box name ex ((-1,minor),[curr_scope]) curr_scope
                                      | ((a,b),ls) ->  check_for_set_box name ex ((a,b),ls@[curr_scope]) curr_scope 
                                  ) else check_for_set_box name ex res curr_scope       
    | ScmApplic'(ex,ls)-> set_from_ls name ([ex]@ls) curr_scope res
    | ScmApplicTP'(ex,ls)-> set_from_ls name ([ex]@ls) curr_scope res
    | ScmSeq'(ls)-> set_from_ls name ls curr_scope res
    | ScmOr'(ls) -> set_from_ls name ls curr_scope res
    | ScmIf'(test,dit,dif)-> set_from_ls name [test;dit;dif] curr_scope res
    | ScmBoxSet'(_,ex) -> check_for_set_box name ex res curr_scope
    | ScmSet'(_,ex)-> check_for_set_box name ex res curr_scope
    | _ -> res


  let rec box_set expr  = 
        (** expr'*)
        let rec foo args expr curr_scope = 
          let rec build_seq ls name minor major build = 
            match ls with
            | [] -> raise X_why_are_you_running
            | [ele] -> build@[ScmSet'(VarParam(name, major), ScmBox'(VarParam(name,major)));ele]
            | ele::eles->
                match ele with
                | ScmSet'(VarParam(_, _), ScmBox'(VarParam(_,_)))->build_seq eles name minor major (build@[ele])
                | ex-> build@[ScmSet'(VarParam(name,major), ScmBox'(VarParam(name,major)))]@ls
          in let rec check_ele_with_list ele ls = 
          match ls with
          | []-> true
          | [x]-> if expr'_eq ele x then true else false
          | x::rest-> if expr'_eq ele x then true else check_ele_with_list ele rest 
    
          in let rec check_lists ls1 ls2 = 
          match ls1 with 
          | []-> true
          | [ele]-> if check_ele_with_list ele ls2 then false else true
          | ele::eles ->if check_ele_with_list ele ls2 then check_lists eles ls2 else true
    
          in let rec should_box name expr curr_scope = 
             let ((get_minor,get_major),get_ls) =  (check_for_get_box name expr ((-1,-1),[]) curr_scope)
            in let ((set_minor,set_major), set_ls) = (check_for_set_box name expr ((-1,-1),[]) curr_scope) 
            in if (get_major = set_major) && (get_major <> -1) && (set_major <> -1)  then (
              match get_ls with
              | []-> ((-1,-1),[[];[]])
              | ls1-> 
                      (match set_ls with
                      | []-> ((-1,-1),[[];[]])
                      | ls2-> if check_lists get_ls set_ls then (
                        match get_minor with
                        | -1 -> ((set_minor,get_major), [get_ls;set_ls])
                        | a-> ((a,get_major), [get_ls;set_ls])
                      ) else ((-1,-1),[[];[]]))) else ((-1,-1),[[];[]])
          in let rec make_box name minor major expr r_ls w_ls curr_scope= 
          match expr with
          | ScmSet'(VarParam(x,a),ex) -> (match ex with
                                        | ScmBox'(x) -> expr
                                        | _ -> if String.equal name x && major = a && (check_ele_with_list curr_scope w_ls) then ScmBoxSet'(VarParam(x,a), make_box name minor major ex r_ls w_ls curr_scope) 
                                                        else ScmSet'(VarParam(x,a),make_box name minor major ex r_ls w_ls curr_scope)) 
          | ScmSet'(VarBound(x,a,b),ex) -> if String.equal name x  && major = b && (check_ele_with_list curr_scope w_ls) then ScmBoxSet'(VarBound(x,a,b), make_box name minor major ex r_ls w_ls curr_scope)  
                                                        else ScmSet'(VarBound(x,a,b),make_box name minor major ex r_ls w_ls curr_scope) 
          | ScmVar'(VarParam(x,a)) -> if String.equal x name && a = major && (check_ele_with_list curr_scope r_ls) then ScmBoxGet'(VarParam(x,a)) else expr
          | ScmVar'(VarBound(x,a,b))-> if String.equal name x && major = b && (check_ele_with_list curr_scope r_ls) then ScmBoxGet'(VarBound(x,a,b)) else expr
          | ScmBoxSet'(a,ex)->ScmBoxSet'(a,make_box name minor major ex r_ls w_ls curr_scope)
          | ScmApplic'(ex,ls)-> ScmApplic'(make_box name minor major ex r_ls w_ls curr_scope, List.map (fun s-> make_box name minor major s r_ls w_ls curr_scope) ls)
          | ScmApplicTP'(ex,ls)-> ScmApplicTP'(make_box name minor major ex r_ls w_ls curr_scope, List.map (fun s-> make_box name minor major s r_ls w_ls curr_scope) ls)
          | ScmOr'(ls)->ScmOr'(List.map (fun s-> make_box name minor major s r_ls w_ls curr_scope) ls)
          | ScmIf'(test,dit,dif)-> ScmIf'(make_box name minor major test r_ls w_ls curr_scope, make_box name minor major dit r_ls w_ls curr_scope, make_box name minor major dif r_ls w_ls curr_scope)
          | ScmSeq'(ls) ->  ScmSeq'((List.map (fun s-> make_box name minor major s r_ls w_ls curr_scope) ls ))
          | ScmLambdaSimple'(args,body)-> ScmLambdaSimple'(args, make_box name minor major body r_ls w_ls expr)
          | ScmLambdaOpt'(args,arg,body) -> ScmLambdaOpt'(args,arg,(make_box name minor major body r_ls w_ls expr))
          | ScmSet'(a,ex) ->  ScmSet'(a, make_box name minor major ex r_ls w_ls curr_scope)
          | _ -> expr
          (**start foo*)
         in match args with
          | [] -> box_set expr
          | [arg]->
                let ((minor,major),ls) =  should_box arg expr curr_scope
                in if minor = -1 && major = -1 then (
                        match ls with
                        | [[];[]]-> box_set expr 
                        | [_;[]]-> box_set expr
                        | [[];_]-> box_set expr           
                        | ls2 -> raise X_why_are_you_running)
                   else( 
                     match ls with 
                     | [[];[]]-> raise X_why_are_you_running
                     | [_;[]]-> raise X_why_are_you_running
                     | [[];_]-> raise X_why_are_you_running   
                     | [ls1;ls2] -> 
                              match expr with
                              | ScmSeq' ls3 -> (match ls3 with 
                                                | ScmSet'(VarParam(_,_),ScmBox'(_))::rest ->box_set (make_box arg minor major (ScmSeq'(build_seq ls3 arg minor major [])) ls1 ls2 curr_scope)
                                                | _-> ScmSeq'([ScmSet'(VarParam(arg,major),ScmBox'(VarParam(arg,major))); box_set (make_box arg minor major expr ls1 ls2 curr_scope)])         
                                                )
                              | ex-> ScmSeq'([ScmSet'(VarParam(arg, major), ScmBox'(VarParam(arg,major))); box_set (make_box arg minor major expr ls1 ls2 curr_scope)])
                   )
          | arg::marg -> 
                let ((minor,major),ls) =  should_box arg expr curr_scope
                in if minor = -1 && major = -1 then(
                  match ls with 
                  | [[];[]] -> foo marg expr curr_scope
                  | [_;[]] -> foo marg expr curr_scope
                  | [[];_] -> foo marg expr curr_scope
                  | ls2-> raise X_why_are_you_running
                  ) else (
                     match ls with
                    | [[];[]] -> raise X_why_are_you_running
                    | [[];_] -> raise X_why_are_you_running
                    | [_;[]] -> raise X_why_are_you_running
                    | [ls1;ls2]-> 
                            match expr with
                            | ScmSeq'(ls3)->(match ls3 with
                                             | ScmSet'(VarParam(_,_),ScmBox'(_))::rest ->foo marg (box_set (make_box arg minor major (ScmSeq'(build_seq ls3 arg minor major [])) ls1 ls2 curr_scope)) curr_scope
                                             | _-> foo marg (ScmSeq'([ScmSet'(VarParam(arg,major),ScmBox'(VarParam(arg,major))); box_set (make_box arg minor major expr ls1 ls2 curr_scope)])) curr_scope
                              )
                            | ex->  foo marg (ScmSeq'([ScmSet'(VarParam(arg, major), ScmBox'(VarParam(arg,major))); make_box arg minor major expr ls1 ls2 curr_scope])) curr_scope)
 (*start box_set*)
    in match expr with 
    | ScmLambdaSimple'(args,ScmLambdaSimple'(a,b))-> ScmLambdaSimple'(args,(box_set (ScmLambdaSimple'(a,b))))
    | ScmLambdaOpt'(args,arg,ScmLambdaSimple'(a,b)) -> ScmLambdaOpt'(args,arg,(box_set (ScmLambdaSimple'(a,b))))
    | ScmLambdaSimple'(args,ScmLambdaOpt'(a,b,c))-> ScmLambdaSimple'(args,(box_set (ScmLambdaOpt'(a,b,c))))
    | ScmLambdaOpt'(args,arg,ScmLambdaOpt'(a,b,c)) -> ScmLambdaOpt'(args,arg,(box_set (ScmLambdaOpt'(a,b,c))))
    | ScmLambdaSimple'(args,body)->  ScmLambdaSimple'(args, foo args body expr)
    | ScmLambdaOpt'(args,arg,body)-> ScmLambdaOpt'(args,arg, foo (args@[arg]) body expr)
    | ScmIf'(test,dit,dif)-> ScmIf'(box_set test, box_set dit, box_set dif)
    | ScmDef'(var,ex)-> ScmDef'(var, box_set ex)
    | ScmOr'(ls)->ScmOr'(List.map (fun s-> box_set s) ls)
    | ScmSeq'(ls)-> ScmSeq'(List.map (fun s-> box_set s) ls)
    | ScmApplic'(ex,ls)-> ScmApplic'(box_set ex, List.map (fun s-> box_set s) ls)
    | ScmApplicTP'(ex,ls)->ScmApplicTP'(box_set ex, List.map (fun s-> box_set s) ls)
    | _ -> expr
             

    let run_semantics expr =
        box_set(
        (annotate_tail_calls
           (annotate_lexical_addresses expr)))
  



    let rec get_ls expr =
      match expr with
      | ScmLambdaSimple'(args,body)-> (
        match args with 
        | [arg] -> let ((a,b),ls1) = check_for_get_box arg body ((-1,-1),[]) expr in
                  let ((c,d),ls2) = check_for_set_box arg body ((-1,-1),[]) expr in
                  [(arg,(ls1,ls2))]
        | arg::margs ->let ((a,b),ls1) = check_for_get_box arg body ((-1,-1),[]) expr in
                        let ((c,d),ls2) = check_for_set_box arg body ((-1,-1),[]) expr in
                        [(arg,(ls1,ls2))]@ (get_ls (ScmLambdaSimple'(margs,body)))
      )  

      let final_test expr = 
        get_ls(
          (annotate_tail_calls
             (annotate_lexical_addresses expr)))

    let test_eq e =
      (* let str = "(lambda (x) 
      (list 
        (lambda () 
          (lambda ()
            (lambda () x)))
        (lambda () 
          (lambda ()
            (lambda ()
              (set! x #t))))))" in
      let temp = (Reader.nt_sexpr str 0).found in
      let temp2 = Tag_Parser.tag_parse_expression (temp) in *)
      let temp2 = ScmDef (ScmVar "test", ScmLambdaSimple (["x"],  ScmApplic   (ScmLambdaSimple (["y"],     ScmApplic (ScmVar "cons",      [ScmLambdaSimple ([], ScmVar "x");       ScmApplic (ScmVar "cons", [ScmSet (ScmVar "x", ScmVar "y"); ScmConst (ScmNil)])])),   [ScmConst (ScmNumber (ScmRational(52,1)))]))) in
      let eq1 = run_semantics(temp2) in
      let eq2 = ScmDef'  (VarFree "test", ScmLambdaSimple'  (["x"],  ScmApplicTP'    (ScmLambdaSimple'  (["y"],     ScmApplicTP'  (ScmVar'  (VarFree "cons"),      [ScmLambdaSimple'  ([], ScmVar'  (VarBound ("x", 1, 0)));       ScmApplic'  (ScmVar'  (VarFree "cons"),        [ScmSet'  (VarBound ("x", 0, 0), ScmVar'  (VarParam ("y", 0)));         ScmConst'  (ScmNil)])])),   [ScmConst'  (ScmNumber (ScmRational(52,1)))]))) in
          if expr'_eq eq1 eq2 then true else raise (X_syntax_error_tester(temp2,eq1,eq2))
  end;; (* end of module Semantic_Analysis *)
