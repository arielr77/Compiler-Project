
#use "semantic-analyser.ml";;

exception X_lama of sexpr * string;;
exception X_this_should_not_happen;;
exception X_List_Of_Sexpr of sexpr list;;
exception X_Print_Expr of expr' * string;;
exception X_reserved_word of string;;
exception X_Print_String of string * string * bool * string;;
exception X_list_size_are_not_equal;;
exception X_proper_list_error;;
exception X_not_implemented;;
exception X_missing_1;;
exception X_missing_2;;
exception X_missing_3;;
exception X_missing_4;;
exception X_missing_5;;
exception X_unvalid_input;;
exception X_Check_Ctbl of (sexpr * (int * string)) list;;
(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants res is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_res address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars res is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_res address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars ress, you will have to update
     this signature to match: The first argument is the constants res type, the second 
     argument is the fvars res type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
   let lcounter_else = ref 0;;
   let lext_counter = ref 0;;
   let lgeneric_counter = ref 0;;
   let lcode_counter = ref 0;;
   let lloop = ref 0;;
   let lApplic_cont_counter = ref 0;;
   let llsloop = ref 0;;
   let loptloop = ref 0;;
   let inc_global_counter p = p := !p+1
  

(**CONST TABLE START**)
let size sexp =
  match sexp with
  | ScmVoid -> 1
  | ScmNil -> 1
  | ScmBoolean(false)-> 2
  | ScmBoolean(true) -> 2
  | ScmNumber(ScmRational(_,_)) -> 17
  | ScmNumber(ScmReal(_)) -> 9
  | ScmChar(x) -> 2
  | ScmString(s) -> 9+(String.length s)
  | ScmSymbol(x) -> 9
  | ScmPair(e,es) -> 17
  | ScmVector(ls) -> if List.length ls = 0 then 1 else  9 + 8*(List.length ls)

let rec remove_dup res lst =
    match lst with
    | [] -> res  
    | e::es -> if (List.mem e res) then remove_dup res es else remove_dup (res@[e]) es

let rec get_offset sexpr lst=
    match lst with
    | [] -> raise X_this_should_not_happen
    | (sexpr2,(offset,_))::rest -> if sexpr_eq sexpr sexpr2 then offset else get_offset sexpr rest

let rec get_consts asts =
  match asts with
  | ScmConst'(const)-> [const]
  | ScmBoxSet'(_, e) -> get_consts e
  | ScmIf'(test,dit,dif) -> (get_consts test)@(get_consts dit)@(get_consts dif)
  | ScmSet'(_, ex) | ScmDef'(_, ex) -> get_consts ex
  | ScmSeq'(ls) | ScmOr'(ls) -> List.flatten (List.map get_consts ls)
  | ScmLambdaSimple'(_, body) | ScmLambdaOpt'(_, _, body) -> get_consts body
  | ScmApplic'(op, ls) | ScmApplicTP'(op, ls) -> List.flatten (List.map get_consts ([op]@ls))
  | _ -> []

let rec handle_unique sexpr =
      match sexpr with
        | ScmSymbol(s) -> [ScmString (s)]@[sexpr]
        | ScmPair(car,cdr) -> (handle_unique car)@(handle_unique cdr)@[car]@[cdr]@[sexpr]
        | ScmVector(ls) -> (List.flatten (List.map (fun s -> handle_unique s) ls))@[sexpr]
        | _ -> [sexpr]

let assemble_consts asts =
  let ls_1 = List.flatten (List.map get_consts asts) in
  let ls_2 =  List.flatten (List.map(fun x-> handle_unique x) ([ScmVoid; ScmNil; ScmBoolean(false); ScmBoolean(true)]@ls_1)) in
  remove_dup [] ls_2

let make_tuple c_tbl sexpr offset =
    match sexpr with
    | ScmVoid -> (sexpr, (offset, "MAKE_VOID"))
    | ScmNil -> (sexpr, (offset, "MAKE_NIL"))
    | ScmBoolean(false) ->(sexpr, (offset, "MAKE_BOOL(0)"))
    | ScmBoolean(true) ->(sexpr, (offset, "MAKE_BOOL(1)"))
    | ScmNumber(ScmReal(f)) -> (sexpr, (offset, "MAKE_LITERAL_REAL("^(string_of_float(f))^")"))
    | ScmNumber(ScmRational(num,dem)) -> (sexpr, (offset,"MAKE_LITERAL_RATIONAL("^(string_of_int(num))^","^(string_of_int(dem))^")"))
    | ScmChar(c) ->  (sexpr, (offset, "MAKE_LITERAL_CHAR("^(string_of_int(int_of_char c))^")"))
    | ScmString(s) -> (sexpr, (offset, "MAKE_LITERAL_STRING  \""^s^"\""))
    | ScmSymbol(_) | ScmPair(_,_) | ScmVector(_) -> (sexpr, (offset, "MISSING_TXT_LITERAL")) 

let rec create_tuples c_tbl res offset =
  match c_tbl with
  | [] -> res
  | sexpr:: rest -> create_tuples rest (res@[make_tuple c_tbl sexpr offset]) (offset + size sexpr)


let rec build_string_for_vector v ls res = 
  match v with
  | [] -> res
  | hd::tl -> build_string_for_vector tl ls res^", const_tbl+" ^  string_of_int (get_offset hd ls)

let rec make_string_for_vector v res =
  if (List.length v = 0)
  then "MAKE_LITERAL_VECTOR"
  else(
  let temp = List.hd v in
  let tl = List.rev (List.tl v) in
  let hd = "const_tbl+" ^ string_of_int (get_offset temp res) in
  let offset_list = build_string_for_vector tl res "" in 
    "MAKE_LITERAL_VECTOR " ^ hd ^ offset_list)

let rec fix_unique sexpr c_tbl =
  match sexpr with
    | (ScmSymbol(s),(offset,"MISSING_TXT_LITERAL")) -> (ScmSymbol(s),(offset, "MAKE_LITERAL_SYMBOL(const_tbl+"^string_of_int (get_offset (ScmString(s)) c_tbl)^")"))
    | (ScmPair(car,cdr),(offset,"MISSING_TXT_LITERAL")) -> (ScmPair(car,cdr),(offset, "MAKE_LITERAL_PAIR(const_tbl+"^string_of_int (get_offset car c_tbl)^", const_tbl+"^string_of_int (get_offset cdr c_tbl)^")"))
    | (ScmVector(ls),(offset,"MISSING_TXT_LITERAL")) -> (ScmVector(ls),(offset, make_string_for_vector ls c_tbl))
    | _ -> sexpr

    
(***************END CONST***********************)

(***********FV TABLE START**********)

let init_fvars = [
  (* Type queries  *)
  "boolean?"; "flonum?"; "rational?";
  "pair?"; "null?"; "char?"; "string?";
  "procedure?"; "symbol?";
  (* String procedures *)
  "string-length"; "string-ref"; "string-set!";
  "make-string"; "symbol->string";
  (* Type conversions *)
  "char->integer"; "integer->char"; "exact->inexact";
  (* Identity test *)
  "eq?";
  (* Arithmetic ops *)
  "+"; "*"; "/"; "="; "<";
  (* Additional rational numebr ops *)
  "numerator"; "denominator"; "gcd";
  (* List ops *)
  "car"; "cdr"; "cons"; "set-car!"; "set-cdr!"; "apply"
] 
let rec make_fvr_tbl_offset fv_tbl offset res =
  match fv_tbl with
  | [] -> res
  | first :: rest -> make_fvr_tbl_offset rest (offset+1) (res@[(first,offset)])

let rec collect_varfrees expr =
    match expr with
    | ScmVar'(VarFree(v))-> [v]
    | ScmIf'(test,dit,dif) -> (collect_varfrees test) @ (collect_varfrees dit) @ (collect_varfrees dif)
    | ScmSeq'(ls) | ScmOr'(ls) -> List.flatten (List.map collect_varfrees ls)
    | ScmSet'(v, e) | ScmDef'(v, e) -> (collect_varfrees (ScmVar'(v)))@(collect_varfrees e)
    | ScmLambdaSimple'(_, body) | ScmLambdaOpt'(_, _, body) -> collect_varfrees body
    | ScmApplic'(op, exp_list) | ScmApplicTP'(op, exp_list) -> List.flatten (List.map collect_varfrees ([op] @ exp_list))
    | _ -> []

  let rec find_fvar_offset var fv_tbl = 
      match fv_tbl with 
        | [] -> "WHY ARE YOU HERE????? NO GOOD. GO BACK"
        | (v,offset)::rest -> if v = var then string_of_int offset else find_fvar_offset var rest

  (*********************FVAR TABL END********************)

  (********************GEN START********************)
      
  let generate_if c_tbl fv_tbl test dit dif env_depth = 
            let else_label = "Else_If_label_"^(string_of_int (!lcounter_else)) in
            let _ = (inc_global_counter lcounter_else) in
            let exit_label = "Exit_If_label_"^(string_of_int (!lext_counter)) in
            let _ = (inc_global_counter lext_counter) in

";    gen if\n;   gen test for if\n"^test^"
mov r12, SOB_TRUE_ADDRESS
cmp rax, r12
jne "^else_label^"\n;   gen dit for if\n"
^dit^
"\njmp "^exit_label^"\n"
^else_label^":\n;    gen dif for if\n"
^dif^"\n"^
exit_label^":
mov r12, 0
;   finish generate if\n"


      let generate_box c_tbl fv_tbl var env_depth = 
var^"\n;   gen box
MALLOC rbx, 8
mov qword[rbx], rax
mov rax, rbx
;    end gen box\n"
     
     
      let generate_box_get c_tbl fv_tbl var env_depth = 
var^"\n;   gen box Get
mov rax, qword [rax]
;    end gen box Get\n"
     
      let generate_box_set c_tbl fv_tbl var ex env_depth = 
"\n;   gen box set\n"
^ex^"\npush rax\n" 
^var^"\npop qword [rax]
mov r12, SOB_VOID_ADDRESS    
mov rax, r12
mov r12, 0
;    end gen box set\n"  
      
      
    let generate_def c_tbl fv_tbl fv ex env_depth = 
";    gen def\n"
^ex^"\nmov r12, SOB_VOID_ADDRESS
mov [fvar_tbl+" ^(find_fvar_offset fv fv_tbl)^ "*8], rax ; insert var to free var table
mov rax, r12 ; define return void
mov r12, 0
;   end gen def\n"

let rec gen_env i ed s =
  let e1 = string_of_int (i*8) in
  let e2 = string_of_int (8*(i+1)) in
  if( i < ed) then
gen_env (i+1) ed (s ^"\nmov r9, "^e1^"
add rbx, r9                      
mov qword rdx, [rbx]
sub rbx, r9
mov r9, "^e2^"
add rax, r9
mov qword [rax], rdx
sub rax, r9\n" )
  else
    s^"\npush rax\n" 

let rec generate_helper c_tbl fv_tbl exp env_depth =
  match exp with
    | ScmConst'(const) -> let const_offset = string_of_int(get_offset const c_tbl) in 
"\n;    gen const\nmov rax, const_tbl +"^const_offset^ "; const --> rax"
    | ScmVar'(VarFree(v)) -> 
"\n;    gen VarFree
mov rax, qword [fvar_tbl + 8*"^(find_fvar_offset v fv_tbl)^"]"
    | ScmVar'(VarParam(_,minor)) -> let min = string_of_int minor in
"\n;    gen VarParam
mov r12, "^min^"
add r12, 4
shl r12, 3
add rbp, r12
mov rax, qword [rbp]
sub rbp, r12\n"

    | ScmVar'(VarBound(_,major, minor)) -> let min = string_of_int minor in
                                            let maj = string_of_int major in
"\n;    gen VarBound
mov r12, 16
add rbp, r12
mov rax, qword [rbp]
sub rbp, r12
mov rax, qword[rax +8*"^maj^ "]
mov rax, qword[rax +8*" ^min^ "]"

    | ScmSet'(VarFree(v), ex) -> let varGen = generate_helper c_tbl fv_tbl ex env_depth in
varGen^
"\n;   gen set for VarFree
mov r12, SOB_VOID_ADDRESS
mov qword [fvar_tbl + 8*" ^(find_fvar_offset v fv_tbl)^"], rax
mov rax, r12
mov r12, 0\n"

    | ScmSet'(VarParam(_,minor), ex) -> let min = string_of_int minor in
                                          let exS = generate_helper c_tbl fv_tbl ex env_depth in
exS^"\n;    gen set for VarParam
mov r12, "^min^"
add r12, 4
shl r12, 3
add rbp, r12
mov qword [rbp], rax
sub rbp, r12
mov r12, SOB_VOID_ADDRESS
mov rax, r12
mov r12,0\n"

    | ScmSet'(VarBound(_,major,minor), ex) -> let maj = string_of_int major in
                                            let min = string_of_int minor in
                                            let exS = generate_helper c_tbl fv_tbl ex env_depth in
exS^"\n;    gen set gor VarBound
mov r12, 16
add rbp, r12
mov rbx, qword [rbp]
mov rbx, qword [8*"^maj^"+rbx]
mov qword[8*"^min^"+rbx], rax
sub rbp, r12
mov r12, SOB_VOID_ADDRESS
mov rax r12
mov r12, 0\n"    
    | ScmIf'(test, dit, dif) -> let newtest = generate_helper c_tbl fv_tbl test env_depth in
                                let newdit = generate_helper c_tbl fv_tbl dit env_depth in
                                let newdif = generate_helper c_tbl fv_tbl dif env_depth in 
                                  generate_if c_tbl fv_tbl newtest newdit newdif env_depth                          
    | ScmBox'(v) -> let varS = generate_helper c_tbl fv_tbl (ScmVar'(v)) env_depth in
                                 generate_box c_tbl fv_tbl varS env_depth
    | ScmBoxGet'(v) -> let varS = generate_helper c_tbl fv_tbl (ScmVar'(v)) env_depth in
                                    generate_box_get c_tbl fv_tbl varS env_depth
    | ScmBoxSet'(v,ex) -> let varS = generate_helper c_tbl fv_tbl (ScmVar'(v)) env_depth in
                          let exS = generate_helper c_tbl fv_tbl ex env_depth in
                                    generate_box_set c_tbl fv_tbl varS exS env_depth
    | ScmDef'(VarFree(v), ex) -> let exS = generate_helper c_tbl fv_tbl ex env_depth in
                                    generate_def c_tbl fv_tbl v exS env_depth
    | ScmSeq'(ls) -> (List.fold_left (fun s acc -> s^(generate_helper c_tbl fv_tbl acc env_depth)^"\n") "" ls)
    | ScmOr'(ls) ->  let _ = (inc_global_counter lext_counter) in
                      let label = "Exit_label_Or_"^(string_of_int (!lext_counter)) in
                      "\n;    gen or\n"^(generate_or c_tbl fv_tbl ls "" env_depth label)^"\n;   end gen or\n"

                    
    | ScmApplic'(op, ls) -> let _ = (inc_global_counter lext_counter) in
                      let _ = (inc_global_counter lApplic_cont_counter) in
                (generate_applic c_tbl fv_tbl op ls env_depth)
    | ScmApplicTP'(op, ls) -> let _ = (inc_global_counter lext_counter) in 
                    let _ = (inc_global_counter lApplic_cont_counter) in
                  (generate_applic_tp c_tbl fv_tbl op ls env_depth)
    | ScmLambdaSimple'(args, body) -> let _ = (inc_global_counter lcode_counter) in
                                      let _ =  (inc_global_counter lgeneric_counter) in 
                                      let _= (inc_global_counter llsloop) in
                                      (generate_lambda_simple c_tbl fv_tbl args body env_depth)
    | ScmLambdaOpt'(args, _, body) -> let _ = (inc_global_counter lcode_counter) in
                                          let _ =  (inc_global_counter lgeneric_counter) in 
                                          let _ = (inc_global_counter loptloop) in
                                        (generate_lambda_opt c_tbl fv_tbl args body env_depth)
    | _ -> raise (X_this_should_not_happen)


    and generate_applic c_tbl fv_tbl op ls env_depth =
            let temp_ls = (List.map (fun e -> (generate_helper c_tbl fv_tbl e env_depth)^"\npush rax\n") ls) in
            let ls_length = string_of_int (List.length temp_ls) in
            let gen_ls =  String.concat "\n" (List.rev temp_ls) in
            let gen_op = generate_helper c_tbl fv_tbl op env_depth in
            let label_exit = "Exit_applic_"^ (string_of_int !lext_counter) in
            let _ = (inc_global_counter lext_counter) in
            let label_cont = "Cont_applic_" ^ (string_of_int !lApplic_cont_counter) in
            let applic_pop_label = "Applic_pop_args_label_" ^(string_of_int !lext_counter) in
            let _ = (inc_global_counter lApplic_cont_counter) in
            
";    gen applic:\n"
^make_applic_intro ls_length gen_ls gen_op label_cont label_exit^
"\npush rsi 
CLOSURE_CODE rsi, rax
call rsi
add rsp, 8 ; curr env
pop r12 ; arg size   
add r12, 1 ; move magic  
shl r12, 3 
mov rbx, r12
cmp r12, 0
je "^label_exit^"\n"
^applic_pop_label^":
      add rsp, 8
      sub r12, 8
      cmp r12, 0
      jne "^applic_pop_label^"\n"
^label_exit^":
mov r12, 0
;   end applic\n"

    and generate_applic_tp c_tbl fv_tbl op ls env_depth =
            let label_exit = "Exit_applic_"^ (string_of_int !lext_counter) in
            let loop_label = "Loop_ApplicTP_"^(string_of_int !lloop) in
            let change_label = "Change_TP_"^(string_of_int !lloop) in
            let label_cont = "Cont_applic_" ^ (string_of_int !lApplic_cont_counter) in
            let _ = (inc_global_counter lApplic_cont_counter) in
            let _ = (inc_global_counter lext_counter) in
            let _ = (inc_global_counter lloop) in
            let _ = (inc_global_counter lloop) in
            let temp_ls = (List.map (fun e -> (generate_helper c_tbl fv_tbl e env_depth)^"\npush rax\n") ls) in
            let gen_ls = String.concat "\n" (List.rev temp_ls) in
            let gen_op = generate_helper c_tbl fv_tbl op env_depth in
            let ls_length = string_of_int (List.length temp_ls) in
";    gen applicTP:\n"
^make_applic_intro ls_length gen_ls gen_op label_cont label_exit^
"\n\tmov r12, 8
  add rbp, r12
  push rsi
  push qword [rbp]  ; save last return address
  sub rbp, r12

; shift frame of stack. rax shold point closure
push qword[rbp]
mov rsi, rax
mov r12, 24
add r12, rbp  ; inc pointer to env
mov r8, [r12]  ; arg size
add r8, 4 
shl r8, 3
add r8, rbp
mov rax, r8    
mov rcx, rbp              
mov r12, 8
sub rcx, r12 ; rcx address first available stack address\n"
^loop_label ^ ":
cmp rsp, rcx            
jg " ^ change_label ^ "
mov rbx, [rcx]
mov [rax], rbx
sub rcx, r12
sub rax, r12
jmp " ^ loop_label ^ "\n" ^
change_label ^ ":   ; end of the newly created stack
mov rsp, rax
add rsp, 8
pop rbp
;   finish fixing the stack

CLOSURE_CODE rsi, rsi ; save the new env and calls code
jmp rsi\n"^
label_exit^":
mov r12, 0
;   end applic TP"


  and make_applic_intro size ls op label1 label2= 
"mov r12, SOB_NIL_ADDRESS
push r12 ;      push magic to stack
;   now we will push the ls/args follow by total number of args\n"
^ls^"
push "^size^ ";    push number of rands to stack
;   now we will gen the operator or function\n"
^op^"
mov r12, rax
mov rsi, rax
mov bl, byte [rsi]
cmp bl, T_CLOSURE         ; check if rax is clouser
je "^label1^ "
jmp "^label2^"\n"
^label1^":
  CLOSURE_ENV rsi, rax      ; get env from closure\n"

  and generate_lambda_simple c_tbl fv_tbl args body env_depth =
    let simple_loop_label = "Loop_Label_LSimple_"^(string_of_int (!llsloop)) in
    let simple_loop_end = "Loop_End_Label_Simple_"^(string_of_int (!llsloop)) in
    let _ = (inc_global_counter llsloop) in
    let cont_label = "Cont_Label_End_Simple_"^(string_of_int (!lgeneric_counter)) in
    let _ = (inc_global_counter lgeneric_counter) in
    let code_label = "Code_Label_LSimple_"^(string_of_int (!lcode_counter)) in
    let _ = (inc_global_counter lcode_counter) in
    let mallocsize = string_of_int (8* (env_depth+1)) in
    let body_2 = generate_helper c_tbl fv_tbl body (env_depth+1) in
    let intro = make_intro_lambda mallocsize env_depth simple_loop_end simple_loop_label code_label cont_label in
intro^"\n"^body_2^"\nleave
ret\n"
^cont_label^":
; resets used registers
mov r13, 0
mov r12, 0
mov r9, 0
;   end lambda simple\n"

    and generate_lambda_opt c_tbl fv_tbl args body env_depth =
        let arg_len = (List.length args) in
        let mallocsize = string_of_int (8* (env_depth+1)) in
        let opt_loop_label = "Loop_Label_LOPT_"^(string_of_int (!loptloop)) in
        let opt_loop_end = "Loop_End_Label_LOPT_"^(string_of_int (!loptloop)) in
        let cont_label = "Opt_Cont_END_Label_"^(string_of_int (!lgeneric_counter)) in
        let code_label = "Code_Label_LOpt_"^(string_of_int (!lcode_counter)) in
        let _ = (inc_global_counter lgeneric_counter) in
        let _ = (inc_global_counter lext_counter) in
        let _ = (inc_global_counter llsloop) in
        let intro = make_intro_lambda mallocsize env_depth opt_loop_end opt_loop_label code_label cont_label in
        let body_2 = (generate_helper c_tbl fv_tbl body (env_depth+1)) in
intro^"\n\tmov r9, rdx
  mov r11, rcx
  mov r14, rbx
  mov r15, rax
  mov rdx, SOB_NIL_ADDRESS
  mov r12, 3
  shl r12, 3
  add rbp, r12
  mov rax, [rbp]
  ;   rax should have total number of args
  mov rbx, "^(string_of_int(arg_len))^"
  sub rbp, r12
  HANDLE_OPT
  mov r12, 4
  add r12, "^string_of_int arg_len^"
  shl r12, 3
  add rbp, r12 
  mov qword [rbp], rdx
  sub rbp, r12
  ;   return original values to main registers
  mov rdx, r9
  mov rcx, r11
  mov rbx, r14
  mov rax, r15\n"
^body_2^
"\nleave
ret\n"
^cont_label^":
;   rests used registers
mov r13, 0
mov r12, 0
mov r15, 0
mov r14, 0
mov r11, 0
mov r9, 0\n"

  and make_intro_lambda mallocsize ed label1 label2 label3 label4 =       
    "\n; generate lambda
MALLOC rax, "^mallocsize^"\npush rbx
push rdx
;   pushing args and 
mov r12, 16
add rbp, r12
mov qword rbx, [rbp] ; get curr env" 
^(gen_env 0 ed "\n")^"
sub r12, 8
add rbp, r12
;   getting args of previous func
mov rcx, [rbp]
mov r12, rcx
shl r12, 3
lea rax, [r12]
;   load relvent env
mov r12, 24
sub rbp, r12
; return back to rel env
MALLOC rax, rax
mov r12, rcx
cmp r12, 0
je "^label1^"
mov r9, 0
mov r13, 32\n"
^label2^":
mov r10, [rbp + r13]
mov [rax + r9], r10
add r9, 8
add r13, 8
sub r12, 1
cmp r12, 0
jne "^label2^"\n"
^label1^":
  mov rdx, rax
  pop rax
  mov qword [rax], rdx
  pop rdx 
  pop rbx
  push r8
  mov r8, rax
  MAKE_CLOSURE (rax , r8, "^label3^")
  pop r8
  jmp "^label4^"\n"
^label3^":

  push rbp
  mov rbp, rsp\n"       
  
  and generate_or c_tbl fv_tbl lst res env_depth exit_label = 
    match lst with
    | [first] -> res^(generate_helper c_tbl fv_tbl first env_depth)^"\n"^exit_label^":\n"
    | first::rest -> let s = "\nmov r12, SOB_TRUE_ADDRESS\ncmp rax, r12\nje "^exit_label^"\nmov r12, 0\n" in
                              generate_or c_tbl fv_tbl rest (res^(generate_helper c_tbl fv_tbl first env_depth)^s) env_depth exit_label
    | [] -> raise (X_this_should_not_happen)

    
    (***************END GEN****************8*)                                                            
  
  let make_consts_tbl asts = let temp = create_tuples (assemble_consts asts) [] 0  in
                                  List.map (fun x-> fix_unique x temp) temp;;
  let make_fvars_tbl asts = let temp  = List.flatten(List.map (fun x-> collect_varfrees x) asts) in
    make_fvr_tbl_offset (remove_dup [] (init_fvars@temp)) 0 [];;
  let generate const_tbl fvar_tbl e = 
    generate_helper const_tbl fvar_tbl e 0;;
end;;