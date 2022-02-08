(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

 #use "pc.ml";;
              

 let rec gcd a b =
   match (a, b) with
   | (0, b) -> b
   | (a, 0) -> a
   | (a, b) -> gcd b (a mod b);;
 
 type scm_number =
   | ScmRational of (int * int)
   | ScmReal of float;;
 
 type sexpr =
   | ScmVoid
   | ScmNil
   | ScmBoolean of bool
   | ScmChar of char
   | ScmString of string
   | ScmSymbol of string
   | ScmNumber of scm_number
   | ScmVector of (sexpr list)
   | ScmPair of (sexpr * sexpr);;
 
 
 let rec evaluate lst str = 
       match lst with 
       | [] -> (match str with
               | "" -> ScmNil
               | _ -> ScmPair(ScmString(str),ScmNil))
       | (hd::tl)-> (match hd with 
                   | ScmChar(x) -> evaluate tl (str^(Char.escaped x))
                   | ScmPair(x)-> (match str with 
                                  | "" -> ScmPair(ScmPair(x),(evaluate tl str))
                                  | _ -> ScmPair(ScmString(str),ScmPair(ScmPair(x), evaluate tl "")))
                   | _ -> ScmNil)
   ;;
               
 
 
 module type READER = sig
     val nt_sexpr : sexpr PC.parser
 end;; (* end of READER signature *)
 
 module Reader : READER = struct 
 open PC;;
 
 let unitify nt = pack nt (fun _ -> ());;
 
 let rec nt_whitespace str =
   const (fun ch -> ch <= ' ') str
 and nt_end_of_line_or_file str =
   let nt1 = unitify nt_end_of_input in
   let nt2 = unitify (char '\n') in
   let nt3 = disj nt1 nt2 in
   nt3 str
 
 and nt_line_comment str =
   let nt1 = const (fun ch -> ch != '\n') in
   let nt1 = star nt1 in
   let nt2 = (char ';') in
   let nt1 = unitify (caten nt2 nt1) in
   nt1 str
 
 and nt_paired_comment str =
   let nt1 = char '{' in
   let nt2 = star nt_sexpr in
   let nt3 = char '}' in
   let ntpaierd= caten nt1(caten nt2 nt3) in 
   let ntpaierd = unitify ntpaierd  in
   ntpaierd str
 
 and nt_sexpr_comment str =
   let nt1 = word "#;" in
   let nt2= caten nt1 nt_sexpr in
   let nt2 = unitify nt2 in 
   nt2 str
 
 and nt_comment str =
 let nt1 = disj nt_line_comment nt_paired_comment in 
 let nt1 = disj  nt1 nt_sexpr_comment in 
 nt1 str
 
 and nt_skip_star str =
   let nt1 = (unitify nt_whitespace) in 
   let nt1 = disj nt1 nt_comment in
   let nt1 =star nt1 in
   let nt1 = unitify nt1 in 
   nt1 str
 
 and make_skipped_star (nt : 'a parser) =
   let nt1 = caten nt nt_skip_star in 
   let nt1 = caten nt_skip_star nt1 in
   let nt1 = pack nt1 (fun (_, (ex, _)) -> ex) in
   nt1
 and nt_natural str =
   (plus (range '0' '9') )str
 and nt_int str =
   let nt1 = char '-' in
   let nt2 = char '+' in
   let nt1 =  (disj nt1 nt2) in
   let nt1 = maybe nt1 in 
   let nt1 = caten nt1 nt_natural in
   let nt1 = pack nt1 (fun p -> match p with
     |(Some('-'),tl) -> '-'::tl
     |(_,tl) -> tl) in
   let nt1 = pack nt1 (fun lst -> int_of_string (list_to_string lst)) in
   nt1 str 
 
 and nt_frac str = 
   let nt1 = char '/' in 
   let nt1 = caten nt_int nt1  in
   let nt2 = pack nt_natural (fun lst -> int_of_string(list_to_string lst)) in 
   let nt1 = caten nt1 nt2 in 
   let nt3 = pack nt1 (fun ((a,b),c)-> match ((a,b),c) with
   |((_,_),0)-> raise X_no_match
   |((n,_),d)-> (n,d)) in
   let nt1 = pack nt3 (fun (a,b)-> 
     ScmRational((a/(gcd a b)),(b/(gcd a b)))) in 
   nt1 str 
 
 and nt_integer_part str = 
   let nt1 = pack nt_natural (fun list -> list_to_string list) in
   nt1 str
 
 and nt_mantissa str = 
   let ntmantisa = pack nt_natural (fun list -> list_to_string list) in 
   ntmantisa str
 
 and nt_exponent str = 
   let nt1 =word_ci "e" in 
   let nt2 = word "*10**" in 
   let nt2 = disj nt1 nt2 in
   let nt1 = word "*10^" in 
   let nt1 = disj nt1 nt2 in 
   let nt1 = caten nt1 nt_int in
   let nt1 = pack nt1 (fun (_,num)-> "e"^(string_of_int num)) in
   nt1 str
 and nt_floatA str =
   let nt1 = char '.' in
   let nt1 = caten nt_integer_part nt1 in
   let nt1 = pack nt1 (fun (a,_)-> a^".") in
   let nt2 = (maybe nt_mantissa) in 
   let nt3 = (maybe nt_exponent) in 
   let nt2 = caten nt2  nt3 in
   let nt2 = pack nt2 (fun (a,b)-> match (a,b) with
   |(Some(c),Some(d)) -> c^d
   |(None,None)-> ""
   |(Some(c),None)-> c
   |(None,Some(c))-> c
   ) in
   let nt3 = caten nt1 nt2 in
   let nt3 = pack nt3 (fun (a,b)-> a^b) in
   nt3 str
 
 and nt_floatB str = 
   let nt1 = char '.' in 
   let nt1 = caten nt1 nt_mantissa in 
   let nt2 = (maybe nt_exponent) in 
   let nt2 = caten nt1 nt2  in 
   let floatB = pack nt2 (fun ((a,b),c) -> match ((a,b),c) with
   |((_,b),Some(str))-> "0."^b^str
   |((_,b),None)-> "0."^b
   ) in
   floatB str
 
 and nt_floatC str = 
   let nt1 = caten nt_integer_part nt_exponent in
   let nt1 = pack nt1 (fun (a,b)->  a^b) in
   nt1 str
 
 and nt_floatAll str = 
   let nt_plus=(char '+') in 
   let nt_minus =  (char '-') in 
   let nt1 = disj nt_plus nt_minus in
   let nt1 = maybe nt1 in 
   let nt2 = disj nt_floatA nt_floatB in 
   let nt2 = disj nt2 nt_floatC in 
   let nt1 = caten nt1 nt2 in
   let ntfloatall = pack nt1 (fun (a,b) -> match (a,b) with
   |(Some('-'),c)-> ScmReal(-.(float_of_string c)) 
   |(_,c)-> ScmReal(float_of_string c))
   in
   ntfloatall str
   
 and nt_number str = 
   let nt1 = nt_floatAll in
   let nt2 = nt_frac in
   let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
   let nt1 = disj nt1 nt2 in
   let nt1 = disj nt1 nt3 in 
   let nt1 = pack nt1 (fun a -> ScmNumber a) in
   let nt1 = not_followed_by nt1 nt_symbol_char in
   nt1 str
 and nt_boolean str =
   let nt_true = (word_ci "#t")in 
   let nt_true= pack nt_true (fun _ -> ScmBoolean true) in
   let nt_false = (word_ci "#f") in 
   let nt_false = pack nt_false (fun _-> ScmBoolean false) in
   let nt1 = disj nt_true nt_false in
   let nt1 = not_followed_by nt1 nt_symbol_char in
   nt1 str
 
 and nt_char_simple str =
   const (fun ch -> ch > ' ') str
 and make_named_char char_name ch =
   pack (word_ci char_name)(fun found -> ch) 
 and nt_char_named str =
   let nt1 =
     disj_list [(make_named_char "nul" '\x00');
                (make_named_char "newline" '\n');
                (make_named_char "page" '\012');
                (make_named_char "return" '\r');
                (make_named_char "space" ' ');
                (make_named_char "tab" '\t')] in
   nt1 str
 and nt_char_hex str = 
  let nt1 = range_ci 'a' 'f' in
  let nt2 = range '0' '9' in
  (disj nt1 nt2) str
 
 and nt_hexadecimal_char str = 
   let nt1 = pack (plus nt_char_hex) (fun ls -> char_of_int (int_of_string ("0x"^(list_to_string ls)))) in  
   let nt1 = caten (char_ci 'x') nt1 in 
   pack nt1 (fun (_,c)-> c) str
 
   and nt_char str =
   let nt1 = disj nt_hexadecimal_char nt_char_named in 
   let nt2 = disj nt1 nt_char_simple in 
   let nt2 = not_followed_by nt2 nt_symbol_char in 
   let nt1 = caten (word "#\\") nt2 in
   pack nt1 (fun (_,ch) -> ScmChar(ch)) str
 
 and nt_symbol_char str = 
   let nt1 = range '0' '9' in
   let nt1 = disj nt1 (range 'a' 'z') in
   let nt1 = disj nt1 (range 'A' 'Z') in
   let nt1 = disj nt1 (char '!') in
   let nt1 = disj nt1 (char '$') in 
   let nt1 = disj nt1 (char '^') in 
   let nt1 = disj nt1 (char '*') in
   let nt1 = disj nt1 (char '-') in 
   let nt1 = disj nt1 (char '_') in 
   let nt1 = disj nt1 (char '=') in
   let nt1 = disj nt1 (char '+') in 
   let nt1 = disj nt1 (char '<') in 
   let nt1 = disj nt1 (char '>') in
   let nt1 = disj nt1 (char '?') in 
   let nt1 = disj nt1 (char '/') in 
   let nt1 = disj nt1 (char ':') in 
   nt1 str
 
 
 and nt_symbol str =
   let nt1 = pack (plus nt_symbol_char ) list_to_string in
   let nt1 = pack nt1 (fun sym -> ScmSymbol sym) in
    (diff nt1 nt_number ) str 
 and nt_string_literal str = 
   (const (fun a -> a!= '\\' && a!= '~' && a!= '\"'))str
 and make_string_meta name c =
   pack (word_ci name) (fun  x -> c)
 and nt_string_meta str =
 let nt1 = make_string_meta "~~" '~' in
 let nt2 = make_string_meta "\\" '\\' in
 let nt3 = make_string_meta "\\f" '\012' in
 let nt4 = make_string_meta "\\t" '\t' in
 let nt5 = make_string_meta "\\r" '\r' in
 let nt6 =make_string_meta "\\n" '\n' in
 let nt1 = disj nt1 nt2 in
 let nt3 = disj nt3 nt4 in 
 let nt5 = disj nt5 nt6 in 
 let nt1 = disj nt1 nt3 in 
 let nt1 = disj nt1 nt5 in 
   nt1 str
 and nt_string_hex str = 
   let nt1 = plus nt_char_hex in
   let nt1 = caten (word_ci "\\x") nt1 in
   let nt1 = caten nt1 (char ';') in 
   ( pack nt1 (fun ((_,a),_) -> (char_of_int (int_of_string ("0x" ^ (list_to_string  a)))))) str  
 
 and nt_stringInterpolated str =
   let nt1 = caten (word "~{") (caten nt_sexpr (char '}')) in
   pack nt1 (fun (_, (sexp, _)) -> ScmPair(ScmSymbol("format"), ScmPair(ScmString("~a"), ScmPair(sexp,ScmNil)))) str
  
 (* and nt_newStringInterpolated str = 
  let nt1 = (caten (word("foramt"))(caten nt_sexpr nt_sexpr )) in
  pack nt1 (fun (_, (sexp,a)) -> ScmPair(ScmSymbol("format"), ScmPair(ScmString(sexp), ScmPair(a,ScmNil)))) str *)
 
 and nt_StringChar str =
   let nt1 = disj nt_string_hex nt_string_meta in
   let nt1 = disj nt1 nt_string_literal in 
   let nt1 = pack nt1 (fun a -> ScmChar(a)) in
   let nt2 = disj nt1 nt_stringInterpolated in
   (* let nt2 = disj nt2 nt_newStringInterpolated in *)
   nt2 str
 
 and nt_string str =
   let nt1 = pack (star nt_StringChar ) (fun ls -> 
   if(List.exists (fun a -> match a with
   | ScmPair(_) -> true
   |  b -> false) ls )
   then 
     (if((List.length ls) != 1)
     then 
       ScmPair(ScmSymbol("string-append"),(evaluate ls "")) 
     else
       List.hd ls)
                        
   else
     ScmString(list_to_string (List.map (fun x -> match x with 
                                                  | ScmChar(y)-> y
                                                  | _ -> ' ') ls))) in 
   let nt2 = caten nt1 (char '\"') in 
   let nt2 = caten (char '\"') nt2 in
   pack nt2 (fun (_,(s,_)) -> s) str
 and nt_vector str = 
   let nt1 = char ')' in
   let nt2 = caten nt_skip_star nt1 in
   let nt2 = pack nt2 (fun _ -> ScmVector []) in
   let nt3 = plus nt_sexpr in
   let nt3 = caten nt3 nt1  in
   let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
   let nt2 = disj nt2 nt3 in
   let nt1 = caten (word "#(") nt2 in
   pack nt1 (fun (_, a) -> a) str
 
 and nt_proper_list str = 
   let nt1 = char '(' in
   let nt2 = plus nt_sexpr in
   let nt1 = pack (caten nt1 nt2) (fun (_,sexp) -> sexp) in
   let nt1 = pack (caten nt1 (char '.')) (fun (sexp,_) -> sexp) in
   let nt1 = pack (caten nt1 nt_sexpr) (fun (sexp,s) -> List.fold_right (fun cur acc -> ScmPair(cur, acc)) sexp s) in
   let nt1 = caten nt1 (char ')') in
    pack nt1 (fun (p,_) -> p) str
 
 
 
 and nt_improper_list str = 
   let nt1 = (char ')') in 
   let nt2 = caten nt_skip_star nt1  in
   let nt2 = pack nt2 (fun a-> ScmNil) in
   let nt3 = plus nt_sexpr in
   let nt4 = char ')' in
   let nt3 = caten nt3 nt4 in
   let nt3 = pack nt3 (fun (sexp,_) -> List.fold_right (fun a b -> ScmPair(a, b)) sexp ScmNil) in
   let nt2 = disj nt2 nt3 in
   let nt1 = caten (char '(')  nt2 in
   let nt_Improper = pack nt1 (fun (_,ls) -> ls) in
   nt_Improper str
 
     
 and nt_list str =
   let nt1 = char '(' in
   let nt2 = caten nt_skip_star (char ')') in
   let nt2 = caten nt1 nt2 in 
   let nt2 = pack nt2 (fun (_)-> ScmNil) in
   let nt3 = disj_list [nt_proper_list; nt_improper_list] in
   let nt3 = pack nt3 (fun (list)-> list) in
   let nt2 = disj nt2 nt3 in 
   nt2 str
 
   and make_quasi_form symbol_name ch =
   let nt1 = word ch in
   let nt1 = pack nt1 (fun _ -> ScmSymbol(symbol_name)) in
   let nt2 = caten nt1 nt_sexpr in
   let nt2 = pack nt2 (fun (symbol,exp)-> ScmPair(symbol,ScmPair(exp,ScmNil))) in
   nt2
 and nt_quoted_forms str =
 
   let nt1 = disj_list [make_quasi_form "quote" "'";
                        make_quasi_form "quasiquote" "`";
                        make_quasi_form "unquote" ",";
                        make_quasi_form "unquote-splicing" ",@"] in
   nt1 str
 
 and nt_sexpr str =
   let nt1 =
     disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
                nt_string; nt_vector; nt_list; nt_quoted_forms] in
   let nt1 = make_skipped_star nt1 in
   nt1 str;;
 
 end;; (*end of struct Reader *)
 
 let rec string_of_sexpr = function
   | ScmVoid -> "#<void>"
   | ScmNil -> "()"
   | ScmBoolean(false) -> "#f"
   | ScmBoolean(true) -> "#t"
   | ScmChar('\n') -> "#\\newline"
   | ScmChar('\r') -> "#\\return"
   | ScmChar('\012') -> "#\\page"
   | ScmChar('\t') -> "#\\tab"
   | ScmChar(' ') -> "#\\space"
   | ScmChar(ch) ->
      if (ch < ' ')
      then let n = int_of_char ch in
           Printf.sprintf "#\\x%x" n
      else Printf.sprintf "#\\%c" ch
   | ScmString(str) ->
      Printf.sprintf "\"%s\""
        (String.concat ""
           (List.map
              (function
               | '\n' -> "\\n"
               | '\012' -> "\\f"
               | '\r' -> "\\r"
               | '\t' -> "\\t"
               | ch ->
                  if (ch < ' ')
                  then Printf.sprintf "\\x%x;" (int_of_char ch)
                  else Printf.sprintf "%c" ch)
              (string_to_list str)))
   | ScmSymbol(sym) -> sym
   | ScmNumber(ScmRational(0, _)) -> "0"
   | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
   | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
   | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
   | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
   | ScmVector(sexprs) ->
      let strings = List.map string_of_sexpr sexprs in
      let inner_string = String.concat " " strings in
      Printf.sprintf "#(%s)" inner_string
   | ScmPair(ScmSymbol "quote",
 
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "'%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "quasiquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "`%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote-splicing",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",@%s" (string_of_sexpr sexpr)
   | ScmPair(car, cdr) ->
      string_of_sexpr' (string_of_sexpr car) cdr
 and string_of_sexpr' car_string = function
   | ScmNil -> Printf.sprintf "(%s)" car_string
   | ScmPair(cadr, cddr) ->
      let new_car_string =
        Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
      string_of_sexpr' new_car_string cddr
   | cdr ->
      let cdr_string = (string_of_sexpr cdr) in
      Printf.sprintf "(%s . %s)" car_string cdr_string;;
  