(**  Abstract Syntax Tree definition of the Datalog language, accessor/check/transformation functions on the ASTs
 *)
(*
@original author: Vandang Tran
@updated by: Jumpei Tanaka
*)

type expr =
  | Prog of stt list
and stt =
  | Rule of rterm * term list
  | Query of rterm (* the goal predicate *)
  | Source of string * (string * stype) list
  | View of string * (string * stype) list
  | Source_schema of string * string * (string * stype) list (* the predicate of edb relation which is Source relation want to update*)
  | Target_schema of string * string * (string * stype) list
  | Constraint of rterm * term list
  | Pk of string * string list (*primary key*)

and rterm =  (* rterm is literal *)
  | Pred of string * var list (* string is name of predicate, var list is a list of variables*)
  | Deltainsert of string * var list (* delta predicate for insertion*)
  | Deltadelete of string * var list (* delta predicate for deletion*)
  | Deltainsert_ot of string * var list (* by Jumpei Tanaka, delta predicate-ot for insertion *)
  | Deltadelete_ot of string * var list (* by Jumpei Tanaka,delta predicate-ot for deletion *)
and term = (* term is one of predicate (positive or negative), equation, non-equation *)
  | Rel of rterm (* positive predicate *)
  | Equal of vterm * vterm  (* for example x = 5 *)
  | Ineq of string * vterm * vterm (* this is for other comparison, string is <>, >, <, >=, <=  *)
  | Not of rterm (* negative predicate *)  (* this is original*)
(*  | Not of term *)
  (* need to extend eqal and ineq to arithemetic expression like the expression "col1-1 = 3+1" in select * from tracks2_prime where col1-1 = 3+1 *)
and var =
  | NamedVar of string
  | NumberedVar of int (* this is not used in parser *)
  | ConstVar of const (* var in a literal in allowed to be a const like int or string, for example p(X,1) or p(X, 'tran' *)
  | AnonVar (* anonimous variable *)
  | AggVar of string * string (* the first string is function, the second is variable *)
and const =
  | Int of int
  | Real of float
  | String of string
  | Bool of bool
  | Null
and stype = Sint | Sreal | Sstring| Sbool (* data type in schema *)
(* and operator = Plus | Minus | Add | Sub | Mul multiply | Div | Lt | Gt | Le | Ge | Eq *)
and vterm (* value term *) =
  (* arithmetic expression *)
  | Const of const | Var of var | Sum of vterm * vterm | Diff of vterm * vterm | Times of vterm * vterm
  | Div of vterm * vterm | Neg of vterm
  (* string expression *)
  | Concat of vterm * vterm
  (* boolean expression *)
  | BoolAnd of vterm * vterm | BoolOr of vterm * vterm | BoolNot of vterm
  (* skolem function y = f(x1,x2, ... ,xn) , added by Jumpei Tanaka*)
(*  | Skolemf of var list *)
;;

(****************************************************
 *
 *  AST accessor functions
 *
 ****************************************************)

(** get the predicate name of an rterm *)
let get_rterm_predname rterm = match rterm with
    | Pred (x, vl) -> x
    | Deltainsert (x, vl)       -> "Δ_ins_"^ x
    | Deltadelete (x, vl)       -> "Δ_del_"^ x
    | Deltainsert_ot (x, vl)    -> "ot_Δ_ins_"^ x (* by Jumpei Tanaka *)
    | Deltadelete_ot (x, vl)    -> "ot_Δ_del_"^ x (* by Jumpei Tanaka *)
;;

(** get the arity of an rterm *)
let get_arity rterm = match rterm with
    | Pred (x, vl)              -> List.length vl
    | Deltainsert (x, vl)       -> List.length vl
    | Deltadelete (x, vl)       -> List.length vl
    | Deltainsert_ot (x, vl)    -> List.length vl (* by Jumpei Tanaka *)
    | Deltadelete_ot (x, vl)    -> List.length vl (* by Jumpei Tanaka *)
;;

(** get the arity of a rule *)
let get_rule_arity rule = match rule with
    | Rule (h, b)     -> get_arity h
    | _               -> invalid_arg "function get_rule_arity called without a rule"
;;

(** get the predicate name of a term *)
let rec get_predname t = match t with
    | Rel r           -> get_rterm_predname r
    | _               -> invalid_arg "function get_predname called without a relation"
;;

(** get a rule's head predicate name *)
let get_rule_predname r = match r with
    | Rule(h, t)      -> get_rterm_predname h
    | Query _         -> invalid_arg "function get_rule_predname called with a query"
    | Source _        -> invalid_arg "function get_rule_predname called with a source"
    | View _          -> invalid_arg "function get_rule_predname called with a view"
    | Source_schema _  -> invalid_arg "function get_rule_predname called with a source schema"
    | Target_schema _  -> invalid_arg "function get_rule_predname called with a target schema"
    | Constraint _    -> invalid_arg "function get_rule_predname called with a constraint"
    | Pk _            -> invalid_arg "function get_rule_predname called with a Pk"
;;

(** get a rule's head pred *)
let rule_head r = match r with
    | Rule(h, _)      -> h
    | Query _         -> invalid_arg "function rule_head called with a query"
    | Source _        -> invalid_arg "function rule_head called with a source"
    | View _          -> invalid_arg "function rule_head called with a view"
    | Source_schema _        -> invalid_arg "function rule_head called with a source schema"
    | Target_schema _        -> invalid_arg "function rule_head called with a target schema"
    | Constraint _    -> invalid_arg "function rule_head called with a constraint"
    | Pk _            -> invalid_arg "function rule_head called with a Pk"
;;

(** get a rule's body list of terms *)
let rule_body r = match r with
    | Rule(_, t)      -> t
    | Query _         -> invalid_arg "function rule_body called with a query"
    | Source _        -> invalid_arg "function rule_body called with a source"
    | View _          -> invalid_arg "function rule_body called with a view"
    | Source_schema _        -> invalid_arg "function rule_body called with a source schema"
    | Target_schema _        -> invalid_arg "function rule_body called with a target schema"
    | Constraint _    -> invalid_arg "function rule_body called with a constraint"
    | Pk _            -> invalid_arg "function rule_body called with a Pk"
;;

(** get rterm varlist *)
let get_rterm_varlist t = match t with
    | Pred (x, vl)            -> vl
    | Deltainsert (x, vl)     -> vl
    | Deltadelete (x, vl)     -> vl
    | Deltainsert_ot (x, vl)  -> vl (* by Jumpei Tanaka *)
    | Deltadelete_ot (x, vl)  -> vl (* by Jumpei Tanaka *)
;;

(** get rterm varlist *)
(* Jumpei Tanaka *)
let rec filter_named_var_list vl = match vl with
    | [] -> []
    | hd::rest -> (_1_filter_named_var_list hd) @ (filter_named_var_list rest)
    and _1_filter_named_var_list v = match v with
      | NamedVar _ -> [v]
      | _ -> []
;;


let rec get_vterm_varlist e = match e with
    | Const const         -> []
    | Var var             ->  [var]
    | Sum (ae1, ae2)      -> (get_vterm_varlist ae1) @ (get_vterm_varlist ae2)
    | Diff (ae1, ae2)     -> (get_vterm_varlist ae1) @ (get_vterm_varlist ae2)
    | Times (ae1, ae2)    -> (get_vterm_varlist ae1) @ (get_vterm_varlist ae2)
    | Div (ae1, ae2)      -> (get_vterm_varlist ae1) @ (get_vterm_varlist ae2)
    | Neg ae              -> get_vterm_varlist ae
    | Concat(ae1, ae2)    -> (get_vterm_varlist ae1) @ (get_vterm_varlist ae2)
    | BoolAnd (ae1, ae2)  -> (get_vterm_varlist ae1) @ (get_vterm_varlist ae2)
    | BoolOr (ae1, ae2)   -> (get_vterm_varlist ae1) @ (get_vterm_varlist ae2)
    | BoolNot ae          -> get_vterm_varlist ae
(*    | Skolemf varl        -> varl *)

(** get the list of variables of a term *)
let rec get_term_varlist t = match t with
    | Rel r              -> get_rterm_varlist r
    | Equal (e1, e2)     -> (get_vterm_varlist e1) @ (get_vterm_varlist e2)
    | Ineq  (op,e1, e2)  -> (get_vterm_varlist e1) @ (get_vterm_varlist e2)
    | Not r              -> get_rterm_varlist r
;;

(** Given a query, returns the rterm that is defined inside*)
let get_query_rterm (r:stt) = match r with
    | Query rt          -> rt
    | _                 -> invalid_arg "function get_query_rterm called without a query"
;;

(** Given a schema declaration (source and view), returns the rterm that is defined inside*)
let get_schema_rterm (r:stt) = match r with
    | Source (name, lst)  -> Pred(name, (List.map (fun (col,typ) -> NamedVar col) lst))
    | View (name, lst)  -> Pred(name, (List.map (fun (col,typ) -> NamedVar col) lst))
    | Source_schema (_, name, lst) -> Pred(name, (List.map (fun (col,typ) -> NamedVar col) lst))
    | Target_schema (_, name, lst) -> Pred(name, (List.map (fun (col,typ) -> NamedVar col) lst))
    | _                 -> invalid_arg "function get_schema_rterm called without an schema"
;;

(** Given a schema declaration (source and view), returns the rterm that is defined inside*)
(* Jumpei Tanaka *)
let get_source_rterml (r:stt) = match r with
    | Source (name, lst) -> [Pred(name, (List.map (fun (col,typ) -> NamedVar col) lst))]
    | _                  -> []
;;

let get_source_sch_rterml (r:stt) = match r with
    | Source_schema (_,name, lst) -> [Pred(name, (List.map (fun (col,typ) -> NamedVar col) lst))]
    | _                  -> []
;;

let get_target_sch_rterml (r:stt) = match r with
    | Target_schema (_,name, lst) -> [Pred(name, (List.map (fun (col,typ) -> NamedVar col) lst))]
    | _                  -> []
;;


(** Given a schema declaration (source and view), returns the attribute list*)
let get_schema_attrs (r:stt) = match r with
    | Source (name, lst)  -> List.map (fun (col,typ) ->  col) lst
    | View (name, lst)    -> List.map (fun (col,typ) ->  col) lst
    | Source_schema (_, name, lst)  -> List.map (fun (col,typ) ->  col) lst
    | Target_schema (_, name, lst)  -> List.map (fun (col,typ) ->  col) lst
    | _                 -> invalid_arg "function get_schema__attrs called without an schema"
;;

(** Given a schema declaration (source and view), returns the list of column:typ  *)
let get_schema_col_typs (r:stt) = match r with
    | Source (name, lst) -> lst
    | View (name, lst)   -> lst
    | _                  -> invalid_arg "function get_schema_col_typs called without an schema"
;;

(** Given a schema declaration (source and view), returns the schema name  *)
let get_schema_name (r:stt) = match r with
    | Source (name, lst) -> name
    | View (name, lst)  -> name
    | Source_schema (_, name, lst) -> name
    | Target_schema (_, name, lst)  -> name
    | _ -> invalid_arg "function get_schema_name called without an schema"
;;

(** Given program return all schema statement*)
let get_schema_stts prog = match prog with
    | Prog sttlst -> List.filter (fun x -> match x with Source _ -> true | View _ -> true | Source_schema _ -> true | Target_schema _ -> true | _ -> false) sttlst
;;

(** Given program return all source statement*)
let get_source_stts prog = match prog with
    | Prog sttlst -> List.filter (fun x -> match x with Source _ -> true | _ -> false) sttlst
;;

(** Given program return all source schema statement*)
let get_source_sch_stts prog = match prog with
    | Prog sttlst -> List.filter (fun x -> match x with Source_schema _ -> true | _ -> false) sttlst
;;

(** Given a rule, returns all the positive and negative rterms
 * inside*)
let get_all_rule_rterms = function
    | Rule(_, t) ->
        let rec extract_rterm acc = function
            | Rel x -> x::acc
            | Not x -> x::acc
            | _ -> acc in
        List.fold_left extract_rterm [] t
    | Query _         -> invalid_arg "function get_all_rule_rterms called with a query"
    | Source _        -> invalid_arg "function get_all_rule_rterms called with a source"
    | View _          -> invalid_arg "function get_all_rule_rterms called with a view"
    | Source_schema _  -> invalid_arg "function get_all_rule_rterms called with a source schema"
    | Target_schema _  -> invalid_arg "function get_all_rule_rterms called with a target schema"
    | Constraint _    -> invalid_arg "function get_all_rule_rterms called with a constraint"
    | Pk _            -> invalid_arg "function get_all_rule_rterms called with a Pk"

(** Given a rule, returns all the negative rterms
 * inside*)
let get_all_negative_rule_rterms = function
    | Rule(_, t) ->
        let rec extract_rterm acc = function
            | Not x -> x::acc
            | _ -> acc in
        List.fold_left extract_rterm [] t
    | Query _         -> invalid_arg "function get_all_rule_rterms called with a query"
    | Source _        -> invalid_arg "function get_all_rule_rterms called with a source"
    | View _          -> invalid_arg "function get_all_rule_rterms called with a view"
    | Source_schema _  -> invalid_arg "function get_all_rule_rterms called with a source schema"
    | Target_schema _  -> invalid_arg "function get_all_rule_rterms called with a target schema"
    | Constraint _    -> invalid_arg "function get_all_rule_rterms called with a constraint"
    | Pk _            -> invalid_arg "function get_all_rule_rterms called with a Pk"

(** Given a rule, returns all the negative rterms
 * inside*)
let get_all_positive_rule_rterms = function
    | Rule(_, t) ->
        let rec extract_rterm acc = function
            | Rel x -> x::acc
            | _ -> acc in
        List.fold_left extract_rterm [] t
    | Query _         -> invalid_arg "function get_all_rule_rterms called with a query"
    | Source _        -> invalid_arg "function get_all_rule_rterms called with a source"
    | View _          -> invalid_arg "function get_all_rule_rterms called with a view"
    | Source_schema _  -> invalid_arg "function get_all_rule_rterms called with a source schema"
    | Target_schema _  -> invalid_arg "function get_all_rule_rterms called with a target schema"
    | Constraint _    -> invalid_arg "function get_all_rule_rterms called with a Constraint"
    | Pk _            -> invalid_arg "function get_all_rule_rterms called with a Pk"

(** Given an equality, returns the (var,const) tuple that defines it *)
let extract_eq_tuple = function
    | Equal (v,c) -> (v,c)
    | _ -> invalid_arg "function extract_eq_tuple called without an equality"

(** Given an inequality, returns the (op,var,const) tuple that defines it *)
let extract_ineq_tuple = function
    | Ineq (s,v,c) -> (s,v,c)
    | _ -> invalid_arg "function extract_ineq_tuple called without an inequality"

(** Given an aggregated variable, returns the (function_name,var_name) tuple that defines it *)
let extract_aggvar_tuple = function
    | AggVar (fn,vn) -> (fn,vn)
    | _ -> invalid_arg "function extract_aggvar_tuple called without an aggregated var"

(****************************************************
 *
 *  AST check / transformation functions
 *
 ****************************************************)

(*Given an equation, returns the equivalent of a negation of it*)
let negate_eq = function
    | Equal (v,c) -> Ineq ("<>",v,c)
    | Ineq ("<>",v,c) -> Equal (v,c)
    | Ineq ("<",v,c) -> Ineq (">=",v,c)
    | Ineq (">",v,c) -> Ineq ("<=",v,c)
    | Ineq ("<=",v,c) -> Ineq (">",v,c)
    | Ineq (">=",v,c) -> Ineq ("<",v,c)
    | _ -> invalid_arg "function negate_eq called without an equation"

(*Given an term, returns the equivalent of a negation of it*)
let negate_term term= match term with
      Rel (rt) -> Not (rt)
    | Not (rt) -> Rel (rt)
    | _ -> negate_eq term

(** Returns true if the provided argument is an aggregate variable *)
let is_aggvar = function
    | AggVar _ -> true
    | _ -> false

(** Returns true if the provided argument is an anonymous variable *)
let is_anon = function
    | AnonVar -> true
    | _ -> false

(** Returns true if the provided argument is an equality involving an
aggregate function*)
let is_agg_equality = function
    | Equal (e1, e2) -> (List.length (List.filter is_aggvar ((get_vterm_varlist e1) @ (get_vterm_varlist e2)))) > 0
    | _ -> invalid_arg "function is_agg_equality called without an equality"

(** Returns true if the provided argument is an inequality involving an
aggregate function*)
let is_agg_inequality = function
    | Ineq (_ , e1, e2) -> (List.length (List.filter is_aggvar ((get_vterm_varlist e1) @ (get_vterm_varlist e2)))) > 0
    | _ -> invalid_arg "function is_agg_inequality called without an equality"

(****************************************************
 *
 *  String operations
 *
 ****************************************************)

(** support function for smart stringify of the AST - see to_string below *)
let rec string_of_const t = match t with
    | Int x -> string_of_int x
    | Real x -> if (x = floor x) then (string_of_float x)^"0" else (string_of_float x)
    | String x -> x
    | Bool x -> string_of_bool x
    | Null -> "null"
;;

(** convert the var type into a string *)
let string_of_var r = match r with
    | NamedVar x -> x
    | NumberedVar x -> "_" ^ string_of_int x
    | AnonVar    -> "_"
    | ConstVar x -> string_of_const x
    | AggVar (fn,vn) -> fn^"("^vn^")"
;;

(** support function for smart stringify of the AST - see to_string below *)
let string_of_rterm r = match r with
    | Pred (pn,vars) -> pn^"("^String.concat ", " (List.map string_of_var vars)^")"
    | Deltainsert (pn,vars) -> "+"^ pn^"("^String.concat ", " (List.map string_of_var vars)^")"
    | Deltadelete (pn,vars) -> "-"^pn^"("^String.concat ", " (List.map string_of_var vars)^")"
    | Deltainsert_ot (pn,vars) -> "(+)"^ pn^"("^String.concat ", " (List.map string_of_var vars)^")" (* by Jumpei Tanaka *)
    | Deltadelete_ot (pn,vars) -> "(-)"^pn^"("^String.concat ", " (List.map string_of_var vars)^")" (* by Jumpei Tanaka *)
;;

(** convert the vterm type into a string *)
let string_of_vterm ae =
    (* open and close parentthesis in current expresion by using the priority of the expression containing the current expression
    opem_paren and close_paren take two priorities of previous operator and current operator
    higher priority means earlier evaluation
    "+" give the same priority of 0 to its two terms, and priority of 0 for the term contain this "+"
    "-" give the priority 0 to the first term and priority 1 to the second term (the first term should be evaluated first), and priority of 0 for the term contain this "-"
    similarly, "*" give its two terms the priority 2, "/" give its two terms the priority 2 and 3
    "-" which is minus sign has highest priority
     *)
  let open_paren prec op_prec =
    if prec > op_prec then  "(" else "" in
  let close_paren prec op_prec =
    if prec > op_prec then  ")" else "" in
  let rec str_of prec aexp =
    match aexp with
      Const c -> string_of_const c
    | Var v -> string_of_var v
    | Sum(f,g) -> (open_paren prec 0)^ (str_of 0 f) ^ "+" ^ (str_of 0 g) ^ (close_paren prec 0)
    | Diff(f,g) -> (open_paren prec 0) ^ (str_of 0 f) ^  "-" ^ (str_of 1 g) ^ (close_paren prec 0)
    | Times(f,g) -> (open_paren prec 2) ^ (str_of 2 f) ^  "*" ^ (str_of 2 g) ^ (close_paren prec 2)
    | Div (f,g) -> (open_paren prec 2)^ (str_of 2 f) ^ "/" ^ (str_of 3 g) ^ (close_paren prec 2)
    | Neg e ->  (open_paren prec 4)^ "-" ^ (str_of 5 e)^(close_paren prec 4)
    | Concat(f,g) -> (open_paren prec 0)^ (str_of 0 f) ^ "^" ^ (str_of 0 g) ^ (close_paren prec 0)
    | BoolAnd (f,g) -> (open_paren prec 2) ^ (str_of 2 f) ^  "*" ^ (str_of 2 g) ^ (close_paren prec 2)
    | BoolOr (f,g) -> (open_paren prec 0)^ (str_of 0 f) ^ "+" ^ (str_of 0 g) ^ (close_paren prec 0)
    | BoolNot e ->  (open_paren prec 4)^ "-" ^ (str_of 5 e)^(close_paren prec 4)
(*    | Skolemf varlst -> "~id:(" ^ String.concat ", " (List.map string_of_var varlst) ^ ")" (* Added by Jumpei tanaka*) *)
  in str_of 0 ae;;
;;

(** support function for smart stringify of the AST - see to_string below *)
let rec string_of_term t = match t with
    | Rel r             -> string_of_rterm r
    | Equal (e1, e2)      -> (string_of_vterm e1) ^ " = " ^ (string_of_vterm e2)
    | Ineq (op,e1, e2)    -> (string_of_vterm e1) ^ " " ^ op ^ " " ^ (string_of_vterm e2)
    | Not rt            -> "not " ^ string_of_rterm rt
;;

let string_of_stype t = match t with
    Sint -> "int"
    | Sreal -> "real"
    | Sstring -> "string"
    | Sbool -> "bool"

(** support function for smart stringify of the AST - see to_string below *)
(* by Jumpei Tanaka *)
let string_of_stt st = match st with
    | Rule (p, tel) -> string_of_rterm p ^ " :- " ^
                       String.concat " , " (List.map string_of_term tel) ^ ".\n"
    | Query r -> "?- " ^ string_of_rterm r ^ ".\n"
    | Source (name, lst)  -> "source " ^ name ^
                             "(" ^ String.concat ", " (List.map (fun (col,typ) -> "'"^col^"'"^":"^ (string_of_stype typ)) lst) ^ ").\n"
    | View (name, lst)    -> "view " ^ name ^
                             "(" ^ String.concat ", " (List.map (fun (col,typ) -> "'"^col^"'"^":"^ (string_of_stype typ)) lst) ^ ").\n"
    | Source_schema (dbschema, relname, lst) -> "source: " ^ dbschema ^ "#" ^ relname ^
                             "(" ^ String.concat ", " (List.map (fun (col,typ) -> "'"^col^"'"^":"^ (string_of_stype typ)) lst) ^ ").\n"
    | Target_schema (dbschema, relname, lst) -> "target: " ^ dbschema ^ "#" ^ relname ^
                             "(" ^ String.concat ", " (List.map (fun (col,typ) -> "'"^col^"'"^":"^ (string_of_stype typ)) lst) ^ ").\n"
    | Constraint (p, tel) -> string_of_rterm p ^ " :- " ^
                             String.concat " , " (List.map string_of_term tel) ^ ".\n"
    | Pk(relname, attrlst) -> "PK(" ^ relname ^ ", [" ^
                              String.concat ", " (List.map (fun col -> "'" ^ col ^ "'") attrlst) ^ "]).\n"
;;

(** smart stringify for AST *)
let to_string e = match e with
    | Prog []         -> invalid_arg "Passed empty program to stringify"
    | Prog stl        -> List.fold_right (^) (List.map string_of_stt stl) ""
;;

let str_to_namedvar = function str -> NamedVar str;;

let stringlist_to_varlist strlst = List.map str_to_namedvar strlst;;

(** convert datalog program to string  *)
let string_of_prog = function
    | Prog stt_lst ->
        String.concat "" (List.map string_of_stt stt_lst)

let stype_of_const c = match c with
    Int _ -> Sint
    | Real _ -> Sreal
    | String _ -> Sstring
    | Bool _ -> Sbool
    | Null -> invalid_arg "Null does not have type"

(** Take a rterm and return its delta of insertion *)
let get_ins_delta_pred del_rterm = match del_rterm with
    | Pred (x, vl) -> Deltainsert (x, vl)
    | Deltainsert (x, vl) -> Deltainsert (x, vl)
    | Deltadelete (x, vl) -> Deltainsert (x, vl)
    | _ -> invalid_arg "A function get_ins_delta_pred is called with invarid args"

(** Take a rterm and return its delta of deletion *)
let get_del_delta_pred del_rterm = match del_rterm with
    | Pred (x, vl) -> Deltadelete (x, vl)
    | Deltainsert (x, vl) -> Deltadelete (x, vl)
    | Deltadelete (x, vl) -> Deltadelete (x, vl)
    | _ -> invalid_arg "A function get_del_delta_pred is called with invarid args"

(** Take a delta rterm and return a dummy rterm of new source  *)
let get_new_source_rel_pred del_rterm = match del_rterm with
    | Pred (x, vl) | Deltainsert (x, vl) | Deltadelete (x, vl) -> Pred("__dummy_new_"^ x,vl)
    | _ -> invalid_arg "A function get_new_source_rel_pred is called with invarid args"

(** Take a delta rterm and return a rterm of source relation *)
let get_source_rel_pred del_rterm = match del_rterm with
    | Pred (x, vl) | Deltainsert (x, vl) | Deltadelete (x, vl) -> Pred(x,vl)
    | _ -> invalid_arg "A function get_source_rel_pred is called with invarid args"

(** take a constraint and return an equivalent rule *)
let rule_of_constraint c = match c with
    | Constraint (h,b)  -> Rule(h,b)
    | Pk _              -> invalid_arg "function rule_of_constraint called with a primary key"
    | Rule _            -> invalid_arg "function rule_of_constraint called with a rule"
    | Query _           -> invalid_arg "function rule_of_constraint called with a query"
    | Source _          -> invalid_arg "function rule_of_constraint called with a source"
    | View _            -> invalid_arg "function rule_of_constraint called with a view"
    | Source_schema _    -> invalid_arg "function rule_of_constraint called with a source schema"
    | Target_schema _    -> invalid_arg "function rule_of_constraint called with a target schema"

let get_empty_pred = Pred ("⊥", [])
;;


(** add a list of stt to a program *)
let add_stts lst prog = match prog with
    | Prog sttlst -> Prog(sttlst@lst)

(** insert a new statement *)
let insert_stt stt prog = add_stts [stt] prog;;

let is_rule_of_predname predname stt = match stt with
    | Rule(h, b) -> (String.compare (get_rterm_predname h)  predname == 0)
    | Query _
    | Source _
    | View _
    | Source_schema _
    | Target_schema _
    | Constraint _ | Pk _  -> false

(** delete all rule of a predname *)
let delete_rule_of_predname predname prog = match prog with
    | Prog sttlst ->
        (* print_endline ("delete rule of "^predname);
        print_endline (string_of_prog (Prog (List.filter (fun x -> not (is_rule_of_predname predname x)) sttlst)) );  *)
        Prog (List.filter (fun x -> not (is_rule_of_predname predname x)) sttlst)
;;

(** check whether a predicate is defined in the program*)
let is_defined_pred predname prog = match prog with
    | Prog sttlst ->
      let all_rules =  (List.filter (fun x -> (is_rule_of_predname predname x)) sttlst) in
      (List.length all_rules) > 0
;;


(***********************************************************************)
(* Added functions                                                     *)
(* by Jumpei Tanaka                                                    *)
(***********************************************************************)

let get_tablename_view view = match view with
    | View (str, _) -> str
    | _ -> invalid_arg "get_tablename_view"
;;

let get_vars_view view = match view with
    | View (_,vars) -> let filter_str var = NamedVar (fst var) in
                       List.map filter_str vars
    | _ -> invalid_arg "get_tablename_view"
;;

let get_tablename_source source = match source with
    | Source (str, _) -> str
    | _ -> invalid_arg "get_tablename_source"
;;

let get_vars_source source = match source with
    | Source (_,vars) -> let filter_str var = NamedVar (fst var) in
                       List.map filter_str vars
    | _ -> invalid_arg "get_tablename_source"
;;

let get_tablename_pk contrt = match contrt with
    | Pk (str, _) -> str
    | _ -> invalid_arg "get_tablename_pk"
;;

let get_vars_pk contrt = match contrt with
    | Pk (_,vars) -> vars
    | _ -> invalid_arg "get_tablename_pk"
;;


(* to change view name for partial get *)
let string_of_view_partial st = match st with
    | View (name, lst) -> name ^ "_partial" ^ "(" ^ String.concat ", " (List.map (fun (col,_) -> col) lst) ^ ")"
    | _ -> invalid_arg "string_of_view"
;;

(** Given program return all rules statement*)
let get_rule_stts prog = match prog with
    | Prog sttlst -> List.filter (fun x -> match x with Rule _ -> true | _ -> false) sttlst
;;

(** Given program return all constraint statement*)
let get_const_stts prog = match prog with
    | Prog sttlst -> List.filter (fun x -> match x with Constraint _ -> true | _ -> false) sttlst
;;

(** Given program return all pk statement*)
let get_pk_stts prog = match prog with
    | Prog sttlst -> List.filter (fun x -> match x with Pk _ -> true | _ -> false) sttlst
;;


let string_of_view st = match st with
    | View (name, lst) -> name ^ "(" ^ String.concat ", " (List.map (fun (col,_) -> col) lst) ^ ")"
    | _ -> invalid_arg "string_of_view"
;;

let string_of_source stl = match stl with
    | Source (name, lst) -> name ^ "(" ^ String.concat ", " (List.map (fun (col,_) -> col) lst) ^ ")"
    | _ -> invalid_arg "string_of_source"
;;

(* transform rule head (idb) to negated atom (idb) *)
let idb2edb stt = match stt with
  | Rule (Pred(str,varlst),_) -> Rel (Pred(str,varlst))
  | Rule (Deltainsert(str,varlst),_) -> Rel (Deltainsert(str,varlst))
  | Rule (Deltadelete(str,varlst),_) -> Rel (Deltadelete(str,varlst))
  | _ -> invalid_arg "idb2edb"
;;

(* get rterm list of positive and negative ordinary literla from body of Rule *)
let rec rule2rt_lst rule = match rule with
  | Rule (rt, tmlst) -> _1_rule2rt_lst tmlst
  | _ -> invalid_arg "function term_lst called with rterm_lst"

  and _1_rule2rt_lst tmlst = match tmlst with
      | [] -> []
      | hd::rest -> (_2_rule2rt_lst hd) @ (_1_rule2rt_lst rest)

  and _2_rule2rt_lst tm = match tm with
      | Rel rt -> [rt]
      | Not rt -> [rt]
      | _ -> []
;;

(* get rterm list of positive and negative ordinary literla from body of Rule list *)
let rec rules2rt_lst rules = match rules with
  | [] -> []
  | hd::rest -> (rule2rt_lst hd) @ (rules2rt_lst rest)

(* get_lmtd_varl                 *)
(*   Input:  terml:term list     *)
(*   Output: lmtd_varl:var list  *)
let rec get_lmtd_varl terml = match terml with
    | [] -> []
    | hd::rest -> (_1_get_lmtd_varl hd) @ (get_lmtd_varl rest)

  and _1_get_lmtd_varl hd = match hd with
    | Rel (rt) -> get_lmtd_var_rel rt
    | Not _ -> []
    | Equal (vt1, vt2) -> get_lmtd_var_eq vt1 vt2
    | Ineq _ -> []

  and get_lmtd_var_rel rt = match rt with
    | Pred(_, varl) -> _1_get_lmtd_var_rel varl
    | Deltainsert(_, varl) -> _1_get_lmtd_var_rel varl
    | Deltadelete(_, varl) -> _1_get_lmtd_var_rel varl
    | _ -> []

  and _1_get_lmtd_var_rel varl = match varl with
    | [] -> []
    | hd::rest -> (_2_get_lmtd_var_rel hd) @ (_1_get_lmtd_var_rel rest)

  and _2_get_lmtd_var_rel var = match var with
    | NamedVar(str) -> [NamedVar(str)]
    | _ -> []

  and get_lmtd_var_eq vt1 vt2 =
    let vt = (vt1, vt2) in
    match vt with
    | (Var(NamedVar(v)), Const(c)) -> [NamedVar(v)]
    | (Const(c), Var(NamedVar(v))) -> [NamedVar(v)]
    | _ -> []
;;

(***********************************************************
 *  AST
 ***********************************************************)
(* Add stt to AST *)
let add_sttl ast sttl = match ast with
  | Prog sttlst -> Prog (sttlst@sttl)
;;

(* return sttl from AST *)
let get_sttl ast = match ast with
  | Prog (sttl) -> sttl
;;

(* AST to stt list *)
let to_sttlst ast = match ast with
  | Prog sttlst -> sttlst
;;

(* Merge ASTs ast: = ast1 + ast2 *)
let merge_ast ast1 ast2 = match ast1 with
  | Prog stt_lst -> let _merge_ast stt_lst1 ast2 = match ast2 with
                      | Prog stt_lst2 -> Prog (stt_lst1@stt_lst2)
                    in
                    _merge_ast stt_lst ast2
;;

(* Subtract ASTs: ast = ast1 - ast2 *)
let subtract_ast ast1 ast2 =
  let rec list_minus lst1 lst2 = match lst2 with
    | [] -> lst1
    | hd::rest -> if (List.mem hd lst1)
                  then
                    let lst11 = List.filter (fun x -> x <> hd) lst1 in
                    list_minus lst11 rest
                  else
                    list_minus lst1 rest
  in
  let result = Prog (list_minus (get_sttl ast1) (get_sttl ast2)) in
result
;;

(* Get Source and change to Pred *)
let rec source2pred stt_lst = match stt_lst with
  | [] -> []
  | hd::rest -> [_1_source2pred hd] @ source2pred rest

  and _1_source2pred hd = match hd with
      | Source (str, vartypes) -> Pred(str, (_2_source2pred vartypes))
      | _ -> invalid_arg "source2pred"

  and _2_source2pred vartypes = match vartypes with
      | [] -> []
      | hd::rest -> [NamedVar(fst hd)] @ (_2_source2pred rest)
;;

(* From given program, exclude source, target and view *)
let exclude_source_target_stt prog = match prog with
  | Prog sttlst -> Prog (
                         List.filter
                         (fun x -> match x with Source _ ->  false | View _ -> false | Source_schema _ -> false | Target_schema _ -> false | _ -> true )
                         sttlst
                        )
;;

(* get rterm list of rule heads *)
let rec rule_head2pred prog = match prog with
  | Prog sttlst -> _1_rule_head2pred sttlst

  and _1_rule_head2pred sttlst = match sttlst with
    | [] -> []
    | hd::rest -> (_2_rule_head2pred hd) @ (_1_rule_head2pred rest)

  and _2_rule_head2pred hd = match hd with
    | Rule (Pred(rel, varlst), _) -> [Pred(rel, varlst)]
    | _ -> []
;;

(** get the predicate name of an rterm *)
let get_predname rterm = match rterm with
    | Pred (x, vl) -> x
    | Deltainsert (x, vl)       -> x
    | Deltadelete (x, vl)       -> x
    | Deltainsert_ot (x, vl)    -> x (* by Jumpei Tanaka *)
    | Deltadelete_ot (x, vl)    -> x (* by Jumpei Tanaka *)
;;

(***********************************************************************)
(* print                                                               *)
(* by Jumpei Tanaka                                                    *)
(***********************************************************************)

let print_sttlst sttlst =
  let print_el s = Printf.printf "%s" (string_of_stt s); in
  List.iter print_el sttlst
;;

(* print AST *)
let print_ast ast = match ast with
  | Prog stt_lst -> print_sttlst stt_lst
;;
