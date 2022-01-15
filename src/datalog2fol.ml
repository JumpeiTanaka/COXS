
open Printf;;
open Lib;;
open Formulas;;
open Fol;;
open Skolem;;
open Fol_ex;;
open Expr;;
open Utils;;
open Tools;;
open Rule_preprocess;;

(* ---------------------------------------------------------------------------------------
  @author: Vandang Tran
  convert the vterm type into a Fol.term
--------------------------------------------------------------------------------------------*)

let rec folterm_of_vterm ae =
    match ae with
      Const c -> Fn (string_of_const c,[])
    | Var v -> Fol.Var (string_of_var v)
    | Sum(f,g) -> Fn("+",[folterm_of_vterm f; folterm_of_vterm g])
    | Diff(f,g) -> Fn("-",[folterm_of_vterm f; folterm_of_vterm g])
    | Times(f,g) -> Fn("*",[folterm_of_vterm f; folterm_of_vterm g])
    | Div (f,g) -> Fn("/",[folterm_of_vterm f; folterm_of_vterm g])
    | Neg e ->  Fn("-",[folterm_of_vterm e])
    | Concat(f,g) -> Fn("^",[folterm_of_vterm f; folterm_of_vterm g])
    | BoolAnd (f,g) -> Fn("and",[folterm_of_vterm f; folterm_of_vterm g])
    | BoolOr (f,g) -> Fn("or",[folterm_of_vterm f; folterm_of_vterm g])
    | BoolNot e ->  Fn("not",[folterm_of_vterm e])
;;


(* ---------------------------------------------------------------------------------------
  @author: Vandang Tran
  for non-recursive datalog, we do not need stratification, we just need recursively translate each idb predicate (identified symkey) to a FO formula,
  this function take a symtkey of a rterm and generate its FO formula recursively (this function is recursive because of unfolding all the idb predicate)
--------------------------------------------------------------------------------------------*)
let rec fol_of_symtkey (idb:symtable) (cnt:colnamtab) (goal:symtkey)  =

    let rule_lst = try Hashtbl.find idb goal
        with Not_found -> raise(SemErr( "Not_found in func fol_of_symtkey"))
        in
    (* disjunction of all rules then we have FO formula for a idb predicate*)

        (* printf "(~_~)0: fol_of_symtkey: rule_lst => \n"; (*Jumpei*) *)
        (* print_sttlst rule_lst; (*Jumpei*) *)

    let fol_of_rule_lst (idb:symtable) (cnt:colnamtab) rules =
        let fol_list = List.map (fol_of_rule idb cnt) rules in
            (* Just print *)

            (* print_endline "(~_~)2"; (*Jumpei*) *)

        let fm = match fol_list with
            hd::bd -> if (List.length bd = 0) then hd else
                    List.fold_left (fun form e -> Formulas.Or(form, e)) hd bd
            | _ -> failwith "there is no rule for the idb relation" in
        fm in

    let fm = fol_of_rule_lst idb cnt rule_lst in
    fm

and fol_of_rule (idb:symtable) (cnt:colnamtab) rule =
    let head = rule_head rule in
    let body = rule_body rule in

    let (p_rt,n_rt,all_eqs,all_ineqs) = split_terms body in
    (* substitute variables of the head to column name of the prediate of the head *)

    let cols =
        try Hashtbl.find cnt (symtkey_of_rterm head)
        with Not_found -> raise(SemErr ("Not found in cnt the atom "^string_of_rterm head))
        in

      (*
      printf "(~_~)1.1: fol_of_rule*: ";  (*Jumpei*)
        printf "cols => [";
        let print_el s = printf "%s; " s in List.iter print_el cols;
        printf "]\n";
      *)

    let varlst = get_rterm_varlist head in
    let subfn = fpf (List.map (fun x -> string_of_var x) varlst) (List.map (fun x -> Fol.Var x) cols) in

    (* existential vars of the body is vars in body but not in the head *)
    let exvars = VarSet.filter (fun x -> not (is_anon x)) (VarSet.diff (get_termlst_varset body) (VarSet.of_list (get_rterm_varlist head))) in

    let conjunction_lst =
        (List.map (fun x -> fol_of_rterm x idb cnt) p_rt)
      @ (List.map (fun x -> Formulas.Not(fol_of_rterm x idb cnt) ) n_rt)
      @ (List.map (fun x -> fol_of_eq x) all_eqs)
      @ (List.map (fun x -> fol_of_ineq x) all_ineqs)
    in

        (* print_endline "(~_~)1.4"; (*Jumpei*) *)

    let fm = match conjunction_lst with
        hd::bd -> if (List.length bd = 0) then hd else
            List.fold_left (fun form e -> Formulas.And(form, e)) hd bd
        | _ -> failwith "the body of rule contains nothing" in

          (* print_endline "(~_~)1.5"; (*Jumpei*) *)

    let fm2 = itlist mk_exists (List.map string_of_var (VarSet.elements exvars)) fm in
        subst subfn fm2

and fol_of_rterm r (idb:symtable) (cnt:colnamtab)=

      (* printf "(~_~)1.3.1: fol_of_rterm: "; (*Jumpei*) *)
      (* printf "rterm => %s\n\n" (string_of_rterm r); *)

    let cols =
        try Hashtbl.find cnt (symtkey_of_rterm r)
        with Not_found -> raise(SemErr ("Not found in cnt the atom "^string_of_rterm r))
        in

    let varlst = get_rterm_varlist r in
    let excols = List.fold_right2 (fun col var l -> if (is_anon var) then col::l else l) cols varlst [] in
    (* create substitution function convert anonymous variables to named variable with alias,
    they will be existential varialbes  *)

    let subfn = List.fold_right2 (fun col var l-> if (is_anon var) then l else (col |-> Fol.Var (string_of_var var)) l) cols varlst undefined in

    let fm = if Hashtbl.mem idb (symtkey_of_rterm r) then
    begin
    (* in the case that the predicate is of idb relation, need to recursive construct FO formula for it *)

      (*
        printf "(~_~)1.2.3.1: fol_of_rterm"; (* Jumpei *)
        printf "symtkey_of_rtem => (%s, %d)\n\n" (fst @@ symtkey_of_rterm r) (snd @@ symtkey_of_rterm r);
      *)

    fol_of_symtkey idb cnt (symtkey_of_rterm r)
    end
    else
    begin

      (* print_endline "(~_~)1.2.3.2: fol_of_rterm"; (* Jumpei *) *)

    (* if this predicate is of an edb relation, just need to call by its name *)
    Atom(R(get_rterm_predname r, (List.map (fun x -> Fol.Var x) cols)))
    end
    in

        (* print_endline "(~_~)1.2.4: fol_of_rterm";  (* Jumpei *) *)

    let fm2 = itlist mk_exists excols fm in
    subst subfn fm2

and fol_of_eq eq = match eq with
    Equal(exp1, exp2) -> Atom(R("=",[folterm_of_vterm exp1; folterm_of_vterm exp2]))
    | _ -> failwith "not a equality"

and fol_of_ineq ineq = match ineq with
    Ineq(str, exp1, exp2) -> Atom(R(str,[folterm_of_vterm exp1; folterm_of_vterm exp2]))
    | _ -> failwith "not a inequality"
;;

(* ---------------------------------------------------------------------------------------
  @author: Vandang Tran
  take a query term and rules of idb relations stored in a symtable, generate a FO formula for it
  added log mode by Jumepi Tanaka
-----------------------------------------------------------------------------------------*)
let fol_of_query (idb:symtable) (cnt:colnamtab) (query:rterm) log =
    (* query is just a rterm which is a predicate therefore need to create a new temporary rule for this query term
    for example if query is q(X,Y,_,5) we create a rule for it: _dummy_(X,Y) :- q(X,Y,_,Z), Z=5. (_dummy_ is a fixed name in the function rule_of_query)
    *)

    let qrule = rule_of_query query idb in
            if !log
            then begin
              print_endline "  1. Ast2fol.fol_of_query => qrule:";
              Printf.printf "  %s\n" (string_of_stt qrule)
            end
            else
              ();

    (* qrule is in the form of _dummy_(x,y) :- query_predicate(x,y), x=1 *)
        let local_idb = Hashtbl.copy idb in
        let local_cnt = Hashtbl.copy cnt in
        (* because insert a temporary dummy qrule, we should work with a local variable of idb *)
        symt_insert local_idb qrule;
        (* add the variable of the head of the qrule to local_cnt *)

        let key = symtkey_of_rule qrule in
            if !log
            then begin
              print_endline "  2. Ast2fol.fol_of_query => key:";
              Printf.printf "  (%s, %d)\n\n" (fst key) (snd key)
            end
            else
              ();

        if not (Hashtbl.mem local_cnt key) then
        Hashtbl.add local_cnt key (List.map string_of_var (get_rterm_varlist (rule_head qrule)));

            if !log
            then begin
              print_endline "  3. Ast2fol.fol_of_query => local_cnt:";
              print_colnamtab local_cnt; Printf.printf "\n";

              print_endline "  4. Ast2fol.fol_of_query => local_idb:";
              print_symtable local_idb; Printf.printf "\n";

              print_endline "  5. Ast2fol.fol_of_query => symtkey_of_rterm (rule_head qrule):";
              let key2 = symtkey_of_rterm (rule_head qrule) in
              Printf.printf "  (%s, %d)\n\n" (fst key2) (snd key2);

              print_endline "  6. Ast2fol.fol_of_query => string_of_symtkey key:";
              Printf.printf "  %s\n\n" (Utils.string_of_symtkey key)
            end
            else
              ();

        (try Hashtbl.find local_cnt key
        with Not_found -> raise(SemErr("Not found in cnt the atom " ^ Utils.string_of_symtkey key ));
        , fol_of_symtkey local_idb local_cnt (Utils.symtkey_of_rterm (rule_head qrule)))


(** take a query term and rules of idb relations stored in a symtable, generate a FO formula for it *)
let fol_of_query2 (idb:symtable) (cnt:colnamtab) (query:rterm) =
    (* query is just a rterm which is a predicate therefore need to create a new temporary rule for this query term
    for example if query is q(X,Y,_,5) we create a rule for it: _dummy_(X,Y) :- q(X,Y,_,Z), Z=5. (_dummy_ is a fixed name in the function rule_of_query)
    *)

    let qrule = rule_of_query query idb in
            (*
            (* Jumpei Tanaka *)
            print_endline "  Ast2fol.fol_of_query => (o_o)1/~~ qrule:";
            Printf.printf "  %s\n" (string_of_stt qrule);
            *)

    (* qrule is in the form of _dummy_(x,y) :- query_predicate(x,y), x=1 *)
        let local_idb = Hashtbl.copy idb in
        let local_cnt = Hashtbl.copy cnt in
        (* because insert a temporary dummy qrule, we should work with a local variable of idb *)
        symt_insert local_idb qrule;
        (* add the variable of the head of the qrule to local_cnt *)

        let key = symtkey_of_rule qrule in
            (*
            (* Jumpei Tanaka *)
            print_endline "  Ast2fol.fol_of_query => (o_o)2/~~ key:";
            Printf.printf "  (%s, %d)\n\n" (fst key) (snd key);
            *)

        if not (Hashtbl.mem local_cnt key) then
        Hashtbl.add local_cnt key (List.map string_of_var (get_rterm_varlist (rule_head qrule)));
            (*
            (* Jumpei Tanaka *)
            print_endline "  Ast2fol.fol_of_query => (o_o)3/~~ local_cnt:";
            Utils.print_colnamtab local_cnt; Printf.printf "\n";

            print_endline "  Ast2fol.fol_of_query => (o_o)4/~~ local_idb:";
            print_symtable local_idb; Printf.printf "\n";

            print_endline "  Ast2fol.fol_of_query => (o_o)5/~~ symtkey_of_rterm (rule_head qrule):";
            let key2 = symtkey_of_rterm (rule_head qrule) in
            Printf.printf "  (%s, %d)\n\n" (fst key2) (snd key2);
            *)

        (try Hashtbl.find local_cnt key with
          Not_found -> raise(SemErr("Not found in cnt the atom "^string_of_symtkey key));
        , fol_of_symtkey local_idb local_cnt (symtkey_of_rterm (rule_head qrule))
        )





(* ---------------------------------------------------------------------------------------
  @author: Jumpei Tanaka
  take ast of schemas and constraints and generate FO sentence of all constraints
------------------------------------------------------------------------------------------*)
let constraint_sentence_of_stt prog_schema prog_const log =

    (* put schemas into symtable *)
    let schema = extract_schema prog_schema in

    let idb = extract_idb prog_const in
        if !log
        then begin
          print_endline "--- function: constraint_sentence_of_stt ---";
          print_endline "schema:"; print_symtable schema; Printf.printf "\n";
          print_endline "idb:"; print_symtable idb; Printf.printf "\n";
          (* Printf.printf "Hashtbl.mem schema (symtkey_of_rterm Expr.get_empty_pred) = %b\n" ( Hashtbl.mem schema (symtkey_of_rterm Expr.get_empty_pred)); *)
          (* Printf.printf "Hashtbl.mem idb (symtkey_of_rterm Expr.get_empty_pred) = %b\n" ( Hashtbl.mem idb (symtkey_of_rterm Expr.get_empty_pred)); *)
        end
        else
          ();

    if Hashtbl.mem idb (symtkey_of_rterm Expr.get_empty_pred)
    then begin
        preprocess_rules idb;
          if !log
          then begin
            print_endline "preprocessed idb:"; print_symtable idb; Printf.printf "\n";
          end
          else
            ();
        let cnt = build_colnamtab schema idb in

        let tmp_log = ref false in
        Imp(snd (fol_of_query idb cnt get_empty_pred tmp_log), False)
    end
    else
        True
;;


(* @author: Jumpei Tanaka *)
(* generate FOL senetence from AST of coers having Source_schema and Target_schema *)
let sentence_of_stt_coers prog_schema prog_rules goal log =

    let schema = Utils.extract_schema prog_schema in
    let idb = Utils.extract_idb prog_rules in
    preprocess_rules idb;
    let cnt = build_colnamtab schema idb in
    let sentence = snd (fol_of_query idb cnt goal log) in

  sentence
;;

(* @author: Jumpei Tanaka *)
(* generate FOL senetence from AST of BIRDS having Source and View *)
let sentence_of_stt_birds prog_schema prog_rules goal log =

    let edb = extract_edb prog_schema in
    let view_rtt = get_schema_rterm (get_view prog_schema) in
    symt_insert edb (Rule(view_rtt,[]));
    let idb = Utils.extract_idb prog_rules in
    preprocess_rules idb;
    let cnt = build_colnamtab edb idb in
    let sentence = snd (fol_of_query idb cnt goal log) in

  sentence
;;

(* ------------------------------------------------------------------------
@author: Vandang Tran
take a view update datalog program and generate the FO sentence of checking whether all delta relations are disjoint
---------------------------------------------------------------------- *)
let disjoint_delta_sentence_of_stt (debug:bool) prog =
    let edb = extract_edb prog in
    (* need to change the view (in query predicate) to a edb relation *)
    let view_rt = get_schema_rterm (get_view prog) in
    (* need to convert the view to be an edb relation *)
    symt_insert edb (Rule(view_rt,[]));
    let idb = extract_idb prog in
    symt_remove idb (symtkey_of_rterm view_rt);

    preprocess_rules idb;
    if debug then (
        print_endline "_____preprocessed datalog rules_______";
        print_symtable idb;
        print_endline "______________\n";
    ) else ();

    let cnt = build_colnamtab edb idb in

    let delta_rt_lst = get_delta_rterms prog in
    (* get each pair of delta relations from the delta relation lst delta_rt_lst *)

    let delta_pair_lst =
        let pair_of_delta_insert lst ins_rel =
            let del_rels = List.filter (is_delta_pair ins_rel) delta_rt_lst in
            if (List.length del_rels = 0) then lst else (ins_rel, (List.hd del_rels))::lst in
        List.fold_left pair_of_delta_insert [] delta_rt_lst in

    (* get the emptiness FO sentence of a relation *)
    let disjoint_fo_sentence ins_rel del_rel =
        let cols = List.map string_of_var (get_rterm_varlist ins_rel) in

        let b =
            And(
                snd (fol_of_query2 idb cnt ins_rel),
                snd (fol_of_query2 idb cnt del_rel)
               )
        in
        itlist mk_exists cols b in
        (* itlist mk_exists cols (And(snd (fol_of_query idb cnt ins_rel), snd (fol_of_query idb cnt del_rel))) in *)

    let djsjoint_sen_lst = List.map (fun (r1,r2) -> disjoint_fo_sentence r1 r2) delta_pair_lst in
    Prop.list_disj djsjoint_sen_lst
;;
