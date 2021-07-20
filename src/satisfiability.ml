(* @author: Jumpei Tanaka *)

open Lib;;
open Formulas;;
open Expr;;
open Utils;;
open Tools;;
open Fol;;
open Printf;;
open Datalog2fol;;

(* @author: Vandang Tran *)
let stype_to_lean_type st = match st with
    (* | Sint -> "ℤ" *)
    | Sint -> "int"
    (* | Sreal -> "ℝ" *)
    (* | Sreal -> "real" *)
    | Sreal -> "rat"
    | Sbool -> "Prop"
    | Sstring -> "string"


(* @author: Vandang Tran *)
let gen_lean_code_for_theorems thms =
    "import bx

local attribute [instance] classical.prop_decidable

" ^ String.concat "\n\n" (List.map (fun x ->  x ^ ":=
    begin
    z3_smt
    end") thms)
    (* try{super {max_iters := 200, timeout := 200000}} *)
;;


(* @author: Jumpei Tanaka *)
(* insertion: reform schemas to replace relatiosn which occurs as delta relations in backward rules and eliminate others *)
let reform_schema_delta_ins prog_schema delta_lst =

  let rec _0_reform_schema prog_schema delta_lst = match prog_schema with
    | Prog sttl -> _1_reform_schema sttl
    and _1_reform_schema sttl = match sttl with
      | [] -> []
      | hd::rest -> (_2_reform_schema hd) @ (_1_reform_schema rest)
    and _2_reform_schema hd = match hd with
      | Source_schema (schema, name, verlst) ->
          if List.mem name delta_lst
          then
            [hd] @ [Source_schema (schema, ("ins_" ^ name), verlst) ]
          else
            [hd]
      | Target_schema (schema, name, verlst) ->
          if List.mem name delta_lst
          then
            [hd] @ [Target_schema (schema, ("ins_" ^ name), verlst) ]
          else
            [hd]
      | _ -> invalid_arg "function reform_schema called without Source_schema or Target_schema"
  in

  let result = Prog (_0_reform_schema prog_schema delta_lst) in
result
;;


(* @author: Jumpei Tanaka *)
(* deletion: reform schemas to replace relatiosn which occurs as delta relations in backward rules and eliminate others *)
let reform_schema_delta_del prog_schema delta_lst =

  let rec _0_reform_schema prog_schema delta_lst = match prog_schema with
    | Prog sttl -> _1_reform_schema sttl
    and _1_reform_schema sttl = match sttl with
      | [] -> []
      | hd::rest -> (_2_reform_schema hd) @ (_1_reform_schema rest)
    and _2_reform_schema hd = match hd with
      | Source_schema (schema, name, verlst) ->
          if List.mem name delta_lst
          then
            [hd] @ [Source_schema (schema, ("del_" ^ name), verlst) ]
          else
            []
      | Target_schema (schema, name, verlst) ->
          if List.mem name delta_lst
          then
            [hd] @ [Target_schema (schema, ("del_" ^ name), verlst) ]
          else
            []
      | _ -> invalid_arg "function reform_schema called without Source_schema or Target_schema"
  in

  let result = Prog (_0_reform_schema prog_schema delta_lst) in
result
;;


(* @author: Jumpei Tanaka *)
(* transform relations in source_schema and target_schema in program to a list of functions from product of n (the arity) types to Prop *)
let schemas_to_lean_func_types prog = match prog with
    Prog sttlst ->
    (* currently just set all the types are int (ℤ) *)
    let p_el funcs s = match s with
        Rule _ -> funcs
        | Query _ -> funcs
        | Constraint _ -> funcs
        | Pk _ -> funcs
        | Source (name, lst)
        | View (name, lst)
        | Source_schema (_, name, lst)
        | Target_schema (_, name, lst) -> ( name ^ ": " ^ String.concat " → " ( List.map (fun (col,typ) -> stype_to_lean_type typ) lst) ^ " → Prop" )::funcs
        in
    List.fold_left p_el [] sttlst
;;


(* @author: Jumpei Tanaka *)
(* reform delta_relations to relations with ins_/del_ *)
let reform_prog_insdel prog =

  let rec _0_reform prog = match prog with
    | Prog sttl -> _1_reform sttl

    and _1_reform sttl = match sttl with
      | [] -> []
      | hd::rest -> (_2_reform hd) @ (_1_reform rest)

    and _2_reform hd = match hd with
      | Rule (Pred(rel, varlst), bodylst)
          ->  let bosylst_delta = _3_reform bodylst in
              [Rule (Pred(rel, varlst),bosylst_delta)]
      | Rule (Deltainsert(rel, varlst), bodylst)
          ->  let rel_ins = "ins_" ^ rel in
              let bodylst_delta = _3_reform bodylst in
              [Rule (Pred(rel_ins, varlst), bodylst_delta)]
      | Rule (Deltadelete(rel, varlst), bodylst)
          ->  let rel_del = "del_" ^ rel in
              let bodylst_delta = _3_reform bodylst in
              [Rule (Pred(rel_del, varlst), (_3_reform bodylst))]
      | _ -> invalid_arg "function eform_prog_insdel called without a rule"

    and _3_reform bodylst = match bodylst with
      | [] -> []
      | hd::rest -> (_4_reform hd) @ (_3_reform rest)

   and _4_reform hd = match hd with
      | Rel (Pred(rel, varlst)) -> [hd]
      | Rel (Deltainsert(rel, varlst)) -> [Rel (Pred (("ins_" ^ rel), varlst))]
      | Rel (Deltadelete(rel, varlst)) -> [Rel (Pred (("del_" ^ rel), varlst))]
      | Not (Pred(rel, varlst)) -> [hd]
      | Not (Deltainsert(rel, varlst)) -> [Not (Pred (("ins_" ^ rel), varlst))]
      | Not (Deltadelete(rel, varlst)) -> [Not (Pred (("del_" ^ rel), varlst))]
      | _ -> [hd]
  in

  let result = Prog (_0_reform prog) in
result
;;

(* if view is t(valst), add ins_t(varlst), del_t(var_lst), tmp_t(varlst) and ins_ttl_t(varlst)as Source *)
let add_source schema_ttl  =

  let rec add schema = match schema with
    | [] -> []
    | hd::rest -> (_1_add hd) @ (add rest)
    and _1_add stt = match stt with
      | View (rel, varlst) ->
        [ Source ( ("ins_" ^ rel), varlst);
          Source ( ("del_" ^ rel), varlst);
          Source ( ("tmp_" ^ rel), varlst);
          Source ( ("ins_ttl_" ^ rel), varlst)
        ]
      | _ -> []
  in

  let added_source_sttl = add (get_sttl schema_ttl) in
added_source_sttl
;;

(* exculde rules which head is view *)
let filter_undef ast_ttl =

  let rec filter view_name putdelta_ttl_sttl = match putdelta_ttl_sttl with
    | [] -> []
    | hd::rest -> (_1_filter view_name hd) @ (filter view_name rest)
    and _1_filter view_name stt = match stt with
      | Rule (Pred(rel, _), _) ->
          if (rel = view_name)
          then []
          else [stt]
      | _ -> [stt]
  in

  let view_name = get_view_name ast_ttl  in
  let ast_undef = Prog (filter view_name (get_sttl ast_ttl)) in

ast_undef
;;


(* @author: Jumpei Tanaka *)
(* run lean to check FOL of consistency and return result *)
let check_fol_of_consistency prog_schema_all prog_const prog_l prog_r evolved_pred_lst =

  (* temporally set log *)
  let temp_log = ref false in

  let rec check_fol return prog_const prog_l prog_r evolved_pred_lst = match evolved_pred_lst with
    | [] -> []
    | hd::rest -> (_1_check_fol return prog_const prog_l prog_r hd)
                  @ (check_fol return prog_const prog_l prog_r rest)

    and _1_check_fol return prog_const prog_l prog_r hd = match hd with
        | Pred(rel, varlst) -> _2_check_fol return prog_const prog_l prog_r rel varlst
        | _ -> invalid_arg "function check_fol without Pred"

    and _2_check_fol return prog_const prog_l prog_r rel varlst =
        (* generate left and right datalog rules as AST by target evolved predicate *)
        let pred_l = Pred ((rel ^ "_newleft"), varlst) in
        let pred_r = Pred ((rel ^ "_newright"), varlst) in
        let pred_goal = Pred (rel, varlst) in
        let prog_l_pred = get_one_query prog_l pred_l in
        let prog_r_pred = get_one_query prog_r pred_r in

            printf "pred_l: %s\n" (string_of_rterm pred_l);
            printf "pred_r: %s\n" (string_of_rterm pred_r);
            print_endline "prog_l_pred:"; Expr.print_ast prog_l_pred; printf "\n";
            print_endline "prog_r_pred:"; Expr.print_ast prog_r_pred; printf "\n";

        (* transform left and right ASTs into lean program *)
        let lean_schema_all = String.concat " " (List.map (fun x -> "{"^x^"}") (schemas_to_lean_func_types prog_schema_all)) in
        let lean_left = sentence_of_stt_coers prog_schema_all prog_l_pred pred_l temp_log in
        let lean_right = sentence_of_stt_coers prog_schema_all prog_r_pred pred_r temp_log in

        let cols = List.map string_of_var varlst in
        let fol_of_consistency =
          "theorem consistency " ^ lean_schema_all ^ ":\n"
          ^ (Fol_ex.lean_string_of_fol_formula
              (Imp (
                    constraint_sentence_of_stt prog_schema_all prog_const temp_log,
                    itlist mk_exists cols (Imp (And (lean_left, (Not lean_right)), False))
                  )
              )
            )
        in

(*
        let fol_of_consistency =
          "theorem consistency " ^ lean_schema_all ^ ":\n"
          ^ (Fol_ex.lean_string_of_fol_formula
              (Imp (
                    constraint_sentence_of_stt prog_schema_all prog_const temp_log,
                    generalize (Imp (And (lean_left, (Not lean_right)), False))
                  )
              )
            )
        in
*)

      let lean_fol_of_consistency = gen_lean_code_for_theorems [fol_of_consistency] in

      (* printf "%s\n" fol_of_consistency; *)
      (* return derived lean program for each target evolved predicate *)
      let result = return @ [(pred_goal, lean_fol_of_consistency)] in
      result
  in

  let result = check_fol [] prog_const prog_l prog_r evolved_pred_lst in

result
;;

(* ===================================================================================== *)
(* ===================================================================================== *)

(* @author: Jumpei Tanaka *)
(* generate a definition of consistency of co-existence strategy by Jumpei Tanaka *)
let lean_consistency prog_schema prog_const prog_l prog_r bwd_delta_ins_lst bwd_delta_del_lst const_delta_ins_lst const_delta_del_lst evolved_pred_lst log =

    (* schema for constraints consists of:
        relations in source,
        relations in target but not in delta relaitons consisting backward rules, and
        delta relations consisting backward rules *)
    let prog_schema_bwd_ins = reform_schema_delta_ins prog_schema bwd_delta_ins_lst in
    let prog_schema_bwd_del = reform_schema_delta_del prog_schema bwd_delta_del_lst in
    let prog_schema_const_ins = reform_schema_delta_ins prog_schema const_delta_ins_lst in
    let prog_schema_const_del = reform_schema_delta_del prog_schema const_delta_del_lst in

    let prog_schema_all =
        Prog (
          unique_element (
            to_sttlst (
              List.fold_left merge_ast (Prog [])
              [prog_schema_bwd_ins; prog_schema_bwd_del; prog_schema_const_ins; prog_schema_const_del] )))
    in

    (* reform +/- in prog_schema by ins_/del_ *)
    let reformed_prog_const = reform_prog_insdel prog_const in
    let reformed_prog_l = reform_prog_insdel prog_l in
    let reformed_prog_r = reform_prog_insdel prog_r in

        if !log
        then begin
          print_endline "prog_schema_all:"; Expr.print_ast prog_schema_all; printf "\n";
          (* print_endline "reformed_prog_const:"; Expr.print_ast reformed_prog_const; printf "\n"; *)
          (* print_endline "reformed_prog_l:"; Expr.print_ast reformed_prog_l; printf "\n"; *)
          (* print_endline "reformed_prog_r:"; Expr.print_ast reformed_prog_r; printf "\n"; *)
        end
        else
          ();

    let result_temp = check_fol_of_consistency prog_schema_all reformed_prog_const reformed_prog_l reformed_prog_r evolved_pred_lst in

    let result = result_temp in

result
;;


(* @author: Jumpei Tanaka *)
(* generate a definition of consistency of co-existence strategy by Jumpei Tanaka *)
let lean_consistency ast_consis ast_constraint_consis target_pred goal log =

  let temp_log = ref true in   (* temporally set log *)

  print_endline "deriving schema for lean-consistency";
  let lean_schema_all = String.concat " " (List.map (fun x -> "{"^x^"}") (schemas_to_lean_func_types ast_consis)) in

  print_endline "deriving fol of lean-consistency";
  let consis = sentence_of_stt_birds ast_consis ast_consis goal temp_log in

  print_endline "deriving colums of lean-consistency";
  let cols = List.map string_of_var (get_varlst_from_pred target_pred) in

  print_endline "deriving lean program of lean-consistency";
  let fol_of_consistency =
      "theorem consistency " ^ lean_schema_all ^ ":\n"
      ^ (Fol_ex.lean_string_of_fol_formula
          (Imp (
                constraint_sentence_of_stt ast_consis ast_constraint_consis temp_log,
                generalize (Imp (consis, False) )
      (*            itlist mk_exists cols (Imp (consis, False) ) *)
               )
          )
        )

  in

  let lean_fol_of_consistency = gen_lean_code_for_theorems [fol_of_consistency] in

lean_fol_of_consistency
;;


(* @author: Jumpei Tanaka *)
(* run lean to check FOL of undef and return result *)
let lean_diff ast_ttl schema_ttl constraint_ttl putdelta_ttl aux_deltains log =

  let temp_log = ref false in   (* temporally set log *)

  (* if view is t(varlst), add ins_t(varlst), del_t(var_lst), tmp_t(varlst) and ins_ttl_t(varlst)as Source *)
  let additional_source = add_source schema_ttl in
  let schema_all = Prog (
                    unique_element @@
                       (get_sttl schema_ttl) @
                       additional_source
                  )
  in

  let lean_schema_all = String.concat " " (List.map (fun x -> "{"^x^"}") (schemas_to_lean_func_types schema_all)) in
  let ast_constraitnt = merge_ast constraint_ttl putdelta_ttl in

  let ast_undef = filter_undef ast_ttl in
  let lean_insaux = sentence_of_stt_birds schema_all ast_undef aux_deltains temp_log in

  let fol_of_undef =
      "theorem diff " ^ lean_schema_all ^ ":\n"
      ^ (Fol_ex.lean_string_of_fol_formula
          (Imp (
                constraint_sentence_of_stt schema_all ast_constraitnt temp_log,
                generalize (Imp (lean_insaux, False) )
               )
          )
        )

  in

  let lean_fol_of_diff = gen_lean_code_for_theorems [fol_of_undef] in

lean_fol_of_diff
;;

(*
(* @author: Jumpei Tanaka *)
(* run lean to check FOL of undef and return result *)
let lean_undef ast_ttl schema_ttl constraint_ttl putdelta_ttl aux_deltains log =

  let temp_log = ref false in   (* temporally set log *)

  (* if view is t(varlst), add ins_t(varlst), del_t(var_lst), tmp_t(varlst) and ins_ttl_t(varlst)as Source *)
  let additional_source = add_source schema_ttl in
  let schema_all = Prog (
                    unique_element @@
                       (get_sttl schema_ttl) @
                       additional_source
                  )
  in

  let lean_schema_all = String.concat " " (List.map (fun x -> "{"^x^"}") (schemas_to_lean_func_types schema_all)) in
  let ast_constraitnt = merge_ast constraint_ttl putdelta_ttl in

  let ast_undef = filter_undef ast_ttl in
  let lean_insaux = sentence_of_stt_birds schema_all ast_undef aux_deltains temp_log in

  let fol_of_undef =
      "theorem undef " ^ lean_schema_all ^ ":\n"
      ^ (Fol_ex.lean_string_of_fol_formula
          (Imp (
                constraint_sentence_of_stt schema_all ast_constraitnt temp_log,
                generalize (Imp (lean_insaux, False) )
               )
          )
        )

  in

  let lean_fol_of_undef = gen_lean_code_for_theorems [fol_of_undef] in

lean_fol_of_undef
;;
*)
