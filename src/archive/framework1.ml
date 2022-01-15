(* @author: Jumpei Tanaka *)

(* open Lib;; *)
open Printf;;
open Expr;;
open Utils;;
open Tools;;
open Preperation;;
open Disjoint;;
open Consistency;;

let steps ast0 log timeout dbschema physical =
  (* ************************************************ *)
  (* Step 1: Preparation                               *)
  (* ************************************************ *)
  print_endline "(* ************************************************ *)";
  print_endline "(* Step 1: Preparation                              *)";
  print_endline "(* ************************************************ *)";
  (* preprocess to make constraint to rule *)

  let ast = Preperation.constraint2rule ast0 in
        print_endline "AST:"; Expr.print_ast ast; printf "\n";

  (* pret list *)
  let source_pred_lst = Preperation.get_source_preds ast log in (* pred (rterm) in source schema *)

  let target_pred_lst = Preperation.get_target_preds ast log in (* pred (rterm) in target schema *)
  let head_pred_lst = Preperation.get_head_preds ast log in (* pred (rterm) in head relations *)
  let init_pred_lst = Preperation.get_init_preds source_pred_lst target_pred_lst head_pred_lst log in (* pred (rterm) in initial relations *)
  let evolved_pred_lst = Preperation.get_evolved_preds target_pred_lst init_pred_lst log in  (* pred (rterm) of evolved relations *)

  (* rel list *)
  let pk_lst = Preperation.get_pk_pred ast0 log in
  let source_rels = get_rels source_pred_lst in
  let target_rels = get_rels target_pred_lst in

    printf "source_rels => [";
    let print_el s = printf "%s; " s in List.iter print_el source_rels;
    printf "]\n";

    printf "target_rels => [";
    let print_el s = printf "%s; " s in List.iter print_el target_rels;
    printf "]\n";

  let source_ins_rels = Preperation.get_source_ins_rels ast source_rels log in
  let source_del_rels = Preperation.get_source_del_rels ast source_rels log in

  (* ASTs *)
  let ast_schemas = Preperation.get_schemas ast log in  (* schema definition *)
  let ast_constraint = Preperation.get_constraints ast log in  (* rules of constraints *)
  let ast_schevo = Preperation.get_schevo_rules ast target_pred_lst source_pred_lst log in (* rules of schema evolution *)
  let ast_bwd = Preperation.get_bwd_rules ast ast_schemas ast_constraint ast_schevo log in  (* rules of backward propagation *)

  let evolved_bwd_pred_lst = Preperation.get_evolved_bwd_preds evolved_pred_lst ast_bwd log in (* pred (rterm) of evolved relations with backward propagation rules *)
  let case1_pred_lst = Preperation.get_case1_preds target_pred_lst init_pred_lst evolved_bwd_pred_lst log in (* pred (rterm) of evolved relations without backward propagation rules *)

  let schema_mpg_lst = Preperation.schema_mapping ast log in (* mapping of schema and relation *)

  (* check of a written strategy *)
  let prep_check_lst = Preperation.check2 ast_bwd evolved_pred_lst source_rels log in
  if (List.length prep_check_lst) != 0
    then (
          List.iter (printf "%s ") prep_check_lst;
          exit 0);
  print_endline "*** Rules are linear and monotonic.*** \n";

  (* Rule for each co-existence of schemas *)
  print_endline "*** Rule for each co-existence of schemas *** \n";
  let evolved_bwd_rel_lst = get_rels evolved_bwd_pred_lst in
  let sttl_delta_pair = Preperation.get_delta_pair ast_schemas ast_constraint ast_schevo ast_bwd evolved_bwd_pred_lst log in


  (* check disjointness *)
  print_endline "*** Disjointness check.*** \n";
  let prep_disjoint_lst = Preperation.prep_disjoint sttl_delta_pair log in
  let disjointness_lst = Disjoint.check_disjoint prep_disjoint_lst log timeout in

  if List.length disjointness_lst <> 0
    then begin
      let e = printf "%s " in
      List.iter e disjointness_lst;
      exit 0
      end
    else
    print_endline "Disjointness is satisfied.";

  (* ************************************************ *)
  (* Step 2: Checking consistency                     *)
  (* ************************************************ *)

  print_endline "\n(* ************************************************ *)";
  print_endline "(* Step 2: Checking consistency                     *)";
  print_endline "(* ************************************************ *)";

  let consistency_lst = Consistency.check_insdel ast_schemas ast_constraint ast_schevo ast_bwd source_pred_lst evolved_bwd_pred_lst source_ins_rels source_del_rels target_pred_lst log timeout in

  if List.length consistency_lst !=0
  then begin
   let e = printf "%s " in
   List.iter e consistency_lst;
   exit 0
  end
  else
    print_endline "Consistency is satisfied.";


  (* *************************************************************************  *)
  (* Step 3: Source schema - Initial relations: derivation of views and schemas *)
  (* ************************************************************************** *)
  print_endline "\n(* ************************************************************************ *)";
  print_endline "(* Step 3: Source schema - Initial relations: derivation of views and schemas *)";
  print_endline "(* ************************************************************************** *)";

  (* derive get_init and putdelta_init *)
  let init_ast_lst = View_init.derivation_init_birds ast_schemas ast_constraint init_pred_lst log in

  (* base relations stt list *)
  let base_rel_sttl = View_init.get_base_rels init_ast_lst in

  (* exeucte birds and generate SQL *)
  let schema_mpg_init_lst = View_init.mpg_init init_pred_lst log physical in
  let all_schema_mpg_init_lst = schema_mpg_lst @ schema_mpg_init_lst in
  print_endline "run BIRDS for initial relations...";
  let birds_init_lst = execute_birds init_ast_lst log dbschema false in (* set true to make verificaiton by BIRDS *)
  let birds_sql_init_lst = List.map snd birds_init_lst in
  let birds_status_init_lst = List.filter (fun x -> match x with 0 -> false | _ -> true) (List.map fst birds_init_lst) in

  let dummy =
    if (List.length birds_status_init_lst) != 0
    then begin printf ""; end
    else begin
      let e = rewrite_sql_schemas log dbschema all_schema_mpg_init_lst in
      List.iter e birds_sql_init_lst;
      end
  in


  (* **************************************************************** *)
  (* Step 4-1: Target schema - Evolutional relations: no backward propagation *)
  (* **************************************************************** *)
  print_endline "\n(* ********************************************************************** *)";
  print_endline "(* Step 4-1: Target schema - Evolutional relations: no backward propagation *)";
  print_endline "(* ************************************************************************ *)";

  (* derive get_1 and putdelta_1 *)
  let case1_ast_lst = View_evo_case1.derivation_case1_birds ast_schemas ast_constraint ast_schevo case1_pred_lst base_rel_sttl log in

  (* exeucte birds and generate SQL *)
  let schema_mpg_1_lst = View_evo_case1.mpg_1 case1_pred_lst log physical in
  let all_schema_mpg_1_lst = schema_mpg_lst @ schema_mpg_init_lst @ schema_mpg_1_lst in
  (* print_endline "run BIRDS for evolved relations of case1..."; *)
  let birds_1_lst = execute_birds case1_ast_lst log dbschema false in (* set true to make verificaiton by BIRDS *)
  let birds_sql_1_lst = List.map snd birds_1_lst in
  let birds_status_1_lst = List.filter (fun x -> match x with 0 -> false | _ -> true) (List.map fst birds_1_lst) in

  let dummy =
    if (List.length birds_status_1_lst) != 0
    then begin printf ""; end
    else begin
      let e = rewrite_sql_schemas log dbschema all_schema_mpg_1_lst in
      List.iter e birds_sql_1_lst;
      end
  in

  (* **************************************************************** *)
  (* Step 4-2: Evolutional relations: case2                           *)
  (*   schema evolution and backward propagation                      *)
  (* **************************************************************** *)
  print_endline "\n(* **************************************************************** *)";
  print_endline "(* Step 4-2: Target schema - Evolutional relations                  *)";
  print_endline "(*   schema evolution and backward propagation                      *)";
  print_endline "(* **************************************************************** *)";

  (* derive get_2 and putdelta_2 *)
  let case2_ast_lst = View_evo_case2.derivation_case2_birds ast_schemas ast_constraint ast_schevo ast_bwd evolved_bwd_pred_lst base_rel_sttl source_rels source_ins_rels source_del_rels source_pred_lst pk_lst log timeout in

  (* exeucte birds and generate SQL *)
  let schema_mpg_2_diff = View_common.mpg_diff evolved_bwd_pred_lst log physical in
  let all_schema_mpg_2_lst = schema_mpg_lst @ schema_mpg_init_lst @ schema_mpg_2_diff in
  let birds_2_lst = execute_birds case2_ast_lst log dbschema true in (* set true to make verificaiton by BIRDS *)
  let birds_sql_2_lst = List.map snd birds_2_lst in
  let birds_status_2_lst = List.filter (fun x -> match x with 0 -> false | _ -> true) (List.map fst birds_2_lst) in

  let dummy =
    if (List.length birds_status_2_lst) != 0
    then begin printf ""; end
    else begin
      let e = rewrite_sql_schemas log dbschema all_schema_mpg_2_lst in
      List.iter e birds_sql_2_lst;
      end
  in


  (* **************************************************************** *)
  (* Show final result                                                *)
  (* **************************************************************** *)
  let birds_result = birds_init_lst @ birds_1_lst @ birds_2_lst in
  View_common.show_result birds_result;
;;
