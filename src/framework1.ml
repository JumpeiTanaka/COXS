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

  (* retrieve constraint_core *)
  let ast_constraint_core = Preperation.get_constraints ast0 log in

  (* transform pk constraint to rules of constraint *)
  let ast = Preperation.constraint2rule ast0 in
        print_endline "AST:"; Expr.print_ast ast; printf "\n";

  let ast_schemas = Preperation.get_schemas ast log in  (* rules of constraints *)

  let ast_constraint_pk =
    let all_constraints = Preperation.get_constraints ast log in
    subtract_ast all_constraints ast_constraint_core
  in

  let ast_constraint = merge_ast ast_constraint_core ast_constraint_pk in  (* rules of constraints *)


      print_endline "ast_constraint_pk:"; Expr.print_ast ast_constraint_pk; printf "\n";
      print_endline "ast_constraint_core:"; Expr.print_ast ast_constraint_core; printf "\n";
      print_endline "ast_constraint:"; Expr.print_ast ast_constraint; printf "\n";


  let ast_rules = subtract_ast (subtract_ast ast ast_schemas) ast_constraint in

    (* print_endline "ast_rules : "; Expr.print_ast ast_rules; printf "\n"; (*Jumpei*) *)

  (* list of preds *)
  let source_pred_lst = Preperation.get_source_preds ast log in (* pred (rterm) in source schema *)
  let target_pred_lst = Preperation.get_target_preds ast log in (* pred (rterm) in target schema *)
  let target_pred_1 = List.hd target_pred_lst in

    (* printf "target_pred_1 = %s\n" (string_of_rterm @@ List.hd target_pred_1); *)



  (* list of rels *)
  let pk_lst = Preperation.get_pk_pred ast0 log in printf "\n";
  let source_rels = get_rels source_pred_lst in

        printf "source_rels => [";
        let print_el s = printf "%s; " s in List.iter print_el source_rels;
        printf "]\n"; 

  let target_rel_1 = get_rel_from_pred target_pred_1 in

        printf "target_rel_1 = %s\n" target_rel_1;


  (* --- ASTs of schemas --- *)
  let ast_schema_1 = Preperation.get_schema_twin ast source_rels target_rel_1 in

        (* print_endline "ast_schema_1: "; Expr.print_ast ast_schema_1; printf "\n"; *)

  (* --- ASTs of schema evolution --- *)
  let ast_schevo_1 = get_one_query ast target_pred_1 in

        (* print_endline "ast_schevo_1: "; Expr.print_ast ast_schevo_1; printf "\n"; *)

  (* --- ASTs of backward update transformation --- *)
  (* source predicates in each schema evolution *)
  let source_pred_lst_1 =
      let rels_body_1 = get_rels_body ast_schevo_1 in
      filter_pred_rellst source_pred_lst rels_body_1
  in

  let delta_source_pred_lst_1 = Preperation.get_delta source_pred_lst_1 in
  let rules_target_rel_1 = Preperation.get_target_delta_rules ast_rules target_rel_1 in
  let head_preds_target_1 = unique_element @@ get_preds_head (Prog (rules_target_rel_1)) in

        printf "head_preds_target_1 => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map string_of_rterm head_preds_target_1);
        printf "]\n";

  let ast_bwd_1_nos =
    let ast_1 = ast_rules in
    Preperation.get_backward_rules ast_1 delta_source_pred_lst_1
  in
      print_endline "ast_backward_1_nos: "; Expr.print_ast ast_bwd_1_nos; printf "\n";

  let ast_bwd_1 = nos2s ast_bwd_1_nos in

  (* retrive all rels in predicates *)
  let all_rels_1 =
    let ast_stgy_1 = merge_ast ast_schevo_1 ast_bwd_1 in
    unique_element @@ (get_rels_head ast_stgy_1) @ (get_rels_body ast_stgy_1)
  in

        printf "all_rels_1 => [";
        let print_el s = printf "%s; " s in
        List.iter print_el all_rels_1;
        printf "]\n";


  (* --- ASTs of constraints --- *)
  (* for the time being, all constraints are for each 1 and 2 *)
  let ast_constraint_core_1 = filter_rules_body ast_constraint_core all_rels_1 in
  let ast_constraint_pk_1 = filter_pk ast_constraint_pk target_rel_1 in
  let ast_constraint_1 = merge_ast ast_constraint_pk ast_constraint_core_1 in


        print_endline "ast_constraint_core_1: "; Expr.print_ast ast_constraint_core_1; printf "\n";
        print_endline "ast_constraint_pk_1: "; Expr.print_ast ast_constraint_pk_1; printf "\n";
        print_endline "ast_constraint_1: "; Expr.print_ast ast_constraint_1; printf "\n";


  (* --- ASTs of ech --- *)
  let ast_1_nos = List.fold_left merge_ast (Prog([])) [ast_schema_1; ast_constraint_1; ast_schevo_1; ast_bwd_1_nos] in
      print_endline "ast_1_nos:"; Expr.print_ast ast_1_nos; printf "\n";

  let ast_1 = List.fold_left merge_ast (Prog([])) [ast_schema_1; ast_constraint_1; ast_schevo_1; ast_bwd_1] in


  (* --- items for target_1 --- *)
  print_endline "Items of target_1";
  let source_pred_lst_1 = Preperation.get_source_preds ast_1 log in
  let target_pred_lst_1 = Preperation.get_target_preds ast_1 log in
  let head_pred_lst_1 = Preperation.get_head_preds ast_1 log in
  let init_pred_lst_1 = Preperation.get_init_preds source_pred_lst_1 target_pred_lst_1 head_pred_lst_1 log in
  let evolved_pred_lst_1 = Preperation.get_evolved_preds target_pred_lst_1 init_pred_lst_1 log in
  let pk_lst_1 = Preperation.get_pk_pred ast_1 log in
  let source_rels_1 = get_rels source_pred_lst_1 in
  let source_ins_rels_1 = Preperation.get_source_ins_rels ast_1 source_rels_1 log in (* normal + *)
  let source_del_rels_1 = Preperation.get_source_del_rels ast_1 source_rels_1 log in (* normal - *)
  let evolved_bwd_pred_lst_1 = Preperation.get_evolved_bwd_preds evolved_pred_lst_1 ast_bwd_1 log in
  let case1_pred_lst_1 = Preperation.get_case1_preds target_pred_lst_1 init_pred_lst_1 evolved_bwd_pred_lst_1 log in
  let schema_mpg_lst_1 = Preperation.schema_mapping ast_1 log in


  (* --- check of target_1 ---------*)
  (* check of a written strategy *)
  let prep_check_lst_1 = Preperation.check2 ast_bwd_1 evolved_pred_lst_1 source_rels_1 log in
  if (List.length prep_check_lst_1) != 0
    then (
          List.iter (printf "%s ") prep_check_lst_1;
          exit 0);
  print_endline "*** target_1: Rules are linear and monotonic.*** \n";

  (* Rule for each co-existence of schemas *)
  print_endline "*** target_1: Rule for each co-existence of schemas *** \n";
  let evolved_bwd_rel_lst_1 = get_rels evolved_bwd_pred_lst_1 in
  let sttl_delta_pair_1 = Preperation.get_delta_pair ast_schema_1 ast_constraint_1 ast_schevo_1 ast_bwd_1 evolved_bwd_pred_lst_1 log in

  (* check disjointness *)
(*
  print_endline "*** target_1: Disjointness check.*** \n";
  let prep_disjoint_lst_1 = Preperation.prep_disjoint sttl_delta_pair_1 log in
  let disjointness_lst_1 = Disjoint.check_disjoint prep_disjoint_lst_1 log timeout in

  if List.length disjointness_lst_1 <> 0
    then begin
      let e = printf "%s " in
      List.iter e disjointness_lst_1;
      exit 0
      end
    else
    print_endline "target_1: Disjointness is satisfied.";
*)

  (* ************************************************ *)
  (* Step 2: Checking consistency                     *)
  (* ************************************************ *)
  print_endline "\n(***********************************)";
  print_endline "(* Step 2: Checking consistency      *)";
  print_endline "(* ***********************************)";

  (* --- check of target_1 ---------*)
  print_endline "*** target_1: checking consistency.*** \n";
  let consistency_lst_1 = Consistency.check_insdel ast_schema_1 ast_constraint_1 ast_schevo_1 ast_bwd_1 source_pred_lst_1 evolved_bwd_pred_lst_1 source_ins_rels_1 source_del_rels_1 target_pred_lst_1 log timeout in

  if List.length consistency_lst_1 !=0
  then begin
   let e = printf "%s " in
   List.iter e consistency_lst_1;
   exit 0
  end
  else
    print_endline "target_1: Consistency is satisfied.\n";

(* *********************************************** *)
(* Step 3: Source schema                           *)
(* *********************************************** *)
print_endline "\n(* *************************************** *)";
print_endline   "(* Step 3: Source schema                   *)";
print_endline   "(* *************************************** *)";

(* derive get_init and putdelta_init *)
let init_pred_lst = unique_element @@ init_pred_lst_1 in

let init_ast_lst_1 =  View_init.derivation_init_birds_1 ast_schemas ast_constraint_core_1 ast_constraint_pk init_pred_lst head_preds_target_1 target_pred_1 ast_schevo_1 source_rels log in

(* exeucte birds and generate SQL *)
let init_all_source_rels = unique_element @@ List.fold_left  List.append [] (List.map get_source_rels_schema init_ast_lst_1)
in
       printf "init_all_source_rels=> [";
       let print_el s = printf "%s; " s in
       List.iter print_el init_all_source_rels;
       printf "]\n";

let schema_mpg_init_lst_1 = View_init.mpg_init init_all_source_rels log physical in
let all_schema_mpg_init_lst_1 = unique_element @@
                                schema_mpg_lst_1 @ schema_mpg_lst_1 @ schema_mpg_init_lst_1 in

       printf "init_all_source_rels=> [\n";
       let print_el s = printf "(%s, %s); " (fst s) (snd s) in
       List.iter print_el all_schema_mpg_init_lst_1;
       printf "\n]\n";

print_endline "run BIRDS for initial relations...";
let birds_init_lst_1 = execute_birds init_ast_lst_1 log dbschema false in (* set true to make verificaiton by BIRDS *)
let birds_sql_init_lst_1 = List.map snd birds_init_lst_1 in
let birds_status_init_lst_1 = List.filter (fun x -> match x with 0 -> false | _ -> true) (List.map fst birds_init_lst_1) in

let dummy =
  if (List.length birds_status_init_lst_1) != 0
  then begin printf ""; end
  else begin
    let e = rewrite_sql_schemas log dbschema all_schema_mpg_init_lst_1 in
    List.iter e birds_sql_init_lst_1;
    end
in


  (* **************************************************************** *)
  (* Step 4: Target schema                                            *)
  (* **************************************************************** *)
  print_endline "\n\n(* ************************************************* *)";
  print_endline   "(* Step 4: Target schema                               *)";
  print_endline   "(* ************************************************* *)";

  (* derive BIRDS program (get and putdelta) for target schema 1 *)
  let target_1_ast = View_evo.derivation_target_birds_1 ast_schema_1 ast_constraint_core_1 ast_constraint_pk_1 ast_schevo_1 ast_bwd_1 target_pred_1 pk_lst init_ast_lst_1 source_pred_lst log timeout in

  let target_ast_lst_1 = [target_1_ast] in

  (* exeucte birds and generate SQL *)
  print_endline "run BIRDS for Target schema ...";
  let birds_target_lst_1 = execute_birds target_ast_lst_1 log dbschema true in (* set true to make verificaiton by BIRDS *)
  let birds_sql_target_lst_1 = List.map snd birds_target_lst_1 in
  let birds_status_target_lst_1 = List.filter (fun x -> match x with 0 -> false | _ -> true) (List.map fst birds_target_lst_1) in

  let dummy =
    if (List.length birds_status_target_lst_1) != 0
    then begin printf ""; end
    else begin
      let e = rewrite_sql_schemas log dbschema all_schema_mpg_init_lst_1 in
      List.iter e birds_sql_target_lst_1;
      end
  in

  (* **************************************************************** *)
  (* Show final result                                                *)
  (* **************************************************************** *)
  let birds_result = birds_init_lst_1 @ birds_target_lst_1 in
  View_common.show_result birds_result;
;;
