(* @author: Jumpei Tanaka *)

(* ************************************************ *)
(* Step 2: Checking consistency                     *)
(* ************************************************ *)

open Expr;;
open Utils;;
open Tools;;
open Printf;;
open Satisfiability;;


(* --------------------------------------------------------
 Derive rules for S_new
 input: lsit of predicates [s(A,B)]
 output: ast as
         s_new(A,B) :- s(A,B), not -s(A,B).
         s_new(A,B) :- +s(A,B).
--------------------------------------------------------*)
let  derive_snew pred_lst =

  let rec derive_new_rules pred_lst = match pred_lst with
    | [] -> []
    | hd::rest -> _1_derive_new_rules hd @ derive_new_rules rest
    and _1_derive_new_rules hd = match hd with
      | Pred (name, varlst) ->
          let snew = Pred (name ^ "_new", varlst) in
          let sold = Pred (name, varlst) in
          let ins = Deltainsert (name, varlst) in
          let del = Deltadelete (name, varlst) in
          let ins_rule = Rule (snew, [Rel(sold); Not(del)]) in
          let del_rule = Rule (snew, [Rel(ins)]) in
          [ins_rule] @ [del_rule]
      | _ -> invalid_arg "function derive_new called without rterm of pred"
  in

  let sttlst = derive_new_rules pred_lst in
  let ast_snew = Prog(sttlst) in

ast_snew
;;

(* --------------------------------------------------------
 Derive rules for T_newright
 input: list of predicates of evolved relations [t(A,B); t2(A,B,C)],
        list of rel names of evolved relations which have backward propagations, [t]
 output: ast as
         t_newright(A,B) :- t(A,B), not -t(A,B).
         t_newright(A,B) :- +t(A,B).
--------------------------------------------------------*)
let derive_tnewright pred_lst rel_bwd_lst =

  let rec derive_new_rules pred_lst rel_bwd_lst = match pred_lst with
    | [] -> []
    | hd::rest -> _1_derive_new_rules hd rel_bwd_lst @ derive_new_rules rest rel_bwd_lst
    and _1_derive_new_rules hd rel_bwd_lst = match hd with
      | Pred (name, varlst) ->
          if List.mem name rel_bwd_lst
          then begin
            let tnew = Pred (name ^ "_newright", varlst) in
            let told = Pred (name ^ "_cur", varlst) in
            let ins = Deltainsert (name, varlst) in
            let del = Deltadelete (name, varlst) in
            let ins_rule = Rule (tnew, [Rel(told); Not(del)]) in
            let del_rule = Rule (tnew, [Rel(ins)]) in
            [ins_rule] @ [del_rule]
         end
         else
            []
      | _ -> invalid_arg "function derive_new_rules called without rterm of pred"
  in

  let sttlst = derive_new_rules pred_lst rel_bwd_lst in
  let ast_tnewright = Prog(sttlst) in

ast_tnewright
;;

(* --------------------------------------------------------
 Derive rules for schevo_right
 input: ast of schema evolution, list of evolved predicates
        t1(A, B) :- s1(A, B) , B = 1.
 output: ast as
        t1_cur(A, B) :- s1(A, B) , B = 1.
--------------------------------------------------------*)
let derive_schevo_right ast_schevo pred_lst =

  let rec get_ast_consis ast pred_lst = match pred_lst with
    | [] -> []
    | hd::rest -> (_1_get_ast_consis ast hd) @ (get_ast_consis ast rest)
    and _1_get_ast_consis ast hd =
      get_sttl @@ get_one_query ast hd
  in

  let rec derive ast pred_lst = match ast with
    | Prog sttl -> _1_derive sttl pred_lst
    and _1_derive sttl pred_lst = match sttl with
      | [] -> []
      | hd::rest -> (_2_derive hd pred_lst) @ (_1_derive rest pred_lst)
    and _2_derive hd pred_lst = match hd with
      | Rule (Pred(rel, varlst), bodylst) ->
          if List.mem (Pred(rel, varlst)) pred_lst
          then
            [Rule (Pred((rel ^ "_cur"), varlst), bodylst)]
          else
            [hd]
      | _ -> invalid_arg "function derive_schevo_right without rules"
  in

  let ast_consis = Prog (get_ast_consis ast_schevo pred_lst) in
  let result = Prog (derive ast_consis pred_lst) in
result
;;

(* get rules for schema evolution which has backward propagation rules *)
let derive_schevo_consis ast evolved_bwd_pred_lst =

  let rec derive ast pred_lst = match pred_lst with
      | [] -> []
      | hd::rest -> (_1_derive ast hd) @ (derive ast rest)

    and _1_derive ast hd =
      get_sttl @@ get_one_query ast hd
  in

  let result = Prog (derive ast evolved_bwd_pred_lst) in
result
;;


(* F(S ⊕ F'(S,∆T)): replace rules of schema evolution with T_new and S_new *)
let derive_ast_schevo_new ast_schevo source_rel_lst evolved_bwd_rel_lst =

  let rec _0_derive_ast_schevo_new ast_schevo source_rel_lst evolved_bwd_rel_lst = match ast_schevo with
    | Prog sttl -> _1_derive_ast_schevo_new sttl source_rel_lst evolved_bwd_rel_lst

    and _1_derive_ast_schevo_new sttl source_rel_lst evolved_bwd_rel_lst = match sttl with
      | [] -> []
      | hd::rest -> (_2_derive_ast_schevo_new hd source_rel_lst evolved_bwd_rel_lst)
                    @ (_1_derive_ast_schevo_new rest source_rel_lst evolved_bwd_rel_lst)

    and _2_derive_ast_schevo_new hd source_rel_lst evolved_bwd_rel_lst = match hd  with
      | Rule (Pred(rel, varlst), bodylst) ->
                if List.mem rel evolved_bwd_rel_lst
                then begin
                  let rel_new = rel ^ "_newleft" in
                  let bodylst_new = _3_derive_ast_schevo_new bodylst source_rel_lst in
                  [Rule (Pred(rel_new, varlst), bodylst_new)]
                end
                else begin
                  let bodylst_new = _3_derive_ast_schevo_new bodylst source_rel_lst in
                  [Rule (Pred(rel, varlst), bodylst_new)]
                end
      | _ -> invalid_arg "function derive_ast_schevo_new without Rule"

  and _3_derive_ast_schevo_new bodylst source_rel_lst = match bodylst with
      | [] -> []
      | hd::rest -> (_4_derive_ast_schevo_new hd source_rel_lst)
                    @ (_3_derive_ast_schevo_new rest source_rel_lst)

  and _4_derive_ast_schevo_new hd source_rel_lst = match hd with
    | Rel (Pred(name, varlst)) ->
          if List.mem name source_rel_lst
          then [Rel(Pred((name ^ "_new"), varlst))]
          else [Rel(Pred(name, varlst))]
    | Not (Pred(name, varlst)) ->
          if List.mem name source_rel_lst
          then [Not(Pred((name ^ "_new"), varlst))]
          else [Not(Pred(name, varlst))]
    | _ -> [hd]
  in

  let sttlst = _0_derive_ast_schevo_new ast_schevo source_rel_lst evolved_bwd_rel_lst in
  let ast_schevo_new = Prog(sttlst) in

ast_schevo_new
;;


(* exucute lean program and return a list of results *)
let execute_lean lean_lst log timeout =

  let rec _1_execute_lean lean_lst timeout = match lean_lst with
    | [] -> []
    | hd::rest -> (_2_execute_lean hd timeout) @ (_1_execute_lean rest timeout)
    and _2_execute_lean hd timeout =
      let is_consistency, msg = Utils.verify_fo_lean !log !timeout (snd hd) in
      if is_consistency = 0
      then
        []
      else
        [(fst hd), msg]
  in

  let result = _1_execute_lean lean_lst timeout in
result
;;


(* ======================================================================== *)
(*
  Step 1: Checking consistency
  F(S ⊕ F'(S,∆T)) ⊂ F(S) ⊕ ∆T
*)
(* generate schema by given source rel list and target_rel *)
let generate_schema ast_schemas source_rels target_rel =

  let rec generate_t sttl_schema target_rel = match sttl_schema with
    | [] -> []
    | hd::rest -> (_1_generate_t hd target_rel) @ (generate_t rest target_rel)
    and _1_generate_t stt target_rel = match stt with
      | Target_schema (_, rel, varlst) ->
         if rel = target_rel
         then
            [ View (rel, varlst);
              Source (("ins_" ^ rel), varlst);
              Source (("del_" ^ rel), varlst)
            ]
         else []
      | _ -> []
  in

  let rec generate_s sttl_schema source_rels = match sttl_schema with
    | [] -> []
    | hd::rest -> (_1_generate_s hd source_rels) @ (generate_s rest source_rels)
    and _1_generate_s stt source_rels = match stt with
      | Source_schema (_, rel, varlst) ->
        if List.mem rel source_rels
        then [Source (rel, varlst)]
        else []
      | _ -> []
  in

  let ast_schema_target = generate_t (get_sttl ast_schemas) target_rel in
  let ast_schema_source = generate_s (get_sttl ast_schemas) source_rels in
  let ast_schemas_consis = Prog (ast_schema_target @ ast_schema_source) in

ast_schemas_consis
;;

(* generate constraint by given source rel list and target_rel *)
let generate_constraint_consis ast_constraint source_rels target_rel =

  let rec generate sttl_constraint rel_lst target_rel = match sttl_constraint with
    | [] -> []
    | hd::rest -> (_1_generate hd rel_lst target_rel) @ (generate rest rel_lst target_rel)

    and _1_generate stt rel_lst target_rel = match stt with
      | Rule (get_empty_pred, bodylst) ->
         let body_rels = get_rels_body ( Prog [stt] ) in
         if list_inclusion body_rels rel_lst
          then [Rule (get_empty_pred, (_2_generate bodylst target_rel))]
          else []
      | _ -> []

    and _2_generate bodylst target_rel = match bodylst with
      | [] -> []
      | hd::rest -> (_3_generate hd target_rel) @ (_2_generate rest target_rel)
      and _3_generate tm target_rel = match tm with
        | Rel(Deltainsert(rel, varlst)) -> [ Rel (Pred ((rel), varlst)) ]
        | Rel(Deltadelete(rel, varlst)) -> [ Not (Pred ((rel), varlst)) ]
        | Not(Deltainsert(rel, varlst)) -> [ Not (Pred ((rel), varlst)) ]
        | Not(Deltadelete(rel, varlst)) -> [ Rel (Pred ((rel), varlst)) ]
(*
        | Rel(Deltainsert(rel, varlst)) -> [ Rel (Pred (("ins_" ^ rel), varlst)) ]
        | Rel(Deltadelete(rel, varlst)) -> [ Rel (Pred (("del_" ^ rel), varlst)) ]
        | Not(Deltainsert(rel, varlst)) -> [ Not (Pred (("ins_" ^ rel), varlst)) ]
        | Not(Deltadelete(rel, varlst)) -> [ Not (Pred (("del_" ^ rel), varlst)) ]
*)
        | _ -> [tm]
  in

  let rel_lst = source_rels @ [target_rel] in
  let ast_constraint_consis = Prog (generate (get_sttl ast_constraint) rel_lst target_rel) in

ast_constraint_consis
;;



(* generate tmp target rule and ins/del on target *)
let generate_ast_pred_newr ast_pred target_rel =

  let rec get_idb_lst rule_sttl = match rule_sttl with
    | [] -> []
    | hd::rest -> (_1_get_idb_lst hd) @ (get_idb_lst rest)
    and _1_get_idb_lst stt = match stt with
      | Rule (Pred(rel, varlst), bodylst) -> [rel]
      | _ -> []
  in

  let rec get_body_lst rule_sttl = match rule_sttl with
    | [] -> []
    | hd::rest -> (_1_get_body_lst hd) @ (get_body_lst rest)
    and _1_get_body_lst stt = match stt with
      | Rule (Pred(rel, varlst), bodylst) -> _2_get_body_lst bodylst
      | _ -> []
    and _2_get_body_lst bodylst = match bodylst with
      | [] -> []
      | hd::rest -> (_3_get_body_lst hd) @ (_2_get_body_lst rest)
    and _3_get_body_lst tm = match tm with
      | Rel(Pred(rel, varlst)) -> [rel]
      | Not(Pred(rel, varlst)) -> [rel]
      | _ -> []
  in

  let rec generate sttl_pred target_rel idb_rel_lst body_rel_lst = match sttl_pred with
    | [] -> []
    | hd::rest -> (_2_generate hd target_rel idb_rel_lst body_rel_lst)
                  @ (generate rest target_rel idb_rel_lst body_rel_lst)

  and _2_generate stt target_rel idb_rel_lst body_rel_lst = match stt with
    | Rule (Pred (rel, varlst), bodylst) ->
        let renamed_bodylst = rename bodylst idb_rel_lst in
        if rel = target_rel
        then
          [ Rule (Pred (("tmp_" ^ rel), varlst), renamed_bodylst);
            Rule (Pred (("newr_" ^ rel), varlst), [Rel(Pred(("tmp_" ^ rel), varlst));
                                                  Not(Pred(("del_" ^ rel), varlst)) ]);
            Rule (Pred (("newr_" ^ rel), varlst), [Rel(Pred(("ins_" ^ rel), varlst))])
          ]
        else if List.mem rel body_rel_lst
        then
          [Rule (Pred ("tmp_" ^ rel, varlst), renamed_bodylst)]
        else
          [Rule (Pred (rel, varlst), renamed_bodylst)]
    | _ -> []

  and rename bodylst idb_rel_lst = match bodylst with
    | [] -> []
    | hd::rest -> (_1_rename hd idb_rel_lst) @ (rename rest idb_rel_lst)
  and _1_rename tm idb_rel_lst = match tm with
    | Rel (Pred(rel, varlst)) ->
        if List.mem rel idb_rel_lst
        then
          [Rel (Pred("tmp_" ^ rel, varlst))]
        else
          [tm]
    | Not (Pred(rel, varlst)) ->
        if List.mem rel idb_rel_lst
        then
          [Not (Pred("tmp_" ^ rel, varlst))]
        else
          [tm]
    | _ -> [tm]
  in

  let idb_rel_lst = list_setminus (unique_element @@ get_idb_lst (get_sttl ast_pred)) [target_rel] in
  let body_rel_lst = unique_element @@ get_body_lst (get_sttl ast_pred) in

  let result = Prog (generate (get_sttl ast_pred) target_rel idb_rel_lst body_rel_lst) in

result
;;


(* generate new_right target rule and ins/del on target *)
let generate_ast_pred_tmp ast_pred target_rel =

  let rec generate sttl_pred starget_rel = match sttl_pred with
    | [] -> []
    | hd::rest -> (_2_generate hd target_rel) @ (generate rest target_rel)

  and _2_generate stt target_rel = match stt with
    | Rule (Pred (rel, varlst), bodylst) ->
        if rel = target_rel
        then
          [Rule (Pred (("tmp_" ^ rel), varlst), bodylst);
           Rule (Pred (("ins_" ^ rel), varlst), [Rel(Pred(rel, varlst)); Not(Pred (("tmp_" ^ rel), varlst))]);
           Rule (Pred (("del_" ^ rel), varlst), [Not(Pred(rel, varlst)); Rel(Pred (("tmp_" ^ rel), varlst))])
          ]
        else
          [Rule (Pred (rel, varlst), bodylst)]
    | _ -> []
  in

  let result = Prog (generate (get_sttl ast_pred) target_rel) in

result
;;

let generate_ast_pred_new ast_pred source_rels target_rel =

  let rec generate sttl_pred source_rels target_rel = match sttl_pred with
    | [] -> []
    | hd::rest -> (_2_generate hd source_rels target_rel) @ (generate rest source_rels target_rel)

  and _2_generate stt source_rels target_rel = match stt with
    | Rule (Pred (rel, varlst), bodylst) ->
        if rel = target_rel
        then
          [Rule (Pred (("new_" ^ rel), varlst), (_3_generate bodylst source_rels)) ]
        else
          [Rule (Pred (rel, varlst), (_3_generate bodylst source_rels))]
    | _ -> []

  and _3_generate bodylst source_rels = match bodylst with
    | [] -> []
    | hd::rest -> (_4_generate hd source_rels) @ (_3_generate rest source_rels)
  and _4_generate tm source_rels = match tm with
    | Rel (Pred (rel, varlst)) ->
        if List.mem rel source_rels
        then [Rel (Pred (("new_" ^ rel), varlst))]
        else [tm]
    | Not (Pred (rel, varlst)) ->
        if List.mem rel source_rels
        then [Not (Pred (("new_" ^ rel), varlst))]
        else [tm]
    | _ -> [tm]
  in

  let result = Prog (generate (get_sttl ast_pred) source_rels target_rel) in

result
;;

(* generate bwd with del/ins and base *)
let generate_ast_bwd_consis ast_bwd_pred  =

  let rec reform ast = match ast with
    | Prog sttl -> _1_reform sttl

    and _1_reform sttl = match sttl with
      | [] -> []
      | hd::rest -> (_2_reform hd ) @ (_1_reform rest)

    and _2_reform stt = match stt with
      | Rule (Pred(rel, varlst), bodylst ) ->
          [ Rule ( Pred(rel, varlst), (_3_reform bodylst) ) ]
      | Rule (Deltainsert(rel, varlst), bodylst ) ->
          [ Rule ( Pred(("ins_" ^ rel), varlst), (_3_reform bodylst) ) ]
      | Rule (Deltadelete(rel, varlst), bodylst ) ->
          [ Rule ( Pred(("del_" ^ rel), varlst), (_3_reform bodylst) ) ]
      | _ -> invalid_arg "function reform_ast_pred called without rules in ast"

    and _3_reform bodylst = match bodylst with
      | [] -> []
      | hd::rest -> (_4_reform hd ) @ (_3_reform rest)

    and _4_reform tm = match tm with
      | Rel (Deltainsert(rel, varlst)) -> [Rel (Pred ( ("ins_" ^ rel), varlst)) ]
      | Rel (Deltadelete(rel, varlst)) -> [Rel (Pred ( ("del_" ^ rel), varlst)) ]
      | Not (Deltainsert(rel, varlst)) -> [Not (Pred ( ("ins_" ^ rel), varlst)) ]
      | Not (Deltadelete(rel, varlst)) -> [Not (Pred ( ("del_" ^ rel), varlst)) ]
      | _ -> [tm]
    in

  let ast_bwd_consis = Prog (reform ast_bwd_pred) in

ast_bwd_consis
;;

(* generate s_new rules *)
let generate_ast_bwd_new ast_pred_consis source_pred_lst source_ins_rels source_del_rels source_pred_lst =

  let rec generate sttl_pred_consis source_rels source_ins_rels source_del_rels source_pred_lst = match sttl_pred_consis with
    | [] -> []
    | hd::rest -> (_1_generate hd source_rels source_ins_rels source_del_rels source_pred_lst)
                   @ (generate rest source_rels source_ins_rels source_del_rels source_pred_lst)

  and _1_generate hd source_rels source_ins_rels source_del_rels source_pred_lst = match hd with
    | Rule (Pred (rel, varlst), bodylst) -> _2_generate bodylst source_rels source_ins_rels source_del_rels source_pred_lst
    | _ -> []

  and _2_generate bodylst source_rels source_ins_rels source_del_rels source_pred_lst = match bodylst with
    | [] -> []
    | hd::rest -> (_3_generate hd source_rels source_ins_rels source_del_rels source_pred_lst)
                   @ (_2_generate rest source_rels source_ins_rels source_del_rels source_pred_lst)

  and _3_generate tm source_rels source_ins_rels source_del_rels source_pred_lst = match tm with
    | Rel(Pred(rel, varlst))
    | Not(Pred(rel, varlst)) ->
      if List.mem rel source_rels
      then
          if (List.mem rel source_ins_rels) && (List.mem rel source_del_rels)
          then
            begin
            let s_varlst = List.hd (get_varlst rel source_pred_lst) in
            [Rule( Pred( ("new_" ^ rel), s_varlst), [Rel (Pred(rel, s_varlst)); Not (Pred(("del_" ^ rel), s_varlst)) ] );
            Rule( Pred( ("new_" ^ rel), s_varlst), [Rel (Pred(("ins_" ^ rel), s_varlst))] )
            ]
            end
          else
            if (List.mem rel source_ins_rels) && not (List.mem rel source_del_rels)
            then
              begin
                let s_varlst = List.hd (get_varlst rel source_pred_lst) in
                [Rule( Pred( ("new_" ^ rel), s_varlst), [Rel (Pred(rel, s_varlst)) ] );
                 Rule( Pred( ("new_" ^ rel), s_varlst), [Rel (Pred(("ins_" ^ rel), s_varlst))] )
                ]
              end
            else
              if not (List.mem rel source_ins_rels) && (List.mem rel source_del_rels)
              then
                begin
                  let s_varlst = List.hd (get_varlst rel source_pred_lst) in
                  [Rule( Pred( ("new_" ^ rel), s_varlst), [Rel (Pred(rel, s_varlst)); Not (Pred(("del_" ^ rel), s_varlst)) ] )
                  ]
                end
              else
                begin
                let s_varlst = List.hd (get_varlst rel source_pred_lst) in
                [Rule( Pred( ("new_" ^ rel), s_varlst), [Rel (Pred(rel, s_varlst)) ] )
                ]
                end
      else []
  | _ -> []

and get_varlst rel source_pred_lst = match source_pred_lst with
  | [] -> []
  | hd::rest -> (_1_get_varlst rel hd) @ (get_varlst rel rest)
  and _1_get_varlst rel rt = match rt with
    | Pred (srel, varlst) ->
      if rel = srel
      then [varlst]
      else []
    | _ -> []
in

  let sttl_pred_consis = get_sttl ast_pred_consis in
  let source_rels = get_rels source_pred_lst in
  let ast_bwd_new = Prog (unique_element @@ generate sttl_pred_consis source_rels source_ins_rels source_del_rels source_pred_lst) in

ast_bwd_new
;;

(* generate goal of consistency checking *)
let generate_ast_pred_goal target_pred =

  let generate target_pred = match target_pred with
    | Pred (rel, varlst) -> Pred (("goal_" ^ rel), varlst)
    | _ -> invalid_arg "function generate_goal without Pred"
  in

  let generate_ast target_pred = match target_pred with
    | Pred (rel, varlst) ->
        Prog [Rule (Pred( ("goal_" ^ rel), varlst), [Rel(Pred( ("new_" ^ rel), varlst));
                                                     Not(Pred(("newr_" ^ rel), varlst))] ) ]
    | _ -> invalid_arg "function generate_goal without Pred"
  in

  let goal = generate target_pred in
  let ast_goal = generate_ast target_pred in

goal, ast_goal
;;

(* -----------------------------------------------------------------------------------------*)
let check ast_schemas ast_constraint ast_schevo ast_bwd source_pred_lst evolved_bwd_pred_lst source_ins_rels source_del_rels log timeout =

  let rec check_consistency ast_schemas ast_constraint ast_schevo ast_bwd source_pred_lst pred_lst log timeout = match pred_lst with
    | [] -> []
    | hd::rest -> (_1_check_consistency ast_schemas ast_constraint ast_schevo ast_bwd source_pred_lst hd log timeout)
                  @ (check_consistency ast_schemas ast_constraint ast_schevo ast_bwd source_pred_lst rest log timeout)

    and _1_check_consistency ast_schemas ast_constraint ast_schevo ast_bwd source_pred_lst target_pred log timeout =

      let source_rels = get_rels source_pred_lst in
      let target_rel = get_rel_from_pred target_pred in

      let ast_schema_consis = generate_schema ast_schemas source_rels target_rel in
      let ast_constraint_consis = generate_constraint_consis ast_constraint source_rels target_rel in
      let ast_pred = get_one_query ast_schevo target_pred in

(*      let ast_bwd_pred = filter_bwd ast_bwd target_pred in *)
      let source_rels2 = get_rels_inbody ast_pred source_rels in
      let ast_bwd_pred = get_queries ast_bwd source_rels2 in
      let ast_pred_tmp = generate_ast_pred_tmp ast_pred target_rel in
      let ast_pred_newr = generate_ast_pred_newr ast_pred target_rel in
      let ast_bwd_consis = generate_ast_bwd_consis ast_bwd_pred in
      let ast_bwd_new = generate_ast_bwd_new ast_pred_tmp source_pred_lst source_ins_rels source_del_rels source_pred_lst in
      let ast_pred_new = generate_ast_pred_new ast_pred source_rels target_rel in
      let goal, ast_pred_goal = generate_ast_pred_goal target_pred in

              print_endline "ast_constraint_consis:"; Expr.print_ast ast_constraint_consis; printf "\n";
              print_endline "ast_bwd_pred:"; Expr.print_ast ast_bwd_pred; printf "\n";
              print_endline "ast_pred_tmp:"; Expr.print_ast ast_pred_tmp; printf "\n";
              print_endline "ast_pred_newr:"; Expr.print_ast ast_pred_newr; printf "\n";
              print_endline "ast_bwd_consis:"; Expr.print_ast ast_bwd_consis; printf "\n";
              print_endline "ast_bwd_new:"; Expr.print_ast ast_bwd_new; printf "\n";
              print_endline "ast_pred_new:"; Expr.print_ast ast_pred_new; printf "\n";

      let ast_consis_0 = List.fold_left merge_ast (Prog [])
                         [ast_schema_consis; ast_constraint_consis;
                          ast_pred_tmp;
                          ast_bwd_consis; ast_bwd_new; ast_pred_new;
                          ast_pred_newr;
                         ast_pred_goal]
      in
      let ast_consis = Prog (unique_element @@ get_sttl ast_consis_0) in

          if !log
          then begin
              print_endline "ast_consistency:"; Expr.print_ast ast_consis; printf "\n";
              printf "goal = %s\n" (string_of_rterm goal);
          end
          else ();

      (* check satisfiability of consistency *)
      let lean_fol_of_consistency = Satisfiability.lean_consistency ast_consis ast_constraint_consis target_pred goal log in

      let is_consistency, msg = Utils.verify_fo_lean !log !timeout lean_fol_of_consistency in

          (* is_consistency = 0 means satisfying consistency , 1 is not *)
          if !log then begin printf "consistency = %d\n" is_consistency; end
          else ();

      if is_consistency != 0
      then begin
        let result = "Consistency is not satisfied about rules of " ^ (string_of_rterm goal) ^ "\n."in
        [result]
      end
      else
        []

  in

  let pred_lst = evolved_bwd_pred_lst in
  let result = check_consistency ast_schemas ast_constraint ast_schevo ast_bwd source_pred_lst pred_lst log timeout in

result
;;
