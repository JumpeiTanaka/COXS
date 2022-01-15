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
let generate_schema ast_schemas source_rels target_rel  target_rel_lst =

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

  let rec generate_t2s sttl_schema t2s_rel_lst = match sttl_schema with
    | [] -> []
    | hd::rest -> (_1_generate_t2s hd t2s_rel_lst) @ (generate_t2s rest t2s_rel_lst)
    and _1_generate_t2s stt t2s_rel_lst = match stt with
      | Target_schema (_, rel, varlst) ->
        if List.mem rel t2s_rel_lst
        then [ Source(rel, varlst)]
        else []
      | _ -> []
  in

  let t2s_rel_lst = List.filter (fun x -> x <> target_rel) target_rel_lst in
  let ast_schema_target = generate_t (get_sttl ast_schemas) target_rel in
  let ast_schema_source = generate_s (get_sttl ast_schemas) source_rels in
  let ast_schema_t2source = generate_t2s (get_sttl ast_schemas) t2s_rel_lst in
  let ast_schemas_consis = Prog (ast_schema_target @ ast_schema_source @ ast_schema_t2source) in

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

(* generate ruturned insertion on target *)
let generate_ast_return_insdel ast_pred target_rel =

  let rec generate sttl_pred starget_rel head_rels = match sttl_pred with
    | [] -> []
    | hd::rest -> (_2_generate hd target_rel head_rels) @ (generate rest target_rel head_rels)

  and _2_generate stt target_rel head_rels = match stt with
    | Rule (Pred (rel, varlst), bodylst) ->
        if rel = target_rel
        then
          [
           Rule (Pred (("r_ins_" ^ rel), varlst), [Rel(Pred("new_" ^ rel, varlst)); Not(Pred (("tmp_" ^ rel), varlst))]);
           Rule (Pred (("r_del_" ^ rel), varlst), [Not(Pred("new_" ^ rel, varlst)); Rel(Pred (("tmp_" ^ rel), varlst))]);
           Rule (Pred (("tmp_" ^ rel), varlst), (_3_generate bodylst head_rels));
          ]
        else
          [Rule (Pred ("tmp_" ^ rel, varlst), (_3_generate bodylst head_rels))]
    | _ -> []

  and _3_generate bodylst head_rels = match bodylst with
    | [] -> []
    | hd::rest -> (_4_generate hd head_rels) @ (_3_generate rest head_rels)

  and _4_generate tm head_rels = match tm with
    | Rel (Pred (rel, varlst)) ->
        if (List.mem rel head_rels)
        then [Rel (Pred (("tmp_" ^ rel), varlst))]
        else [tm]
    | Not (Pred (rel, varlst)) ->
        if (List.mem rel head_rels)
        then [Not (Pred (("tmp_" ^ rel), varlst))]
        else [tm]
    | _ -> [tm]

  in

  let head_rels = get_rels_head ast_pred in
  let result = Prog (generate (get_sttl ast_pred) target_rel head_rels) in

result
;;


let generate_ast_pred_tmp ast_pred target_rel =

  let rec generate sttl_pred starget_rel head_rels = match sttl_pred with
    | [] -> []
    | hd::rest -> (_2_generate hd target_rel head_rels) @ (generate rest target_rel head_rels)

  and _2_generate stt target_rel head_rels = match stt with
    | Rule (Pred (rel, varlst), bodylst) ->
        if rel = target_rel
        then
          [
           Rule (Pred (("ins_" ^ rel), varlst), [Rel(Pred(rel, varlst)); Not(Pred (("tmp_" ^ rel), varlst))]);
           Rule (Pred (("del_" ^ rel), varlst), [Not(Pred(rel, varlst)); Rel(Pred (("tmp_" ^ rel), varlst))]);
           Rule (Pred (("tmp_" ^ rel), varlst), (_3_generate bodylst head_rels));
          ]
        else
          [Rule (Pred ("tmp_" ^ rel, varlst), (_3_generate bodylst head_rels))]
    | _ -> []

  and _3_generate bodylst head_rels = match bodylst with
    | [] -> []
    | hd::rest -> (_4_generate hd head_rels) @ (_3_generate rest head_rels)

  and _4_generate tm head_rels = match tm with
    | Rel (Pred (rel, varlst)) ->
        if (List.mem rel head_rels)
        then [Rel (Pred (("tmp_" ^ rel), varlst))]
        else [tm]
    | Not (Pred (rel, varlst)) ->
        if (List.mem rel head_rels)
        then [Not (Pred (("tmp_" ^ rel), varlst))]
        else [tm]
    | _ -> [tm]

  in

  let head_rels = get_rels_head ast_pred in
  let result = Prog (generate (get_sttl ast_pred) target_rel head_rels) in

result
;;

let generate_ast_pred_new ast_pred source_rels =

  let rec generate sttl_pred source_rels head_rels= match sttl_pred with
    | [] -> []
    | hd::rest -> (_2_generate hd source_rels head_rels) @ (generate rest source_rels head_rels)

  and _2_generate stt source_rels head_rels = match stt with
    | Rule (Pred (rel, varlst), bodylst) ->
          [Rule (Pred (("new_" ^ rel), varlst), (_3_generate bodylst source_rels head_rels)) ]
    | _ -> []

  and _3_generate bodylst source_rels head_rels = match bodylst with
    | [] -> []
    | hd::rest -> (_4_generate hd source_rels head_rels) @ (_3_generate rest source_rels head_rels)

  and _4_generate tm source_rels head_rels = match tm with
    | Rel (Pred (rel, varlst)) ->
        if (List.mem rel source_rels) ||  (List.mem rel head_rels)
        then [Rel (Pred (("new_" ^ rel), varlst))]
        else [tm]
    | Not (Pred (rel, varlst)) ->
        if (List.mem rel source_rels) ||  (List.mem rel head_rels)
        then [Not (Pred (("new_" ^ rel), varlst))]
        else [tm]
    | _ -> [tm]
  in

  let head_rels = get_rels_head ast_pred in
  let result = Prog (generate (get_sttl ast_pred) source_rels head_rels) in

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
let generate_ast_bwd_new ast_pred_tmp source_pred_lst source_ins_rels source_del_rels =

  let rec generate sttl_pred_tmp source_rels source_ins_rels source_del_rels source_pred_lst = match sttl_pred_tmp with
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

  let sttl_pred_tmp = get_sttl ast_pred_tmp in
  let source_rels = get_rels source_pred_lst in
  let ast_bwd_new = Prog (unique_element @@ generate sttl_pred_tmp source_rels source_ins_rels source_del_rels source_pred_lst) in

ast_bwd_new
;;


(* generate goal of consistency checking *)
let generate_ast_pred_goal_ins target_pred =

  let generate target_pred = match target_pred with
    | Pred (rel, varlst) -> Pred (("goal_ins_" ^ rel), varlst)
    | _ -> invalid_arg "function generate_goal without Pred"
  in

  let generate_ast target_pred = match target_pred with
    | Pred (rel, varlst) ->
        Prog [Rule (Pred( ("goal_ins_" ^ rel), varlst), [Rel(Pred( ("r_ins_" ^ rel), varlst));
                                                         Not(Pred(("ins_" ^ rel), varlst))]
                   )
             ]
    | _ -> invalid_arg "function generate_goal without Pred"
  in

  let goal = generate target_pred in
  let ast_goal = generate_ast target_pred in

goal, ast_goal
;;

(* generate goal of consistency checking *)
let generate_ast_pred_goal_del target_pred =

  let generate target_pred = match target_pred with
    | Pred (rel, varlst) -> Pred (("goal_del_" ^ rel), varlst)
    | _ -> invalid_arg "function generate_goal without Pred"
  in

  let generate_ast target_pred = match target_pred with
    | Pred (rel, varlst) ->
        Prog [Rule (Pred( ("goal_del_" ^ rel), varlst), [Rel (Pred( ("r_del_" ^ rel), varlst));
                                                         Not (Pred(("del_" ^ rel), varlst)) ]
                   )
             ]
    | _ -> invalid_arg "function generate_goal without Pred"
  in

  let goal = generate target_pred in
  let ast_goal = generate_ast target_pred in

goal, ast_goal
;;


(* -----------------------------------------------------------------------------------------*)
let check_insdel ast_schemas ast_constraint ast_schevo ast_bwd source_pred_lst evolved_bwd_pred_lst source_ins_rels source_del_rels target_pred_lst log timeout =

  let rec check_consistency ast_schemas ast_constraint ast_schevo ast_bwd source_pred_lst pred_lst target_rel_lst log timeout = match pred_lst with
    | [] -> []
    | hd::rest -> (_1_check_consistency ast_schemas ast_constraint ast_schevo ast_bwd source_pred_lst hd  target_rel_lst log timeout)
                  @ (check_consistency ast_schemas ast_constraint ast_schevo ast_bwd source_pred_lst rest target_rel_lst log timeout)

    and _1_check_consistency ast_schemas ast_constraint ast_schevo ast_bwd source_pred_lst target_pred target_rel_lst log timeout =

      let source_rels = get_rels source_pred_lst in
      let target_rel = get_rel_from_pred target_pred in
      let ast_schema_consis = generate_schema ast_schemas source_rels target_rel target_rel_lst in
      let ast_constraint_consis = generate_constraint_consis ast_constraint source_rels target_rel in
      let ast_pred = get_one_query ast_schevo target_pred in
      let source_rels2 = get_rels_inbody ast_pred source_rels in

      let ins_rules = get_rules_ins_in_body ast_bwd target_rel in
      let del_rules = get_rules_del_in_body ast_bwd target_rel in

      let head_preds_ins = get_preds_head ins_rules in
      let head_preds_del = get_preds_head del_rules in

      let ast_bwd_pred_ins =
        let nodel_ast_bwd = subtract_ast ast_bwd del_rules in
        let rec get_queries_ins ast preds = match preds with
          | [] -> []
          | hd::rest -> (get_sttl @@ get_one_query ast hd) @ (get_queries_ins ast rest)
        in
        Prog (unique_element @@ get_queries_ins nodel_ast_bwd head_preds_ins)
      in

      let ast_bwd_pred_del =
        let nodel_ast_bwd = subtract_ast ast_bwd ins_rules in
        let rec get_queries_del ast preds = match preds with
          | [] -> []
          | hd::rest -> (get_sttl @@ get_one_query ast hd) @ (get_queries_del ast rest)
        in
        Prog (unique_element @@ get_queries_del nodel_ast_bwd head_preds_del)
      in

      let ast_pred_tmp = generate_ast_pred_tmp ast_pred target_rel in

      let ast_bwd_consis_ins = generate_ast_bwd_consis ast_bwd_pred_ins in
      let ast_bwd_consis_del = generate_ast_bwd_consis ast_bwd_pred_del in

      let bwd_pred_ins_source_ins_rels =
        let rels = unique_element @@ get_ins_rels_head ast_bwd_pred_ins in
        List.filter (fun x -> List.mem x source_rels) rels
      in

      let bwd_pred_ins_source_del_rels =
        let rels = unique_element @@ get_del_rels_head ast_bwd_pred_ins in
        List.filter (fun x -> List.mem x source_rels) rels
      in

      let bwd_pred_del_source_ins_rels =
        let rels = unique_element @@ get_ins_rels_head ast_bwd_pred_del in
        List.filter (fun x -> List.mem x source_rels) rels
      in

      let bwd_pred_del_source_del_rels =
        let rels = unique_element @@ get_del_rels_head ast_bwd_pred_del in
        List.filter (fun x -> List.mem x source_rels) rels
      in

      let ast_bwd_new = generate_ast_bwd_new
        ast_pred_tmp source_pred_lst
        (bwd_pred_ins_source_ins_rels @ bwd_pred_del_source_ins_rels)
        (bwd_pred_ins_source_del_rels @ bwd_pred_del_source_del_rels)
      in

      let ast_return_insdel = generate_ast_return_insdel ast_pred target_rel in

      let ast_pred_new = generate_ast_pred_new ast_pred source_rels in

      let goal_ins, ast_pred_goal_ins = generate_ast_pred_goal_ins target_pred in
      let goal_del, ast_pred_goal_del = generate_ast_pred_goal_del target_pred in


        if !log
        then begin
              printf "source_rels => [";
              let print_el s = printf "%s; " s in
              List.iter print_el source_rels;
              printf "]\n";

              printf "target_rel => %s\n" target_rel;

              print_endline "ast_schema_consis:"; Expr.print_ast ast_schema_consis; printf "\n";
              print_endline "ast_constraint_consis:"; Expr.print_ast ast_constraint_consis; printf "\n";
              print_endline "ast_pred:"; Expr.print_ast ast_pred; printf "\n";
              print_endline "ast_bwd_pred_ins:"; Expr.print_ast ast_bwd_pred_ins; printf "\n";
              print_endline "ast_bwd_pred_del:"; Expr.print_ast ast_bwd_pred_del; printf "\n";
              print_endline "ast_pred_tmp:"; Expr.print_ast ast_pred_tmp; printf "\n";
              print_endline "ast_bwd_consis_ins:"; Expr.print_ast ast_bwd_consis_ins; printf "\n";
              print_endline "ast_bwd_consis_del:"; Expr.print_ast ast_bwd_consis_del; printf "\n";
              print_endline "ast_bwd_new:"; Expr.print_ast ast_bwd_new; printf "\n";
              print_endline "ast_return_insdel:"; Expr.print_ast ast_return_insdel; printf "\n";
              print_endline "ast_pred_new:"; Expr.print_ast ast_pred_new; printf "\n";
              print_endline "ast_pred_goal_ins:"; Expr.print_ast ast_pred_goal_ins; printf "\n";
              print_endline "ast_pred_goal_del:"; Expr.print_ast ast_pred_goal_del; printf "\n";
        end
        else ();


      (* --- Consisitency check of insertion on T --- *)
      let ast_consis_ins_0 = List.fold_left merge_ast (Prog [])
                            [ ast_schema_consis;
                              ast_constraint_consis;
                              ast_pred_goal_ins;
                              ast_pred_new;
                              ast_bwd_new;
                              ast_bwd_consis_ins;
                              ast_bwd_consis_del;
                              ast_pred_tmp;
                              ast_return_insdel;
                             ]
      in

      let ast_consis_ins = Prog (unique_element @@ get_sttl ast_consis_ins_0) in

          (* is_consistency = 0 means satisfying consistency , 1 is not *)
          if !log then begin
            print_endline "ast_consistency_ins:"; Expr.print_ast ast_consis_ins; printf "\n";
            printf "goal_ins = %s\n\n" (string_of_rterm goal_ins);
          end
          else ();

      (* check satisfiability of consistency *)
      let lean_fol_of_consistency_ins = Satisfiability.lean_consistency ast_consis_ins ast_constraint_consis target_pred goal_ins log in

      let is_consistency_ins, msg_ins = Utils.verify_fo_lean !log !timeout lean_fol_of_consistency_ins in

        if !log
          then begin printf "consistency_ins = %d\n\n" is_consistency_ins; end
          else ();


      (* --- Consisitency check of deletion on T --- *)
      let ast_consis_del_0 = List.fold_left merge_ast (Prog [])
                            [ ast_schema_consis;
                              ast_constraint_consis;
                              ast_pred_goal_del;
                              ast_pred_new;
                              ast_bwd_new;
                              ast_bwd_consis_ins;
                              ast_bwd_consis_del;
                              ast_pred_tmp;
                              ast_return_insdel;
                             ]
      in

      let ast_consis_del = Prog (unique_element @@ get_sttl ast_consis_del_0) in

          (* is_consistency = 0 means satisfying consistency , 1 is not *)
          if !log then begin
            print_endline "ast_consistency_del:"; Expr.print_ast ast_consis_del; printf "\n";
            printf "goal_del = %s\n\n" (string_of_rterm goal_del);
          end
          else ();

      (* check satisfiability of consistency *)
      let lean_fol_of_consistency_del = Satisfiability.lean_consistency ast_consis_del ast_constraint_consis target_pred goal_del log in

      let is_consistency_del, msg_del = Utils.verify_fo_lean !log !timeout lean_fol_of_consistency_del in

        if !log
          then begin printf "consistency_del = %d\n\n" is_consistency_del; end
          else ();

      (* --- result --- *)
      if (is_consistency_ins != 0) &&  (is_consistency_del != 0)
      then begin
        let result_ins = "Consistency is not satisfied about rules of " ^ (string_of_rterm goal_ins) ^ "\n." in
        let result_del = "Consistency is not satisfied about rules of " ^ (string_of_rterm goal_del) ^ "\n." in
        [result_ins; result_del]
      end
      else if (is_consistency_ins != 0) && (is_consistency_del = 0)
          then begin
            let result_ins = "Consistency is not satisfied about rules of " ^ (string_of_rterm goal_ins) ^ "\n." in
            [result_ins]
          end
      else if (is_consistency_ins = 0) && (is_consistency_del != 0)
          then begin
            let result_del = "Consistency is not satisfied about rules of " ^ (string_of_rterm goal_del) ^ "\n." in
            [result_del]
          end
      else
        []

  in

  let target_rel_lst = get_rels target_pred_lst in
  let pred_lst = evolved_bwd_pred_lst in
  let result = check_consistency ast_schemas ast_constraint ast_schevo ast_bwd source_pred_lst pred_lst target_rel_lst log timeout in

result
;;
