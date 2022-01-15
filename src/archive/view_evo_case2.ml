(* @author: Jumpei Tanaka *)

  (* **************************************************************** *)
  (* Step 4-2: Evolutional relations: case2                           *)
  (*   schema evolution by non-selection and backward propagation     *)
  (* **************************************************************** *)

open Expr;;
open Utils;;
open Tools;;
open View_common;;
open Printf;;

(*********************************************
  Reform predicate of relation name in source schema into name of base relation
  In: e.g.
      bodylst:     [+t1(A,B), not s1(A,B), B=1]
      base_rel_lst: [base_s1]
  Out: e.g.
      reformed_bodylst: [+t1(A,B), not base_s1(A,B), B=1]
*********************************************)
let rec reform_body_base bodylst base_rel_lst = match bodylst with
      | [] -> []
      | hd::rest -> (_1_reform hd base_rel_lst) @ (reform_body_base rest base_rel_lst)
    and _1_reform tm base_rel_lst = match tm with
      | Rel (Pred(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then [Rel (Pred (("base_" ^ rel), varlst))]
          else [tm]
      | Rel (Deltainsert(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then [Rel (Deltainsert (("base_" ^ rel), varlst))]
          else [tm]
      | Rel (Deltadelete(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then [Rel (Deltadelete (("base_" ^ rel), varlst))]
          else [tm]
      | Not (Pred(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then [Not (Pred(("base_" ^ rel), varlst))]
          else [tm]
      | Not (Deltainsert(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then [Rel (Deltainsert (("base_" ^ rel), varlst))]
          else [tm]
      | Not (Deltadelete(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then [Rel (Deltadelete (("base_" ^ rel), varlst))]
          else [tm]
      | _ -> [tm]
;;

(*********************************************
  Reform predicate of base relation name in source schema into name_new of base relation
  In: e.g.
      bodylst:     [+t1(A,B), not base_s1(A,B), B=1]
      base_rel_lst: [base_s1]
  Out: e.g.
      reformed_bodylst: [+t1(A,B), not base_s1_new(A,B), B=1]
*********************************************)
let reform_body_base_new bodylst base_rel_lst =

    let rec reform bodylst base_rel_lst = match bodylst with
      | [] -> []
      | hd::rest -> (_1_reform hd base_rel_lst) @ (reform rest base_rel_lst)
    and _1_reform tm base_rel_lst = match tm with
      | Rel (Pred(rel, varlst)) ->
          if List.mem rel base_rel_lst
          then begin [Rel (Pred ((rel ^ "_new"), varlst))] end
          else begin [tm] end
      | Not (Pred(rel, varlst)) ->
          if List.mem rel base_rel_lst
          then begin [Not (Pred((rel ^ "_new"), varlst))] end
          else begin [tm] end
      | _ -> [tm]
    in

    let bodylst_new = reform bodylst base_rel_lst in
bodylst_new
;;

(*********************************************
  Reform predicate of base relation name in source schema into name_new of base relation
  In: e.g.
      bodylst:     [+t1(A,B), not base_s1(A,B), B=1]
  Out: e.g.
      reformed_bodylst: [ins_t1(A,B), not base_s1(A,B), B=1]
*********************************************)
let rec reform_body_insdel bodylst =

  let rec reform bodylst = match bodylst with
    | [] -> []
    | hd::rest -> (_1_reform hd) @ (reform rest)
    and _1_reform tm  = match tm with
      | Rel(Deltainsert(rel, varlst)) -> [Rel(Pred("ins_" ^ rel, varlst))]
      | Rel(Deltadelete(rel, varlst)) -> [Rel(Pred("del_" ^ rel, varlst))]
      | Not(Deltainsert(rel, varlst)) -> [Not(Pred("ins_" ^ rel, varlst))]
      | Not(Deltadelete(rel, varlst)) -> [Not(Pred("del_" ^ rel, varlst))]
      | _ -> [tm]
  in

  let reformed_bodylst = reform bodylst in
reformed_bodylst
;;



(*********************************************
  In: target_pred
  Out: pred of aux relation
*********************************************)
let get_aux_pred target_pred = match target_pred with
  | Pred(rname, varlst) -> Pred("diff_" ^ rname, varlst)
  | _ -> invalid_arg "function sget_aux_pred  called without a Pred"
;;

(*********************************************
  In: target_pred
  Out: insertion of pred of aux relation
*********************************************)
let get_aux_pred_ins target_pred = match target_pred with
  | Pred(rname, varlst) -> Deltainsert("diff_" ^ rname, varlst)
  | _ -> invalid_arg "function sget_aux_pred  called without a Pred"
;;

(*********************************************
  In: AST of schema, pred of target schema, AST of rules for target schema
  Out: AST of BIRDS program for schema
*********************************************)
let generate_schema_2_noaux ast_schemas ast_bwd target_pred ast_pred base_rel_sttl base_rel_lst =

  let rec generate_view ast_schemas pred_rel_name = match ast_schemas with
    | Prog sttl -> _1_generate_view sttl pred_rel_name
    and _1_generate_view sttl pred_rel_name = match sttl with
      | [] -> []
      | hd::rest -> (_2_generate_view hd pred_rel_name) @ (_1_generate_view rest pred_rel_name)
    and _2_generate_view stt pred_rel_name = match stt with
      | Target_schema (_, rel, varlst) ->
          if rel = pred_rel_name
          then [View (rel, varlst)]
          else []
      | _ -> []
  in

  let rec generate_source_fwd ast_pred base_rel_sttl base_rel_lst = match ast_pred with
    | Prog sttl -> _1_generate_source_fwd sttl base_rel_sttl base_rel_lst
    and _1_generate_source_fwd sttl base_rel_sttl base_rel_lst = match sttl with
      | [] -> []
      | hd::rest -> (_2_generate_source_fwd hd base_rel_sttl base_rel_lst)
                    @ (_1_generate_source_fwd rest base_rel_sttl base_rel_lst)
    and _2_generate_source_fwd stt base_rel_sttl base_rel_lst = match stt with
      | Rule (Pred(rel, varlst), bodylst) -> _3_generate_source_fwd bodylst base_rel_sttl base_rel_lst
      | _ -> []
    and _3_generate_source_fwd bodylst base_rel_sttl base_rel_lst = match bodylst with
      | [] -> []
      | hd::rest -> (_4_generate_source_fwd hd base_rel_sttl base_rel_lst)
                      @ (_3_generate_source_fwd rest base_rel_sttl base_rel_lst)
    and _4_generate_source_fwd tm base_rel_sttl base_rel_lst = match tm with
      | Rel (Pred (rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then _5_generate_source_fwd rel base_rel_sttl
          else []
      | Not (Pred (rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then _5_generate_source_fwd rel base_rel_sttl
          else []
      | _ -> []
    and _5_generate_source_fwd rel base_rel_sttl = match base_rel_sttl with
      | [] -> []
      | hd::rest -> (_6_generate_source_fwd rel hd) @ (_5_generate_source_fwd rel rest)
    and _6_generate_source_fwd rel stt = match stt with
      | Source (rel_name, varlst) ->
          if rel_name = ("base_" ^ rel)
          then [stt]
          else []
      | _ -> []
  in

  let rec generate_source_bwd ast_bwd base_rel_sttl base_rel_lst = match ast_bwd with
    | Prog sttl -> _1_generate_source_bwd sttl base_rel_sttl base_rel_lst

    and _1_generate_source_bwd sttl base_rel_sttl base_rel_lst = match sttl with
      | [] -> []
      | hd::rest -> (_2_generate_source_bwd hd base_rel_sttl base_rel_lst)
                    @ (_1_generate_source_bwd rest base_rel_sttl base_rel_lst)

    and _2_generate_source_bwd stt base_rel_sttl base_rel_lst = match stt with
      | Rule (Pred(rel, varlst), bodylst) ->
            body_generate_source_bwd bodylst base_rel_sttl base_rel_lst
      | Rule (Deltainsert(rel, varlst), bodylst) ->
            (head_generate_source_bwd rel base_rel_sttl base_rel_lst)
            @ (body_generate_source_bwd bodylst base_rel_sttl base_rel_lst)
      | Rule (Deltadelete(rel, varlst), bodylst) ->
            (head_generate_source_bwd rel base_rel_sttl base_rel_lst)
            @ (body_generate_source_bwd bodylst base_rel_sttl base_rel_lst)
      | _ -> []

    and head_generate_source_bwd rel base_rel_sttl base_rel_lst =
      if List.mem ("base_" ^ rel) base_rel_lst
        then stt_generate_source_bwd rel base_rel_sttl
        else []

    and body_generate_source_bwd bodylst base_rel_sttl base_rel_lst = match bodylst with
      | [] -> []
      | hd::rest -> (_1_body_generate_source_bwd hd base_rel_sttl base_rel_lst)
                      @ (body_generate_source_bwd rest base_rel_sttl base_rel_lst)
    and _1_body_generate_source_bwd tm base_rel_sttl base_rel_lst = match tm with
      | Rel (Pred (rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then stt_generate_source_bwd rel base_rel_sttl
          else []
      | Not (Pred (rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then stt_generate_source_bwd rel base_rel_sttl
          else []
      | _ -> []

    and stt_generate_source_bwd rel base_rel_sttl = match base_rel_sttl with
      | [] -> []
      | hd::rest -> (_1_stt_generate_source_bwd rel hd) @ (stt_generate_source_bwd rel rest)
    and _1_stt_generate_source_bwd rel stt = match stt with
      | Source (rel_name, varlst) ->
          if rel_name = ("base_" ^ rel)
          then [stt]
          else []
      | _ -> []
  in

  let pred_rel_name = get_predname target_pred in
  let view_sttl = generate_view ast_schemas pred_rel_name in
  let fwd_source_sttl = generate_source_fwd ast_pred base_rel_sttl base_rel_lst in
  let ast_bwd_pred = filter_bwd ast_bwd target_pred in
  let bwd_source_sttl = generate_source_bwd ast_bwd_pred base_rel_sttl base_rel_lst in
  let source_sttl = unique_element (fwd_source_sttl @ bwd_source_sttl) in
  let ast_schema_2 = Prog (view_sttl @ source_sttl) in

  (*
      print_endline "ast_schemas:"; Expr.print_ast ast_schemas; printf "\n";
      print_endline "ast_pred:"; Expr.print_ast ast_pred; printf "\n";
      print_endline "ast_bwd_pred:"; Expr.print_ast ast_bwd_pred; printf "\n";
      printf "pred_rel_name = %s\n" pred_rel_name;
      print_endline "view_sttl:"; Expr.print_sttlst view_sttl; printf "\n";
      print_endline "fwd_source_sttl:"; Expr.print_sttlst fwd_source_sttl; printf "\n";
      print_endline "bwd_source_sttl:"; Expr.print_sttlst bwd_source_sttl; printf "\n";
      print_endline "ast_schema_2:"; Expr.print_ast ast_schema_2; printf "\n";
 *)

ast_schema_2
;;

(* generate source schema of aux *)
let generate_aux_shcema ast_schemas target_pred =

  let rec generate_aux ast_schemas pred_rel_name = match ast_schemas with
    | Prog sttl -> _1_generate_aux sttl pred_rel_name
    and _1_generate_aux sttl pred_rel_name = match sttl with
      | [] -> []
      | hd::rest -> (_2_generate_aux hd pred_rel_name) @ (_1_generate_aux rest pred_rel_name)
    and _2_generate_aux stt pred_rel_name = match stt with
      | Target_schema (_, rel, varlst) ->
          if rel = pred_rel_name
          then [Source ("diff_" ^ rel, varlst)]
          else []
      | _ -> []
  in

  let pred_rel_name = get_predname target_pred in
  let aux_sttl = generate_aux ast_schemas pred_rel_name in

aux_sttl
;;



(* **************************************************************
  Generate get_t_sb
  Input: list of rules, e.g. t1(A,B) :- s1(A,B). ,
         predicate of evolved relation,
         list of base relation names
  Output: list of rules, e.g.
          t1(A,B) :- base_s1(A,B).
************************************************************** *)
let generate_get_t_sb ast pred base_rel_lst =

  let rec reform ast pred base_rel_lst = match ast with
    | Prog sttl -> _1_reform sttl pred base_rel_lst

    and _1_reform sttl pred base_rel_lst = match sttl with
      | [] -> []
      | hd::rest -> (_2_reform hd pred base_rel_lst) @ (_1_reform rest pred base_rel_lst)

    and _2_reform stt pred base_rel_lst = match stt with
      | Rule (Pred(rel, varlst), bodylst ) ->
              [ Rule ( Pred(rel, varlst), (reform_body_base bodylst base_rel_lst) ) ]
      | _ -> invalid_arg "function reform_ast_pred called without rules in ast"
    in

  let result = Prog (reform ast pred base_rel_lst) in
result
;;

(* **************************************************************
  Generate get_t_sb
  Input: list of rules, e.g. t1(A,B) :- s1(A,B). ,
         predicate of evolved relation,
         list of base relation names
  Output: list of rules, e.g.
          t1_0(A,B) :- base_s1(A,B).
************************************************************** *)
let generate_get_0 ast pred base_rel_lst =

  let rec reform ast pred base_rel_lst = match ast with
    | Prog sttl -> _1_reform sttl pred base_rel_lst

    and _1_reform sttl pred base_rel_lst = match sttl with
      | [] -> []
      | hd::rest -> (_2_reform hd pred base_rel_lst) @ (_1_reform rest pred base_rel_lst)

    and _2_reform stt pred base_rel_lst = match stt with
      | Rule (Pred(rel, varlst), bodylst ) ->
              [ Rule ( Pred(rel ^ "_0", varlst), (reform_body_base bodylst base_rel_lst) ) ]
      | _ -> invalid_arg "function reform_ast_pred called without rules in ast"
    in

  let result = Prog (reform ast pred base_rel_lst) in
result
;;

(* **************************************************************
  Generate get_2
  Input: e.g.
          get_t_sb:    t1(A,B) :- base_s1(A,B).
          target_pred: t1(A,B)
          aux_pred:    diff_t1(A,B)
  Output: e.g.
          t1(A,B) :- base_s1(A,B).
          t1(A,B) :- diff_t1(A,B).
************************************************************** *)
let generate_get_2 ast_get_t_sb target_pred aux_pred =
  let ast_aux = Prog ( [Rule(target_pred, [Rel(aux_pred)])] ) in
  let ast_get_2 =  merge_ast ast_get_t_sb ast_aux in

ast_get_2
;;

(* **************************************************************
  Generate put_t_sb
  Input: e.g.
          source_rels2:    [s1(A,B)]
          ast_bwd_pred:    +s1(A,B) :- +t1(A,B), not s1(A,B), B=1.
                           -s1(A,B) :- -t1(A,B), s1(A,B), B=1.
          target_pred:     t1(A,B)
          ast_get_2:       t1(A,B) :- base_s1(A,B), B=1.
                           t1(A,B) :- diff_t1(A,B).
          base_rel_lst:    [base_s1(A,B)]
  Output: e.g.
          +base_s1(A,B)  :- ins_t(Y), not base_s1(A,B), B=1.
          −base_s1(A,B)  :- del_t(Y), .base_s1(A,B), B=1.
          ins_t1(A,B) :- t(A,B), ¬ttmp(A,B).
          del_t1(A,B) :- ¬t(A,B), ttmp(A,B).
          tmp_t(A,B) :- base_s1(A,B), B=1.
          tmp_t(A,B) :- diff_t1(A,B).
************************************************************** *)
let generate_putdelta_t_sb ast_bwd_pred target_pred ast_get_2 base_rel_lst =

  let rec get_f_prime_rule ast_bwd_lst base_rel_lst ast_bwd_lst2 = match ast_bwd_lst with
    | [] -> []
    | hd::rest -> (_1_get_f_prime_rule hd base_rel_lst ast_bwd_lst2) @ (get_f_prime_rule rest base_rel_lst ast_bwd_lst2)
    and _1_get_f_prime_rule stt base_rel_lst ast_bwd_lst2 = match stt with
      | Rule (Pred(rel, varlst), bodylst) ->
          let reformed_bodylst = reform_body_insdel (reform_body_base bodylst base_rel_lst) in
          let delta_rule_lst = get_delta_rules bodylst ast_bwd_lst2 base_rel_lst in
          if List.mem ("base_" ^ rel) base_rel_lst
          then
            [Rule (Pred("base_" ^ rel, varlst), reformed_bodylst)] @ delta_rule_lst
          else
            [Rule (Pred(rel, varlst), reformed_bodylst)] @ delta_rule_lst

      | Rule (Deltainsert(rel, varlst), bodylst) ->
          let reformed_bodylst = reform_body_insdel (reform_body_base bodylst base_rel_lst) in
          let delta_rule_lst = get_delta_rules bodylst ast_bwd_lst2 base_rel_lst in
          if List.mem ("base_" ^ rel) base_rel_lst
          then
            [Rule (Deltainsert("base_" ^ rel, varlst), reformed_bodylst)] @ delta_rule_lst
          else
            [Rule (Deltainsert(rel, varlst), reformed_bodylst)] @ delta_rule_lst

      | Rule (Deltadelete(rel, varlst), bodylst) ->
          let reformed_bodylst = reform_body_insdel (reform_body_base bodylst base_rel_lst) in
          let delta_rule_lst = get_delta_rules bodylst ast_bwd_lst2 base_rel_lst in
          if List.mem ("base_" ^ rel) base_rel_lst
          then
            [Rule (Deltadelete("base_" ^ rel, varlst), reformed_bodylst)] @ delta_rule_lst
          else
            [Rule (Deltadelete(rel, varlst), reformed_bodylst)] @ delta_rule_lst
      | _ -> []

    and get_delta_rules bodylst ast_bwd_lst2 base_rel_lst = match bodylst with
      | [] -> []
      | hd::rest -> (_1_get_delta_rules hd ast_bwd_lst2 base_rel_lst)
                    @ (get_delta_rules rest ast_bwd_lst2 base_rel_lst)
      and _1_get_delta_rules tm ast_bwd_lst2 base_rel_lst = match tm with
        | Rel(Deltainsert(rel, varlst)) ->
            if List.mem ("base_" ^ rel) base_rel_lst
            then ins_get_delta_rules rel ast_bwd_lst2 base_rel_lst
            else []
        | Rel(Deltadelete(rel, varlst)) ->
            if List.mem ("base_" ^ rel) base_rel_lst
            then del_get_delta_rules rel ast_bwd_lst2 base_rel_lst
            else []
        | Not(Deltainsert(rel, varlst)) ->
            if List.mem ("base_" ^ rel) base_rel_lst
            then ins_get_delta_rules rel ast_bwd_lst2 base_rel_lst
            else []
        | Not(Deltadelete(rel, varlst)) ->
            if List.mem ("base_" ^ rel) base_rel_lst
            then del_get_delta_rules rel ast_bwd_lst2 base_rel_lst
            else []
        | _ -> []

    and ins_get_delta_rules rel bwd_sttl base_rel_lst = match bwd_sttl with
      | [] -> []
      | hd::rest -> (_1_ins_get_delta_rules rel hd base_rel_lst)
                    @ (ins_get_delta_rules rel rest base_rel_lst)
      and _1_ins_get_delta_rules rel stt base_rel_lst = match stt with
        | Rule (Deltainsert (ins_rel, ins_varlst), ins_bodylst) ->
          if rel = ins_rel
          then begin
            let reformed_ins_bodylst = reform_body_insdel (reform_body_base ins_bodylst base_rel_lst) in
            [Rule (Pred ("ins_base_" ^ins_rel, ins_varlst), reformed_ins_bodylst)]
            end
          else
            []
        | _ -> []

    and del_get_delta_rules rel bwd_sttl base_rel_lst = match bwd_sttl with
      | [] -> []
      | hd::rest -> (_1_del_get_delta_rules rel hd base_rel_lst)
                     @ (del_get_delta_rules rel rest base_rel_lst)
      and _1_del_get_delta_rules rel stt base_rel_lst = match stt with
        | Rule (Deltadelete (del_rel, del_varlst), del_bodylst) ->
          if rel = del_rel
          then begin
            let reformed_ins_bodylst = reform_body_insdel (reform_body_base del_bodylst base_rel_lst) in
            [Rule (Pred ("del_base_" ^del_rel, del_varlst), reformed_ins_bodylst)]
            end
          else
            []
        | _ -> []

  in

  let get_delta_target_rule target_pred = match target_pred with
    | Pred(rel, varlst) ->
      [
        Rule( Pred("ins_" ^ rel, varlst), [Rel(Pred(rel, varlst)); Not(Pred("tmp_" ^ rel, varlst))]);
        Rule( Pred("del_" ^ rel, varlst), [Not(Pred(rel, varlst)); Rel(Pred("tmp_" ^ rel, varlst))])
      ]
    | _ -> invalid_arg "function get_delta_target_rule without a predicate"
  in

  let rec get_tmp_target_rule get_2_sttl target_pred = match get_2_sttl with
    | [] -> []
    | hd::rest -> (_1_get_tmp_target_rule hd target_pred) @ (get_tmp_target_rule rest target_pred)
  and _1_get_tmp_target_rule stt target_pred = match stt with
    | Rule (Pred(rel, varlst), bodylst) ->
        if Pred(rel, varlst) = target_pred
        then  [Rule (Pred("tmp_" ^ rel, varlst), bodylst)]
        else [stt]
    | _ -> []
  in

  let f_prime_rule_lst = get_f_prime_rule (get_sttl ast_bwd_pred) base_rel_lst (get_sttl ast_bwd_pred) in
  let delta_target_rule_lst = get_delta_target_rule target_pred in
  let tmp_target_rule_lst = get_tmp_target_rule (get_sttl ast_get_2) target_pred in

  let ast_put_t_sb = Prog (f_prime_rule_lst @ delta_target_rule_lst @ tmp_target_rule_lst) in

ast_put_t_sb
;;


(* **************************************************************
  Generate put_t_a
  Input: e.g.
          target_pred:     t1(A,B)
          aux_pred:        diff_t1(A,B)
          source_pred_lst:  [s1(A.B)]
          base_rel_lst:    [base_s1]
  Output: e.g.
          +diff_t1(A,B)  :- t1(A,B), not t1_pp(A,B), not diff_t1(A,B).
          -diff_t1(A,B)  :- not t1(A,B), diff_t1(A,B).
          base_s1_new(A,B) :- base_s1(A,B), not -base_s1(A,B).
          base_s1_new(A,B) :- +base_s1(A,B).
          t1_pp(A,B) :- base_s1_new(A,B), B=1.
************************************************************** *)
let generate_putdelta_t_a target_pred aux_pred source_pred_lst base_rel_lst ast_get_t_sb source_ins_rels source_del_rels =

  let get_aux_rule target_pred aux_pred =
    let target_rel = get_rel_from_pred target_pred in
    let target_varlst = get_varlst_from_pred target_pred in
    let aux_rel = get_rel_from_pred aux_pred in
    let aux_varlst = get_varlst_from_pred aux_pred in

    let aux_rule_lst =
      [ Rule (Deltainsert(aux_rel, aux_varlst),
              [Rel(Pred(target_rel, target_varlst)); Not(Pred(target_rel ^ "_pp", target_varlst));
               Not(Pred(aux_rel, aux_varlst))]
             );
        Rule (Deltadelete(aux_rel, aux_varlst),
              [Not(Pred(target_rel, target_varlst)); Rel(Pred(aux_rel, aux_varlst))]
             );
      ]
    in
  aux_rule_lst
  in

  let rec get_base_source_rule source_pred_lst base_rel_lst source_ins_rels source_del_rels = match source_pred_lst with
    | [] -> []
    | hd::rest -> (_1_get_base_source_rule hd base_rel_lst source_ins_rels source_del_rels)
                  @ (get_base_source_rule rest base_rel_lst source_ins_rels source_del_rels)
    and _1_get_base_source_rule pred base_rel_lst source_ins_rels source_del_rels = match pred with
      | Pred(rel, varlst) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then
            if (List.mem rel source_ins_rels) && (List.mem rel source_del_rels)
            then begin
              [Rule( Pred( "base_" ^ rel ^ "_new", varlst),
                     [Rel (Pred("base_" ^ rel, varlst)); Not(Deltadelete("base_" ^ rel, varlst))]
                   );
              Rule( Pred("base_" ^ rel ^ "_new", varlst),
                    [Rel(Deltainsert("base_" ^ rel, varlst))]
                  )
              ] end
            else
              if (List.mem rel source_ins_rels) && not (List.mem rel source_del_rels)
              then
                begin
                  [Rule( Pred( "base_" ^ rel ^ "_new", varlst),
                          [Rel (Pred("base_" ^ rel, varlst))]
                   );
                  Rule( Pred("base_" ^ rel ^ "_new", varlst),
                          [Rel(Deltainsert("base_" ^ rel, varlst))]
                  )
                  ] end
              else
                if not (List.mem rel source_ins_rels) && (List.mem rel source_del_rels)
                then
                  begin
                    [Rule( Pred( "base_" ^ rel ^ "_new", varlst),
                          [Rel (Pred("base_" ^ rel, varlst)); Not(Deltadelete("base_" ^ rel, varlst))] );
                    ]
                  end
                else
                  begin
                    [Rule( Pred( "base_" ^ rel ^ "_new", varlst),
                            [Rel (Pred("base_" ^ rel, varlst))]
                    )
                    ]
                  end
          else []
      | _ -> invalid_arg "function get_base_source_rule without Pred"
  in

  let rec get_target_pp_rule get_t_sb_sttl base_rel_lst target_pred head_rels = match get_t_sb_sttl with
    | [] -> []
    | hd::rest -> (_1_get_target_pp_rule hd base_rel_lst target_pred head_rels )
                  @ (get_target_pp_rule rest base_rel_lst target_pred head_rels )
    and _1_get_target_pp_rule hd base_rel_lst target_pred head_rels = match hd with
      | Rule (Pred(rel, valst), bodylst) ->
          let bodylst_new = reform_body_base_new bodylst base_rel_lst in

            let str = List.map string_of_term bodylst in
            printf "bodylst => [";
            let print_el s = printf "%s; " s in
            List.iter print_el str;
            printf "]\n\n";

            let str_new = List.map string_of_term bodylst_new in
            printf "bodylst_new => [";
            let print_el s = printf "%s; " s in
            List.iter print_el str_new;
            printf "]\n\n";

          if Pred(rel, valst) = target_pred
          then
            [Rule (Pred(rel ^ "_pp", valst), (_2_get_target_pp_rule bodylst_new head_rels)) ]
          else
            [Rule (Pred(rel ^ "_pp", valst), (_2_get_target_pp_rule bodylst_new head_rels)) ]
      | _ -> []

    and _2_get_target_pp_rule body_lst head_rels = match body_lst with
      | [] -> []
      | hd::rest -> (_3_get_target_pp_rule hd head_rels) @ (_2_get_target_pp_rule rest head_rels)

    and _3_get_target_pp_rule tm head_rels = match tm with
      | Rel (Pred (rel, varlst)) ->
          if (List.mem rel head_rels)
          then [Rel (Pred ((rel ^ "_pp"), varlst))]
          else [tm]
      | Not (Pred (rel, varlst)) ->
          if (List.mem rel head_rels)
          then [Not (Pred ((rel ^ "_pp"), varlst))]
          else [tm]
      | _ -> [tm]
  in

  let head_rels = get_rels_head ast_get_t_sb in

  let aux_rule_lst = get_aux_rule target_pred aux_pred in
  let base_source_rule_lst = get_base_source_rule source_pred_lst base_rel_lst source_ins_rels source_del_rels in
  let target_pp_rule_lst = get_target_pp_rule (get_sttl ast_get_t_sb) base_rel_lst target_pred head_rels in

    print_endline "-- aux_rule_lst : "; Expr.print_ast (Prog (aux_rule_lst )); printf "\n";
    print_endline "-- base_source_rule_lst : "; Expr.print_ast (Prog (base_source_rule_lst)); printf "\n";
    print_endline "-- target_pp_rule_lst : "; Expr.print_ast (Prog (target_pp_rule_lst )); printf "\n";

  let ast_putdelta_t_a = Prog (aux_rule_lst @ base_source_rule_lst @ target_pp_rule_lst) in

ast_putdelta_t_a
;;

(* generate ins_aux predicate for satisfiability check *)
let generate_aux_deltainsert target_pred = match target_pred with
  | Pred (name, varlst) -> Deltainsert ( ("diff_" ^ name), varlst)
  | _ -> invalid_arg "function generate_aux_deltainsert without Pred"
;;

(* -------------------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------------------- *)
(* Derive BIRdS program for case2 relaitons *)
let derivation_case2_birds ast_schemas ast_constraint ast_schevo ast_bwd evolved_bwd_pred_lst base_rel_sttl source_rels source_ins_rels source_del_rels source_pred_lst pk_lst log timeout =

  let rec derive_all_case2 ast_schemas ast_constraint ast_schevo ast_bwd pred_lst base_rel_sttl base_rel_lst source_rels source_ins_rels source_del_rels source_pred_lst pk_lst log = match pred_lst with
    | [] -> []
    | hd::rest ->
      (_1_derive_case2 ast_schemas ast_constraint ast_schevo ast_bwd hd base_rel_sttl base_rel_lst source_rels source_ins_rels source_del_rels source_pred_lst pk_lst log)
      @ (derive_all_case2 ast_schemas ast_constraint ast_schevo ast_bwd rest base_rel_sttl base_rel_lst source_rels source_ins_rels source_del_rels source_pred_lst pk_lst log)

    and _1_derive_case2 ast_schemas ast_constraint ast_schevo ast_bwd target_pred base_rel_sttl base_rel_lst source_rels source_ins_rels source_del_rels source_pred_lst pk_lst log =
      let ast_pred = get_one_query ast_schevo target_pred in
      let source_rels2 = get_rels_inbody ast_pred source_rels in
      let aux_pred = get_aux_pred target_pred in
      let ast_bwd_pred = get_queries ast_bwd source_rels2 in

      let ast_schema_2_noaux = generate_schema_2_noaux ast_schemas ast_bwd target_pred ast_pred base_rel_sttl base_rel_lst in
      let schema_aux = generate_aux_shcema ast_schemas target_pred in
      let ast_schema_2 = Prog ((get_sttl ast_schema_2_noaux) @ schema_aux) in

      let ast_get_t_sb = generate_get_t_sb ast_pred target_pred base_rel_lst in
      let ast_get_2 = generate_get_2 ast_get_t_sb target_pred aux_pred in

      let ast_putdelta_t_sb_noaux = generate_putdelta_t_sb ast_bwd_pred target_pred ast_get_t_sb base_rel_lst in
      let ast_putdelta_t_sb = generate_putdelta_t_sb ast_bwd_pred target_pred ast_get_2 base_rel_lst in


      let ast_putdelta_t_a = generate_putdelta_t_a target_pred aux_pred source_pred_lst base_rel_lst ast_get_t_sb source_ins_rels source_del_rels in
      let ast_putdelta_2 = merge_ast ast_putdelta_t_sb ast_putdelta_t_a in
      let ast_constraint_2_noaux = generate_constraint ast_schema_2 ast_constraint base_rel_lst in
      let ast_constraint_aux = generate_constraint_aux pk_lst target_pred ast_get_t_sb in
      let ast_constraint_2 = merge_ast ast_constraint_2_noaux ast_constraint_aux in

      let ast_2_noaux = List.fold_left merge_ast (Prog []) [ast_schema_2_noaux; ast_constraint_2_noaux; ast_get_t_sb; ast_putdelta_t_sb_noaux ]  in
      let ast_2_aux = List.fold_left merge_ast (Prog []) [ast_schema_2; ast_constraint_2; ast_get_2; ast_putdelta_2 ]  in

            if !log
            then begin
              print_endline "ast_pred: "; Expr.print_ast ast_pred; printf "\n";
              print_endline "ast_bwd_pred: "; Expr.print_ast ast_bwd_pred; printf "\n";
              print_endline "---------------------------------";

              print_endline "ast_schema_2_noaux: "; Expr.print_ast ast_schema_2_noaux; printf "\n";
              print_endline "ast_schema_2: "; Expr.print_ast ast_schema_2; printf "\n";

              print_endline "ast_constraint_aux: "; Expr.print_ast ast_constraint_aux; printf "\n";
              print_endline "ast_constraint_2: "; Expr.print_ast ast_constraint_2; printf "\n";

              print_endline "ast_get_t_sb: "; Expr.print_ast ast_get_t_sb; printf "\n";
              print_endline "ast_get_2: "; Expr.print_ast ast_get_2; printf "\n";

              print_endline "ast_putdelta_t_sb_noaux: "; Expr.print_ast ast_putdelta_t_sb_noaux; printf "\n";
              print_endline "ast_putdelta_t_sb: "; Expr.print_ast ast_putdelta_t_sb; printf "\n";
              print_endline "ast_putdelta_t_a: "; Expr.print_ast ast_putdelta_t_a; printf "\n";
              print_endline "ast_putdelta_2: "; Expr.print_ast ast_putdelta_2; printf "\n";

              print_endline "ast_2_noaux: "; Expr.print_ast ast_2_noaux; printf "\n";
              print_endline "ast_2_aux: "; Expr.print_ast ast_2_aux; printf "\n";


            end
            else
              ();

      (* ---------------------------------------------------------------------------------- *)
      (* check whether +diff_t is satisfiable or not, unsatisfiable then no need to use aux *)
      (* ---------------------------------------------------------------------------------- *)
      let aux_deltains = get_aux_pred_ins target_pred in
      let lean_fol_of_diff = Satisfiability.lean_diff ast_2_aux ast_schema_2 ast_constraint_2 ast_putdelta_2 aux_deltains log in

      let is_diff, msg = Utils.verify_fo_lean !log !timeout lean_fol_of_diff in
        printf "msg = %s\n" msg;
        printf "is_diff = %d\n" is_diff;

      let ast_2 =
        if is_diff = 0
        then [ast_2_noaux]
        else [ast_2_aux]
      in

            if !log
            then begin
              print_endline "ast_2: "; Expr.print_ast (List.hd ast_2); printf "\n";
            end
            else
              ();
  ast_2
  in

  (* -------------------------------------------------------------------------- *)
  let base_rel_lst = get_rels @@ Expr.source2pred base_rel_sttl in
        printf "base_rel_lst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el base_rel_lst;
        printf "]\n\n";

  let ast_lst = derive_all_case2 ast_schemas ast_constraint ast_schevo ast_bwd evolved_bwd_pred_lst base_rel_sttl base_rel_lst source_rels source_ins_rels source_del_rels source_pred_lst pk_lst log in

ast_lst
;;
