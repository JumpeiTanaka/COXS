(* @author: Jumpei Tanaka *)

  (* **************************************************************** *)
  (* Common tools for derivation of views and schemas                 *)
  (* **************************************************************** *)

open Expr;;
open Utils;;
open Tools;;
open Printf;;

(* get rel name of base relations *)
let get_base s_rel = "base_" ^ s_rel;;

(* get rel name of aux. relations *)
let get_nos_ins t_rel s_rel = "nos_i_" ^ t_rel ^ "_" ^ s_rel;;
let get_nos_del t_rel s_rel = "nos_d_" ^ t_rel ^ "_" ^ s_rel;;
let get_dif_ins t_rel = "dif_i_" ^ t_rel;;
let get_dif_del t_rel = "dif_d_" ^ t_rel;;

let get_aux_lost rel = "a_lost_" ^ rel;;
let get_aux_gain rel = "a_gain_" ^ rel;;
let get_aux_c rel = "a_c_" ^ rel;;

(* filter ast of constraint by rel_lst of schema  *)
let rec filter_constraint ast_constraint rels_schema = match ast_constraint with
  | Prog sttl -> _1_filter_constraint sttl rels_schema
  and _1_filter_constraint sttl rels_schema = match sttl with
    | [] -> []
    | hd::rest -> (_2_filter_constraint hd rels_schema) @ (_1_filter_constraint rest rels_schema)
  and _2_filter_constraint stt rels_schema = match stt with
    | Rule (get_empty_pred, bodylst) ->
        let constraint_rels = unique_element @@ get_rels_body (Prog [stt]) in
        if list_inclusion constraint_rels rels_schema
          then [stt]
          else []
    | _ -> invalid_arg "function generate_constraint2 without rule of constraint"
;;


(* change rel name of source to base *)
let rec source2base bodylst source_rels_schevo = match bodylst with
  | [] -> []
  | hd::rest -> (_1_source2base hd source_rels_schevo) @ (source2base rest source_rels_schevo)

  and _1_source2base tm source_rels_schevo  = match tm with
    | Rel (Pred(rel, varlst)) ->
        if List.mem rel source_rels_schevo
          then [Rel (Pred( (get_base rel), varlst))]
          else [tm]
    | Not (Pred(rel, varlst)) ->
        if List.mem rel source_rels_schevo
          then [Not (Pred( (get_base rel), varlst))]
          else [tm]
    | Rel (Deltainsert(rel, varlst)) ->
        if List.mem rel source_rels_schevo
          then [Rel (Deltainsert( (get_base rel), varlst))]
          else [tm]
    | Not (Deltadelete(rel, varlst)) ->
        if List.mem rel source_rels_schevo
          then [Not (Deltadelete( (get_base rel), varlst))]
          else [tm]
    | _ -> [tm]
;;


(* replace +t(X) to ins_t(X) or -t(X) to del_t(X) *)
let rec insdel_base body_sttl target_rel_lst = match body_sttl with
  | [] -> []
  | hd::rest -> (_1_insdel_base hd target_rel_lst) @ (insdel_base rest target_rel_lst)
  and _1_insdel_base tm target_rel_lst = match tm with
    | Rel(Deltainsert(rel, vars)) ->
        if List.mem rel target_rel_lst
          then [Rel(Pred(("ins_" ^ rel), vars))]
          else [tm]
    | Rel(Deltadelete(rel, vars)) ->
        if List.mem rel target_rel_lst
          then [Rel(Pred(("del_" ^ rel), vars))]
          else [tm]
    | Not(Deltainsert(rel, vars)) ->
        if List.mem rel target_rel_lst
          then [Not(Pred(("ins_" ^ rel), vars))]
          else [tm]
    | Not(Deltadelete(rel, vars)) ->
        if List.mem rel target_rel_lst
          then [Not(Pred(("del_" ^ rel), vars))]
          else [tm]
    | _ -> [tm]
;;

(* reform delta_relations in body to relations with ins_/del_ *)
let reform_prog_body_insdel prog  =

  let rec _0_reform prog  = match prog with
    | Prog sttl -> _1_reform sttl

    and _1_reform sttl  = match sttl with
      | [] -> []
      | hd::rest -> (_2_reform hd ) @ (_1_reform rest )

    and _2_reform hd = match hd with
      | Rule (Pred(rel, varlst), bodylst)
          ->  let bodylst_delta = _3_reform bodylst in
              [Rule (Pred(rel, varlst), bodylst_delta)]
      | Rule (Deltainsert(rel, varlst), bodylst)
          ->  let bodylst_delta = _3_reform bodylst in
              [Rule (Deltainsert(rel, varlst), bodylst_delta)]
      | Rule (Deltadelete(rel, varlst), bodylst)
          ->  let bodylst_delta = _3_reform bodylst in
              [Rule (Deltadelete(rel, varlst), bodylst_delta)]
      | _ -> invalid_arg "function eform_prog_insdel called without a rule"

    and _3_reform bodylst = match bodylst with
      | [] -> []
      | hd::rest -> (_4_reform hd ) @ (_3_reform rest )

   and _4_reform hd = match hd with
      | Rel (Pred(rel, varlst)) ->
          [hd]
      | Rel (Deltainsert(rel, varlst)) ->
          [Rel (Pred (("ins_" ^ rel), varlst))]
      | Rel (Deltadelete(rel, varlst)) ->
          [Rel (Pred (("del_" ^ rel), varlst))]
      | Not (Pred(rel, varlst)) ->
          [hd]
      | Not (Deltainsert(rel, varlst)) ->
          [Not (Pred (("ins_" ^ rel), varlst))]
      | Not (Deltadelete(rel, varlst)) ->
          [Not (Pred (("del_" ^ rel), varlst))]
      | _ -> [hd]
  in

  let result = Prog (_0_reform prog ) in
result
;;

(* **************************************************************
  Generate constraint
  Input: source ver1#s1(A,B), target ver2#t1(A,B)
         _|_ :- t1(A,B), A=1. _|_ :- s1(A,B), s1(A,B1), not B=B1. _|_ :- t2(X,Y.Z), not Z=1.
  Output: _|_ :- t1(A,B), A=1. _|_ :- base_s1(A,B), base_s1(A,B1), not B=B1.
************************************************************** *)
let generate_constraint schema ast_constraint base_rel_lst =

  let rec reform ast base_rel_lst = match ast with
    | Prog sttl -> _1_reform sttl base_rel_lst

    and _1_reform sttl base_rel_lst = match sttl with
      | [] -> []
      | hd::rest -> (_2_reform hd base_rel_lst) @ (_1_reform rest base_rel_lst)

    and _2_reform stt base_rel_lst = match stt with
      | Rule (Pred(rel, varlst), bodylst ) ->
              [ Rule ( Pred(rel, varlst), (_3_reform bodylst base_rel_lst) ) ]
      | _ -> invalid_arg "function reform called without rules in ast"

    and _3_reform bodylst base_rel_lst = match bodylst with
      | [] -> []
      | hd::rest -> (_4_reform hd base_rel_lst) @ (_3_reform rest base_rel_lst)

    and _4_reform tm base_rel_lst = match tm with
      | Rel (Pred(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then [Rel (Pred (("base_" ^ rel), varlst))]
          else [tm]
      | Rel (Deltainsert(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          (* then [Rel (Deltainsert (("base_" ^ rel), varlst))] *)
          then [Rel (Pred (("base_" ^ rel), varlst))]
          else [Rel (Pred (rel, varlst))]
      | Rel (Deltadelete(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then [Not (Pred (("base_" ^ rel), varlst))]
          else [Not (Pred (rel, varlst))]
      | Not (Pred(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then [Not (Pred(("base_" ^ rel), varlst))]
          else [Not (Pred(rel, varlst))]
      | Not (Deltainsert(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then [Rel (Pred(("base_" ^ rel), varlst))]
          else [Rel (Pred(rel, varlst))]
      | Not (Deltadelete(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then [Not (Pred(("base_" ^ rel), varlst))]
          else [tm]
      | _ -> [tm]
    in

  let rels_schema = get_rels_schema schema in
  let ast_base_constraint = Prog (reform ast_constraint base_rel_lst) in
  let filtered_constraint = Prog (filter_constraint ast_base_constraint rels_schema) in
  let reformed_constraint = reform_prog_body_insdel filtered_constraint in

reformed_constraint
;;

(* generate PK constraint between target and aux of diff *)
let generate_constraint_aux pk_lst target_pred ast_get =

  let rec get pk_lst target_rel target_varlst sttl_get = match pk_lst with
  | [] -> []
  | hd::rest -> (_1_get hd target_rel target_varlst sttl_get)
                @ (get rest  target_rel target_varlst sttl_get)
  and _1_get hd target_rel target_varlst sttl_get = match hd with
    | (rel, varlst) ->
        if rel = target_rel
        then
          let varlst_aux = get_varlst_aux varlst target_varlst in
          let build_in_lst = get_buildin varlst target_varlst in
          let rule_body_lst = get_body rel sttl_get in
          let aux_tm = Rel(Pred ("diff_" ^ rel, varlst_aux)) in
          let rule_lst = get_rules rule_body_lst aux_tm build_in_lst  in
          rule_lst
        else
          []

  and get_varlst_aux varlst target_varlst = match target_varlst with
    | [] -> []
    | hd::rest -> (_1_get_varlst_aux varlst hd) @ (get_varlst_aux varlst rest)
    and _1_get_varlst_aux varlst hd = match hd with
      | NamedVar (var) ->
        if List.mem var varlst
        then [NamedVar (var)]
        else [NamedVar (var ^ "1")]
      | _ -> []

  and get_buildin varlst target_varlst = match target_varlst with
    | [] -> []
    | hd::rest -> (_1_get_buildin varlst hd) @ (get_buildin varlst rest)
    and _1_get_buildin varlst hd = match hd with
      | NamedVar (var) ->
        if List.mem var varlst
        then []
        else [Ineq ("<>", Var(NamedVar(var)), Var(NamedVar(var ^ "1")))]
      | _ -> []

  and get_body rel sttl_get = match sttl_get with
    | [] -> []
    | hd::rest -> (_1_get_body rel hd) @ (get_body rel rest)
    and _1_get_body rel hd = match hd with
      | Rule (_, bodylst) -> [_2_get_body bodylst]
      | _ -> []
    and _2_get_body bodylst = match bodylst with
      | [] -> []
      | hd::rest -> (_3_get_body hd) @ (_2_get_body rest)
    and _3_get_body hd = match hd with
      | Rel _ -> [hd]
      | Not _ -> [hd]
      | _ -> [hd]

  and get_rules rule_body_lst aux_tm build_in_lst = match rule_body_lst with
    | [] -> []
    | hd::rest -> (_1_get_rules hd aux_tm build_in_lst) @ (get_rules rest aux_tm build_in_lst)
    and _1_get_rules body aux_tm build_in_lst = match build_in_lst with
      | [] -> []
      | hd::rest -> (_2_get_rules body aux_tm hd) @ (_1_get_rules body aux_tm rest)
    and _2_get_rules body aux_tm build_in =
        [Rule(get_empty_pred, ( body @ [aux_tm] @ [build_in] ) )]

  in

  let target_rel = get_rel_from_pred target_pred in
  let target_varlst = get_varlst_from_pred target_pred in
  let constraint_aux = Prog (get pk_lst target_rel target_varlst (get_sttl ast_get)) in

constraint_aux
;;


(* generate PK constraint between target and aux of Ad+ (naming of dif_aux is changed) *)
let generate_pk_constraint_aux_2 pk_lst target_pred ast_get =

  let rec get pk_lst target_rel target_varlst sttl_get ad_ins = match pk_lst with
  | [] -> []
  | hd::rest -> (_1_get hd target_rel target_varlst sttl_get ad_ins )
                @ (get rest  target_rel target_varlst sttl_get ad_ins )
  and _1_get hd target_rel target_varlst sttl_get ad_ins = match hd with
    | (rel, varlst) ->
        if rel = target_rel
        then
          let varlst_aux = get_varlst_aux varlst target_varlst in
          let build_in_lst = get_buildin varlst target_varlst in
          let rule_body_lst = get_body rel sttl_get in
          let aux_tm = Rel(Pred (ad_ins, varlst_aux)) in
          let rule_lst = get_rules rule_body_lst aux_tm build_in_lst  in
          rule_lst
        else
          []

  and get_varlst_aux varlst target_varlst = match target_varlst with
    | [] -> []
    | hd::rest -> (_1_get_varlst_aux varlst hd) @ (get_varlst_aux varlst rest)
    and _1_get_varlst_aux varlst hd = match hd with
      | NamedVar (var) ->
        if List.mem var varlst
        then [NamedVar (var)]
        else [NamedVar (var ^ "1")]
      | _ -> []

  and get_buildin varlst target_varlst = match target_varlst with
    | [] -> []
    | hd::rest -> (_1_get_buildin varlst hd) @ (get_buildin varlst rest)
    and _1_get_buildin varlst hd = match hd with
      | NamedVar (var) ->
        if List.mem var varlst
        then []
        else [Ineq ("<>", Var(NamedVar(var)), Var(NamedVar(var ^ "1")))]
      | _ -> []

  and get_body rel sttl_get = match sttl_get with
    | [] -> []
    | hd::rest -> (_1_get_body rel hd) @ (get_body rel rest)
    and _1_get_body rel hd = match hd with
      | Rule (_, bodylst) -> [_2_get_body bodylst]
      | _ -> []
    and _2_get_body bodylst = match bodylst with
      | [] -> []
      | hd::rest -> (_3_get_body hd) @ (_2_get_body rest)
    and _3_get_body hd = match hd with
      | Rel _ -> [hd]
      | Not _ -> [hd]
      | _ -> [hd]

  and get_rules rule_body_lst aux_tm build_in_lst = match rule_body_lst with
    | [] -> []
    | hd::rest -> (_1_get_rules hd aux_tm build_in_lst) @ (get_rules rest aux_tm build_in_lst)
    and _1_get_rules body aux_tm build_in_lst = match build_in_lst with
      | [] -> []
      | hd::rest -> (_2_get_rules body aux_tm hd) @ (_1_get_rules body aux_tm rest)
    and _2_get_rules body aux_tm build_in =
        [Rule(get_empty_pred, ( body @ [aux_tm] @ [build_in] ) )]

  in

  let target_rel = get_rel_from_pred target_pred in
  let target_varlst = get_varlst_from_pred target_pred in
  let ad_ins = get_dif_ins target_rel in
  let constraint_aux = Prog (get pk_lst target_rel target_varlst (get_sttl ast_get) ad_ins) in

constraint_aux
;;

(* Ad1+ ∩ Ad1- = ∅
   Ad1- ∩ ¬F1(Sb.nos) = ∅ *)
let generate_ad_aux_constraint_nos target_pred =

  let t_rel = get_rel_from_pred target_pred in
  let vars = get_varlst_from_pred target_pred in
  let ad_ins = get_dif_ins t_rel in
  let ad_del = get_dif_del t_rel in

  let result = Prog(
      [Rule(get_empty_pred, [Rel(Pred(ad_ins, vars)); Rel(Pred(ad_del, vars))]);
       Rule(get_empty_pred, [Rel(Pred(ad_del, vars)); Not(Pred(("nos_" ^ t_rel), vars))])
      ]
     )
  in

result
;;


(* Ad1+ ∩ Ad1- = ∅
   Ad1- ∩ ¬F1(Sb.nos) = ∅ *)
let generate_ad_aux_constraint_zero target_pred =

  let t_rel = get_rel_from_pred target_pred in
  let vars = get_varlst_from_pred target_pred in
  let ad_ins = get_dif_ins t_rel in
  let ad_del = get_dif_del t_rel in

  let result = Prog(
      [Rule(get_empty_pred, [Rel(Pred(ad_ins, vars)); Rel(Pred(ad_del, vars))]);
       Rule(get_empty_pred, [Rel(Pred(ad_del, vars)); Not(Pred(("zero_" ^ t_rel), vars))])
      ]
     )
  in

result
;;

(* generate mapping of (schema_ver, rel_name) for diff *)
let mpg_diff pred_lst log physical =

  let rec mapping rel_lst physical = match rel_lst with
    | [] -> []
    | hd::rest -> (_1_mapping hd physical) @ (mapping rest physical)
    and _1_mapping rel physical =
      [(!physical, "diff_" ^ rel) ]
  in

  let rel_lst = get_rels pred_lst in
  let diff_mpg = mapping rel_lst physical in
      if !log
      then begin
            printf "diff_mpg => [";
            let print_el s = printf "(%s, %s); " (fst s) (snd s) in
            List.iter print_el diff_mpg;
            printf "]\n\n";
     end
     else
      ();

diff_mpg
;;

(* show BIRDS result *)
let show_result result =

  let status_lst = List.filter (fun x -> match x with 0 -> false | _ -> true) (List.map fst result) in
  let sql_lst = List.map snd result in

  if (List.length status_lst) != 0
  then begin
    print_endline "\n\n-------------------------------------------------------.";
    print_endline "BIRDS process are failed."
  end
  else begin
    print_endline "\n\n-------------------------------------------------------.";
    print_endline "All BIRDS process are succeeded.";
    printf "Generated SQL files  => [";
    let print_el s = printf "%s; " s in
    List.iter print_el sql_lst;
    printf "]\n\n"
    end
;;



(* **************************************************************
  Generate get_t_sb
  Input: list of rules, e.g. t1(A,B) :- s1(A,B). ,
         list of source relation names,
         prefix to be added
  Output: list of rules, e.g.
          t1(A,B) :- base_s1(A,B).
************************************************************** *)
let gen_get_t_sb ast source_rels prefix =

  let rec reform sttl = match sttl with
    | [] -> []
    | hd::rest -> (_1_reform hd) @ (reform rest)

    and _1_reform stt = match stt with
      | Rule (Pred(rel, varlst), bodylst) ->
              [ Rule ( Pred(rel, varlst), (_2_reform bodylst) ) ]
      | _ -> invalid_arg "function gen_get_t_sb without rules in ast"

    and _2_reform bodylst = match bodylst with
      | [] -> []
      | hd::rest -> (_3_reform hd) @ (_2_reform rest)

    and _3_reform tm = match tm with
      | Rel (Pred (rel_name, varlst)) ->
         if List.mem rel_name source_rels
          then [Rel (Pred (prefix ^ rel_name, varlst))]
          else [tm]
      | Not (Pred (rel_name, varlst)) ->
         if List.mem rel_name source_rels
          then [Not (Pred (prefix ^ rel_name, varlst))]
          else [tm]
      | _ -> [tm]
    in

  let result = Prog (reform @@ get_sttl ast ) in
result
;;

(* **************************************************************
  Generate get_t_sb based on updated base_relations
  Input: t1(A,B) :- s1_0(A,B).
         s1_0(A,B) :- base_s1_0(A,B)
  Output: new_t1(A,B) :- new_s1_0(A,B).
          new_s1_0(A,B) :- new_base_s1_0(A,B)
************************************************************** *)
let gen_get_t_sb_new ast s_rel source_rels prefix =

  let rec reform sttl head_rels = match sttl with
    | [] -> []
    | hd::rest -> (_1_reform hd head_rels) @ (reform rest head_rels)

    and _1_reform stt  head_rels = match stt with
      | Rule (Pred(rel, varlst), bodylst) ->
              [ Rule ( Pred("new_" ^ rel, varlst), (_2_reform bodylst head_rels) ) ]
      | _ -> invalid_arg "function gen_get_t_sb without rules in ast"

    and _2_reform bodylst head_rels = match bodylst with
      | [] -> []
      | hd::rest -> (_3_reform hd head_rels) @ (_2_reform rest head_rels)

    and _3_reform tm head_rels = match tm with
      | Rel (Pred (rel_name, varlst)) ->
         if (List.mem rel_name source_rels) && (rel_name = s_rel) && not (List.mem rel_name head_rels)
          then [Rel (Pred ("new_" ^ prefix ^ rel_name, varlst))]
        else if (List.mem rel_name source_rels) && not (rel_name = s_rel) && not (List.mem rel_name head_rels)
          then [Rel (Pred (prefix ^ rel_name, varlst))]
        else if not (List.mem rel_name source_rels) && not (rel_name = s_rel) && (List.mem rel_name head_rels)
          then [Rel (Pred ("new_" ^ rel_name, varlst))]
        else [tm]
      | Not (Pred (rel_name, varlst)) ->
         if (List.mem rel_name source_rels) && (rel_name = s_rel) && not (List.mem rel_name head_rels)
          then [Not (Pred ("new_" ^ prefix ^ rel_name, varlst))]
        else if (List.mem rel_name source_rels) && not (rel_name = s_rel) && not (List.mem rel_name head_rels)
          then [Not (Pred (prefix ^ rel_name, varlst))]
        else if not (List.mem rel_name source_rels) && not (rel_name = s_rel) && (List.mem rel_name head_rels)
          then [Not (Pred ("new_" ^ rel_name, varlst))]
        else [tm]
      | _ -> [tm]
    in

  let head_rels = get_rels_head ast in
  let result = Prog (reform (get_sttl ast) head_rels) in
result
;;

(* exclude rule of schem evolution from ast_bwd *)
let exculde_schevo ast_bwd target_rel =

  let rec gen sttl target_rel = match sttl with
    | [] -> []
    | hd::rest -> (_1_gen hd target_rel) @ (gen rest target_rel)
    and _1_gen stt target_rel = match stt with
      | Rule(Pred(rel,var), body) ->
          if rel = target_rel
            then []
            else [stt]
      | _ -> [stt]
  in

  let result = Prog( gen (get_sttl ast_bwd) target_rel ) in

result
;;
