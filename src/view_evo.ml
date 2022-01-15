(* @author: Jumpei Tanaka *)

  (* **************************************************************** *)
  (* Step 4: Target schema                                            *)
  (* **************************************************************** *)

open Expr;;
open Utils;;
open Tools;;
open View_common;;
open Printf;;

(* **************************************************************
  Generate constratint core
  (exampe)
  Input: [s1(X,Y); s2(X,Z) ]
         _|_ :- s2(X,Z), not s1(X,_).
  Output: _|_ :- base_s2(X,Z), not base_s1(X,_).
************************************************************** *)
let generate_const_core_target ast_constraint_core source_pred_lst =

  let rec convert sttl_constraint_core source_rel_lst = match sttl_constraint_core with
    | [] -> []
    | hd::rest -> (_1_convert hd source_rel_lst) @ (convert rest source_rel_lst)

    and _1_convert stt source_rel_lst = match stt with
      | Rule (h, body) ->
          [Rule (h, (_2_convert body source_rel_lst))]
      | _ -> []

    and _2_convert body2 source_rel_lst = match body2 with
      | [] -> []
      | hd::rest -> (_3_convert hd source_rel_lst) @ (_2_convert rest source_rel_lst)

    and _3_convert tm source_rel_lst = match tm with
      | Rel(Pred(rel, varlst)) ->
          if List.mem rel source_rel_lst
              then [Rel(Pred("base_" ^ rel, varlst))]
              else [tm]
      | Rel(Deltainsert(rel, varlst)) ->
          if List.mem rel source_rel_lst
              then [Rel(Deltainsert("base_" ^ rel, varlst))]
              else [tm]
      | Rel(Deltadelete(rel, varlst)) ->
          if List.mem rel source_rel_lst
              then [Rel(Deltadelete("base_" ^ rel, varlst))]
              else [tm]
      | Not(Pred(rel, varlst)) ->
          if List.mem rel source_rel_lst
              then [Not(Pred("base_" ^ rel, varlst))]
              else [tm]
      | Not(Deltainsert(rel, varlst)) ->
          if List.mem rel source_rel_lst
              then [Not(Deltainsert("base_" ^ rel, varlst))]
              else [tm]
      | Not(Deltadelete(rel, varlst)) ->
          if List.mem rel source_rel_lst
              then [Not(Deltadelete("base_" ^ rel, varlst))]
              else [tm]
      | _ -> [tm]
  in

  let source_rel_lst = get_rels source_pred_lst in
  let result = Prog (convert (get_sttl ast_constraint_core) source_rel_lst ) in
result
;;


(* --------------------------------------------------------------
  Derive BIRdS program for taregt rel

  % schemas
    view t(X).            (* S: view *)
    source b_s(X).        (* Sb: base relation *)
    source dif_i_t(X).    (* Ad+: aux for diff *)
    source dif_d_t(X).    (* Ad-: aux for diff *)

  % constraint
     Ad1+ ∩ Ad1- = ∅
     Ad1- ∩ ¬S0 = ∅

  % get
    T1 = get_t(Sb, Ad+, Ad-)
       = (S0 ∩ ¬Ad-) ∪ Ad+
          S0 = get_t_sb(Sb) = F(Sb)

  % putdelta
    (Sb', Ad1+', Ad1-')
     = (Sb, Ad1+, Ad1-) ⨁ putdelta ((Sb, Ad1+, Ad1-), T1')

    % putdelta_base (for each Si)
    Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+
     ∆Sb+ = F1'+(Sb, ∆T1)
     ∆Sb- = F1'-(Sb, ∆T1)

    % diff
    % putdelta_ad1_ins
    Ad1+' = (Ad1+ ∩ ¬∆Ad1+-) ∪ ∆Ad1++
      ∆Ad1++ = T1' ∩ ¬T1'' ∩ ¬Ad1+
      ∆Ad1+- = ¬T1' ∩ Ad1+

    % putdelta_ad1_del
    Ad1-' = (Ad1- ∩ ¬∆Ad1--) ∪ ∆Ad1-+
      ∆Ad1-+ = ¬T1' ∩ T1'' ∩ ¬Ad1-
      ∆Ad1-- = (T1' ∩ Ad1-) ∪ (¬T1'' ∩ Ad1-)

      T'' = F1(Sb')

    % ∆T1
      ∆T1+ = T1' ∩ ¬T1_tmp
      ∆T1- = ¬T1' ∩ T1_tmp
         T1_tmp = get_t1( Sb, Ad1+, Ad1-)
                = (get_t1_sb(Sb) ∩ ¬Ad1-) ∪ Ad1+
 *)
(* -------------------------------------------------------------------------------------- *)
(* Derive BIRdS program for case2 relaitons *)
let derivation_target_birds_1 ast_schema ast_constraint_core ast_constraint_pk ast_schevo ast_bwd target_pred pk_lst init_ast_lst source_pred_lst log timeout =

  (* === parts ======================================================== *)
  let target_rel = get_rel_from_pred target_pred in
  let target_vars = get_varlst_from_pred target_pred in

  let source_preds_schevo =
    let rels_body = unique_element @@ get_rels_body ast_schevo in

    let rec filter rels_body source_pred_lst = match source_pred_lst with
      | [] -> []
      | hd::rest -> (_1_filter rels_body hd) @ (filter rels_body rest)
      and _1_filter rels_body tm = match tm with
        | Pred(rel, varlst) -> if List.mem rel rels_body then [tm] else []
        | _ -> []
    in

    filter rels_body source_pred_lst
  in

  let source_rels_schevo = get_rels source_preds_schevo in
  let source_ins_rels_bwd = get_ins_rels_head ast_bwd in
  let source_del_rels_bwd = get_del_rels_head ast_bwd in

      (*  printf "source_preds_schevo => [";
          let print_el s = printf "%s; " s in
          List.iter print_el (List.map string_of_rterm source_preds_schevo);
          printf "]\n";
        *)

  (* exclude rule of schem evolution from ast_bwd *)
  let ast_bwd_ex_schevo = exculde_schevo ast_bwd target_rel in

  (* ================================================================= *)
  (*    functions                                                      *)
  (* ================================================================= *)
  (* change rel name of source to new, others to nos_base *)
  let rec source2new bodylst source_rel source_rels_schevo rel_new = match bodylst with
    | [] -> []
    | hd::rest -> (_1_source2new hd source_rel source_rels_schevo rel_new)
                  @ (source2new rest source_rel source_rels_schevo rel_new)

    and _1_source2new tm source_rel source_rels_schevo rel_new = match tm with
      | Rel (Pred(rel, varlst)) ->
          if (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Rel (Pred(rel_new, varlst))]
          else if not (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Rel (Pred( ("nos_" ^ (get_base rel)), varlst))]
          else
            [tm]

      | Not (Pred(rel, varlst)) ->
          if (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Not (Pred(rel_new, varlst))]
          else if  not (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Not (Pred( ("nos_" ^ (get_base rel)), varlst))]
          else
            [tm]

      | Rel (Deltainsert(rel, varlst)) ->
          if (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Rel (Deltainsert(rel_new, varlst))]
          else if  not (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Not (Deltainsert( (get_base rel), varlst))]
          else
            [tm]

      | Not (Deltadelete(rel, varlst)) ->
          if (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Not (Deltadelete(rel_new, varlst))]
          else if  not (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Not (Deltadelete( (get_base rel), varlst))]
          else
            [tm]
      | _ -> [tm]
  in


  (* Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+ *)
  let new_gen_s_b source_preds_schevo source_ins_rels_bwd source_del_rels_bwd =

    (* Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+ *)
    let rec gen_base source_preds_schevo source_ins_rels_bwd source_del_rels_bwd = match source_preds_schevo with
      | [] -> []
      | hd::rest -> (_1_gen_base hd source_ins_rels_bwd source_del_rels_bwd)
                    @ (gen_base rest source_ins_rels_bwd source_del_rels_bwd)

      and _1_gen_base hd source_ins_rels_bwd source_del_rels_bwd = match hd with
        | Pred(rel, varlst) ->
            let base_rel = get_base rel in
            if (List.mem rel source_ins_rels_bwd) && (List.mem rel source_del_rels_bwd)
              then [ Rule (Pred(("pp_" ^ base_rel), varlst),
                           [Rel(Pred (base_rel, varlst)); Not(Deltadelete(base_rel, varlst))
                           ] );
                     Rule (Pred(("pp_" ^ base_rel), varlst),
                           [Rel(Deltainsert(base_rel, varlst))] )
                   ]
            else if (List.mem rel source_ins_rels_bwd) && not (List.mem rel source_del_rels_bwd)
              then [ Rule (Pred(("pp_" ^ base_rel), varlst),
                           [Rel(Pred (base_rel, varlst))] );
                     Rule (Pred(("pp_" ^ base_rel), varlst),
                           [Rel(Deltainsert(base_rel, varlst)) ] )
                   ]
            else if not (List.mem rel source_ins_rels_bwd) && (List.mem rel source_del_rels_bwd)
              then [  Rule (Pred(("pp_" ^ base_rel), varlst),
                           [Rel(Pred (base_rel, varlst)); Not(Deltadelete(base_rel, varlst))
                           ] )
                   ]
            else if not (List.mem rel source_ins_rels_bwd) && not (List.mem rel source_del_rels_bwd)
              then [ Rule (Pred(("pp_" ^ base_rel), varlst),
                          [Rel(Pred (base_rel, varlst))
                          ] )
                   ]
            else
             []

        | _ -> []
    in

    let new_base = gen_base source_preds_schevo source_ins_rels_bwd source_del_rels_bwd in
    let result = new_base in
  result
  in


  (* change s to base_s *)
  let rec gen_get_t_sb sttl_schevo source_rels_schevo = match sttl_schevo with
    | [] -> []
    | hd::rest -> (_1_gen_get hd source_rels_schevo) @ (gen_get_t_sb rest source_rels_schevo)

    and _1_gen_get stt source_rels_schevo = match stt with
      | Rule (Pred(rel, varlst), bodylst)
          -> [Rule (Pred("zero_" ^ rel, varlst), (_2_gen_get bodylst source_rels_schevo))]
      | _ -> []

    and _2_gen_get bodylst source_rels_schevo = match bodylst with
      | [] -> []
      | hd::rest -> (_3_gen_get hd source_rels_schevo)
                    @ (_2_gen_get rest source_rels_schevo)

    and _3_gen_get tm source_rels_schevo = match tm with
      | Rel(Pred(rel, varlst)) ->
           if List.mem rel source_rels_schevo
            then [Rel(Pred((get_base rel), varlst))]
            else [Rel(Pred("zero_" ^ rel, varlst))]
      | Not(Pred(rel, varlst)) ->
          if List.mem rel source_rels_schevo
            then [Not(Pred((get_base rel), varlst))]
            else [Not(Pred("zero_" ^ rel, varlst))]
      | _ -> [tm]
  in

  (* new_get *)
  let new_gen_get_t1_sb ast_schevo source_preds_schevo source_rels_schevo =

    (* Sb_nos' = (Sb' ∩ A2+') ∪ A2-' *)
    let rec gen sttl_schevo head_rels = match sttl_schevo with
      | [] -> []
      | hd::rest -> (_1_gen hd head_rels) @ (gen rest head_rels)

      and _1_gen stt head_rels = match stt with
        | Rule (Pred(rel, varlst), bodylst) ->
             [Rule (Pred("pp_" ^ rel, varlst), (_2_gen bodylst source_rels_schevo head_rels))]
        | _ -> []

      and _2_gen bodylst source_rels_schevo head_rels = match bodylst with
        | [] -> []
        | hd::rest -> (_3_gen hd source_rels_schevo head_rels)
                      @ (_2_gen rest source_rels_schevo head_rels)

      and _3_gen tm source_rels_schevo head_rels = match tm with
        | Rel(Pred(rel, varlst)) ->
            if (List.mem rel source_rels_schevo) && not (List.mem rel head_rels)
              then [Rel(Pred("pp_" ^ (get_base rel), varlst))]
            else if not (List.mem rel source_rels_schevo) && (List.mem rel head_rels)
              then [Rel(Pred("pp_" ^ rel, varlst))]
            else
              [tm]
        | Not(Pred(rel, varlst)) ->
            if (List.mem rel source_rels_schevo) && not (List.mem rel head_rels)
              then [Not(Pred("pp_" ^ (get_base rel), varlst))]
            else if not (List.mem rel source_rels_schevo) && (List.mem rel head_rels)
              then [Rel(Pred("pp_" ^ rel, varlst))]
            else
              [tm]
        | _ -> [tm]
    in

    let head_rels = get_rels_head ast_schevo in
    let new_get = gen (get_sttl ast_schevo) head_rels in

  new_get
  in

  (* T1 = get_t(Sb, Ad+, Ad-)
       = (get_t_sb(Sb) ∩ ¬Ad-) ∪ Ad+ *)
  let gen_get_t target_pred =

    let t_rel = get_rel_from_pred target_pred in
    let vars = get_varlst_from_pred target_pred in
    let ad_ins = get_dif_ins t_rel in
    let ad_del = get_dif_del t_rel in

    let result =
      [Rule(Pred(t_rel, vars), [Rel(Pred( ("zero_" ^ t_rel), vars)); Not(Pred(ad_del, vars))]);
       Rule(Pred(t_rel, vars), [Rel(Pred(ad_ins, vars))])
      ]
    in
  result
  in

  (* -------------------------------------------------
    Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+
     ∆Sb+ = F'+(Sb, ∆T1)
     ∆Sb- = F'-(Sb, ∆T1)
  --------------------------------------------------- *)
  let gen_putdelta_base ast_bwd source_rels_schevo target_rel =

    let rec gen sttl_bwd = match sttl_bwd with
    | [] -> []
    | hd::rest -> (_1_gen hd) @ (gen rest)

    and _1_gen stt = match stt with
      | Rule (Pred(rel, varlst), bodylst) ->
          let insdel_base_bodylst = insdel_base (source2base bodylst source_rels_schevo) [target_rel] in
          [Rule (Pred(rel, varlst), insdel_base_bodylst)]

      | Rule (Deltainsert(rel, varlst), bodylst) ->
          let base_rel =
            if List.mem rel source_rels_schevo
              then get_base rel
              else rel
          in

          (* replacing body with "base_"  *)
          let base_bodylst = insdel_base (source2base bodylst source_rels_schevo) [target_rel] in
          [Rule (Deltainsert(base_rel, varlst), base_bodylst)]

      | Rule (Deltadelete(rel, varlst), bodylst) ->
          let base_rel =
            if List.mem rel source_rels_schevo
              then get_base rel
              else rel
          in

          (* replacing body with "base_"  *)
          let base_aux_bodylst = insdel_base (source2base bodylst source_rels_schevo) [target_rel] in

        [Rule (Deltadelete(base_rel, varlst), base_aux_bodylst)]

      | _ -> []
    in

    let result = gen (get_sttl ast_bwd) in
  result
  in

 (* --------------------------------------------------------------------
      % diff
      % putdelta_ad1_ins
      Ad1+' = (Ad1+ ∩ ¬∆Ad1+-) ∪ ∆Ad1++
        ∆Ad1++ = T1 ∩ ¬T1'' ∩ ¬Ad1+
        ∆Ad1+- = ¬T1 ∩ Ad1+

      % putdelta_ad1_del
      Ad1-' = (Ad1- ∩ ¬∆Ad1--) ∪ ∆Ad1-+
        ∆Ad1-+ = ¬T1 ∩ T1'' ∩ ¬Ad1-
        ∆Ad1-- = (T1 ∩ Ad1-) ∪ (¬T1'' ∩ Ad1-)

        T'' = F1(Sb_nos')
        Sb_nos' = (Sb' ∩ A2+') ∪ A2-'
  ---------------------------------------------------------------------- *)
  let putdelta_ad target_rel_1 target_vars_1 =

    let ad1_ins = get_dif_ins target_rel_1 in
    let ad1_del = get_dif_del target_rel_1 in
    let target_1_pred = Pred (target_rel_1, target_vars_1) in
    let new_target_1_pred = Pred ("pp_" ^ target_rel_1, target_vars_1) in

    (* ∆Ad1++ = T1 ∩ ¬T1'' ∩ ¬Ad1+ *)
    (* ∆Ad1+- = ¬T1 ∩ Ad1+ *)
    let putdelta_ad1_ins =
      [ Rule(Deltainsert(ad1_ins, target_vars_1),
             [ Rel (target_1_pred);
               Not (new_target_1_pred);
               Not (Pred(ad1_ins, target_vars_1))
             ]
            );
        Rule(Deltadelete(ad1_ins, target_vars_1),
             [ Not (target_1_pred);
               Rel (Pred(ad1_ins, target_vars_1))
             ]
            )
     ]
    in

  (* ∆Ad1-+ = ¬T1 ∩ T1'' ∩ ¬Ad1- *)
  (* ∆Ad1-- = (T1 ∩ Ad1-) ∪ (¬T1'' ∩ Ad1-) *)
  let putdelta_ad1_del =
      [ Rule(Deltainsert(ad1_del, target_vars_1),
             [ Not (target_1_pred);
               Rel (new_target_1_pred);
               Not (Pred(ad1_del, target_vars_1))
             ]
            );
        Rule(Deltadelete(ad1_del, target_vars_1),
             [ Rel (target_1_pred);
               Rel (Pred(ad1_del, target_vars_1))
             ]
            );
        Rule(Deltadelete(ad1_del, target_vars_1),
             [ Not (new_target_1_pred);
               Rel (Pred(ad1_del, target_vars_1))
             ]
            )
     ]
    in

  putdelta_ad1_ins @ putdelta_ad1_del
  in

  (* --------------------------------------------------------
    ∆T1+ = T1' ∩ ¬T1_tmp
    ∆T1- = ¬T1' ∩ T1_tmp
       T1_tm = get_t1( (Sb, A2+, A2-), Ad1+, Ad1-)
             = (get_t1_sb (Sb, A2+, A2-) ∩ ¬Ad1-) ∪ Ad1+
  ------------------------------------------------------------- *)
  let generate_insdel_target t_rel t_var get_t =

    let rule_insdel_t = [
        Rule(Pred(("ins_"^t_rel), t_var),
             [Rel(Pred(t_rel, t_var)); Not(Pred(("tmp_" ^ t_rel), t_var))]);
        Rule(Pred(("del_"^t_rel), t_var),
             [Not(Pred(t_rel, t_var)); Rel(Pred(("tmp_" ^ t_rel), t_var))]);
        ]
    in

    let rule_tmp_get_t =
      let rec transform get_t t_rel = match get_t with
        | [] -> []
        | hd::rest -> (_1_transform hd t_rel) @ (transform rest t_rel)

        and _1_transform stt t_rel = match stt with
          | Rule(Pred(rel, vars), bodylst) ->
            if rel = t_rel
            then
              [Rule(Pred("tmp_" ^ rel, vars), bodylst)]
            else
              [stt]
          | _ -> [stt]
      in
      transform get_t t_rel
    in

  rule_insdel_t @ rule_tmp_get_t
  in

  (* === sttl =========================================================== *)
  let schema_target =
    let sources = unique_element @@ List.fold_left  List.append [] (List.map get_source init_ast_lst) in
    let target = schema2schema @@ (Prog (get_target_schemas ast_schema)) in
    (get_sttl target) @ sources
  in

  (* T1 = get_t( Sb, Ad+, Ad-)
       = (get_t_sb(Sb) ∩ ¬Ad-) ∪ Ad+ *)
  let get_t = gen_get_t target_pred in

  (* get_t1_sb(Sb) = F1(Sb) *)
  let get_t_sb = gen_get_t_sb (get_sttl ast_schevo) source_rels_schevo in

  (* putdelta ( (Sb, Ad+, Ad1-), T') *)
  let putdelta_base = gen_putdelta_base ast_bwd_ex_schevo source_rels_schevo target_rel in
    (* printf "putdelta_base: \n";  Expr.print_sttlst putdelta_base; printf "\n"; *)

  let putdelta_ad = putdelta_ad target_rel target_vars in

  (* new_T1 = F1(Sb_new) *)
  let new_get_t1_sb = new_gen_get_t1_sb ast_schevo source_preds_schevo source_rels_schevo in

  (* Sb_new *)
  let new_s_b = new_gen_s_b source_preds_schevo source_ins_rels_bwd source_del_rels_bwd in

  (* ∆T1+ = T1' ∩ ¬T1_tmp, ∆T1- = ¬T1' ∩ T1_tmp *)
  let insdel_target = generate_insdel_target target_rel target_vars get_t in

  (* constraints *)
  let ast_constraint_core_target = generate_const_core_target ast_constraint_core source_pred_lst in
  let stgy_constraints = (get_sttl ast_constraint_core_target)
                          @ (get_sttl ast_constraint_pk) in
  let aux_constraints =
    let ast_pk_aux_constraint = generate_pk_constraint_aux_2 pk_lst target_pred (Prog(get_t_sb)) in
    let ast_ad_aux_constraint = generate_ad_aux_constraint_zero target_pred in
    (get_sttl ast_pk_aux_constraint) @ (get_sttl ast_ad_aux_constraint)
  in

  (*-- main ----------------------------------------------------------------------------*)
  let ast = Prog (schema_target @
                  stgy_constraints @ aux_constraints @
                  get_t @ get_t_sb @
                  putdelta_base @
                  putdelta_ad @
                  new_get_t1_sb @ new_s_b @
                  insdel_target
                 )
  in
ast
;;

(* ======================================================================================= *)

(* --------------------------------------------------------------
  Derive BIRdS program for taregt rel

  % schemas
    view t1(X).            (* S: view *)
    source b_s1(X).        (* Sb: base relation *)
    source nos_i_t1_s1(X). (* A1+: aux for no-share *)
    source nos_d_t1_s1(X). (* A1-: aux for no-share *)
    source nos_i_t2_s1(X). (* A2+: aux for no-share *)
    source nos_d_t2_s1(X). (* A2-: aux for no-share *)
    source dif_i_t1(X).    (* Ad1+: aux for diff *)
    source dif_d_t1(X).    (* Ad1-: aux for diff *)
    source dif_i_t2(X).    (* Ad2+: aux for diff *)
    source dif_d_t2(X).    (* Ad2-: aux for diff *)

  % constraint
     Ad1+ ∩ Ad1- = ∅
     Ad1- ∩ ¬F1(Sb.nos) = ∅

  % get
    T1 = get_t1( (Sb, A2+, A2-), Ad1+, Ad1-)
       = (get_t1_sb (Sb, A2+, A2-) ∩ ¬Ad1-) ∪ Ad1+

    get_t1_sb (Sb, A2+, A2-) = F1(Sb.nos)
    Sb_nos = (Sb ∩ ¬A2+) ∪ A2-


  % putdelta
    (Sb', A1+', A1-', A2+'. A2-', Ad1+', Ad1-', Ad2+', Ad2-')
     = (Sb, A1+, A1-, A2+, A2-, Ad1+, Ad1-, Ad2+, Ad2-) ⨁
      putdelta ( (Sb, A1+, A1-, A2+, A2-, Ad1+, Ad1-, Ad2+, Ad2-), T1')

    % putdelta_base (for each Si)
    Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+
     ∆Sb+ = F1'+(Sb, ∆T1) ∩ ¬A2+
     ∆Sb- = F1'-(Sb, ∆T1) ∩ ¬A2+

    % putdelta_a1_ins (when (+)s1)
    A1+' = (A1+ ∩ ¬∆A1+-) ∪ ∆A1++
     ∆A1++ = ∆Sb+
     ∆A1+- = ∆Sb-

    % putdelta_a1_del (when (-)s1)
    A1-' = A1- ∪ ∆A1-+
     ∆A1-+ = ∆Sb- ∩ ¬A1- ∩ ¬A1+

    % putdelta_a2_ins
    A2+' = A2+ ∩ ¬∆A2+-
     ∆A2+- = F1'+(Sb, ∆T1)

    % putdelta_a2_del
    A2-' = A2- ∩ ¬∆A2--
     ∆A2-- = F1'-(A2-, ∆T1) ∪ (∆Sb+ ∩ A2-)

    % diff
    % putdelta_ad1_ins
    Ad1+' = (Ad1+ ∩ ¬∆Ad1+-) ∪ ∆Ad1++
      ∆Ad1++ = T1 ∩ ¬T1'' ∩ ¬Ad1+
      ∆Ad1+- = ¬T1 ∩ Ad1+

    % putdelta_ad1_del
    Ad1-' = (Ad1- ∩ ¬∆Ad1--) ∪ ∆Ad1-+
      ∆Ad1-+ = ¬T1 ∩ T1'' ∩ ¬Ad1-
      ∆Ad1-- = (T1 ∩ Ad1-) ∪ (¬T1'' ∩ Ad1-)

      T'' = F1(Sb_nos')
      Sb_nos' = (Sb' ∩ A2+') ∪ A2-'

    % ∆T1
      ∆T1+ = T1' ∩ ¬T1_tmp
      ∆T1- = ¬T1' ∩ T1_tmp
         T1_tm = get_t1( (Sb, A2+, A2-), Ad1+, Ad1-)
               = (get_t1_sb (Sb, A2+, A2-) ∩ ¬Ad1-) ∪ Ad1+
 *)
(* -------------------------------------------------------------------------------------- *)
(* Derive BIRdS program for case2 relaitons *)
let derivation_target_birds_2 ast_schema ast_constraint_core ast_constraint_pk ast_schevo ast_bwd target_pred_1 target_pred_2 pk_lst init_ast_lst_2 target_1_ins_nos_rels target_1_del_nos_rels target_2_ins_nos_rels target_2_del_nos_rels source_pred_lst log timeout =

    (* Jumpei-del *)
    print_endline "--- derivation_target_birds_2 ---";
    print_endline "ast_bwd:"; Expr.print_ast ast_bwd; printf "\n";

        printf "target_2_del_nos_rels => ["; let print_el s = printf "%s; " s in
        List.iter print_el target_2_del_nos_rels; printf "]\n";

  (* === parts ======================================================== *)
  let target_rel_1 = get_rel_from_pred target_pred_1 in
  let target_vars_1 = get_varlst_from_pred target_pred_1 in

  let target_rel_2 = get_rel_from_pred target_pred_2 in
  let target_vars_2 = get_varlst_from_pred target_pred_2 in

  let source_preds_schevo =
    let rels_body = unique_element @@ get_rels_body ast_schevo in

    let rec filter rels_body source_pred_lst = match source_pred_lst with
      | [] -> []
      | hd::rest -> (_1_filter rels_body hd) @ (filter rels_body rest)
      and _1_filter rels_body tm = match tm with
        | Pred(rel, varlst) -> if List.mem rel rels_body then [tm] else []
        | _ -> []
    in

    filter rels_body source_pred_lst
  in

  let source_rels_schevo = get_rels source_preds_schevo in
  let source_ins_rels_bwd = get_ins_rels_head ast_bwd in
  let source_del_rels_bwd = get_del_rels_head ast_bwd in

      (*  printf "source_preds_schevo => [";
          let print_el s = printf "%s; " s in
          List.iter print_el (List.map string_of_rterm source_preds_schevo);
          printf "]\n";
        *)

  (* ================================================================= *)
  (*    functions                                                      *)
  (* ================================================================= *)

  (* change rel name of source to new, others to nos_base *)
  let rec source2new bodylst source_rel source_rels_schevo rel_new = match bodylst with
    | [] -> []
    | hd::rest -> (_1_source2new hd source_rel source_rels_schevo rel_new)
                  @ (source2new rest source_rel source_rels_schevo rel_new)

    and _1_source2new tm source_rel source_rels_schevo rel_new = match tm with
      | Rel (Pred(rel, varlst)) ->
          if (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Rel (Pred(rel_new, varlst))]
          else if not (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Rel (Pred( ("nos_" ^ (get_base rel)), varlst))]
          else
            [tm]

      | Not (Pred(rel, varlst)) ->
          if (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Not (Pred(rel_new, varlst))]
          else if  not (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Not (Pred( ("nos_" ^ (get_base rel)), varlst))]
          else
            [tm]

      | Rel (Deltainsert(rel, varlst)) ->
          if (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Rel (Deltainsert(rel_new, varlst))]
          else if  not (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Not (Deltainsert( (get_base rel), varlst))]
          else
            [tm]

      | Not (Deltadelete(rel, varlst)) ->
          if (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Not (Deltadelete(rel_new, varlst))]
          else if  not (rel = source_rel) && (List.mem rel source_rels_schevo)
            then [Not (Deltadelete( (get_base rel), varlst))]
          else
            [tm]
      | _ -> [tm]
  in

(*
  (* replace +t(X) to ins_t(X) or -t(X) to del_t(X) *)
  let rec insdel_base body_sttl = match body_sttl with
    | [] -> []
    | hd::rest -> (_1_insdel_base hd) @ (insdel_base rest)
    and _1_insdel_base tm = match tm with
      | Rel(Deltainsert(rel, vars)) -> [Rel(Pred(("ins_" ^ rel), vars))]
      | Rel(Deltadelete(rel, vars)) -> [Rel(Pred(("del_" ^ rel), vars))]
      | _ -> [tm]
  in
*)

  (* Sb_nos = (Sb ∩ ¬A2+) ∪ A2- *)
  let rec gen_s_b_nos source_preds_schevo target_rel = match source_preds_schevo with
    | [] -> []
    | hd::rest -> (_1_gen hd target_rel) @ (gen_s_b_nos rest target_rel)

    and _1_gen tm target_rel = match tm with
      | Pred(rel, varlst) ->

        (* Jumpei-del *)
        printf "target_2_ins_nos_rels=> ["; let print_el s = printf "%s; " s in
        List.iter print_el target_2_ins_nos_rels; printf "]\n";

        printf "target_2_del_nos_rels => ["; let print_el s = printf "%s; " s in
        List.iter print_el target_2_del_nos_rels; printf "]\n\n";


        if (List.mem rel target_2_ins_nos_rels) && (List.mem rel target_2_del_nos_rels)
          then
            [ Rule(Pred("nos_" ^ (get_base rel), varlst),
                  [Rel(Pred( (get_base rel), varlst));
                   Not(Pred( (get_nos_ins target_rel rel), varlst))]);
             Rule(Pred("nos_" ^ (get_base rel), varlst),
                  [Rel(Pred( (get_nos_del target_rel rel), varlst))])
            ]
        else if not (List.mem rel target_2_ins_nos_rels) && (List.mem rel target_2_del_nos_rels)
          then
            [ Rule(Pred("nos_" ^ (get_base rel), varlst),
                  [Rel(Pred( (get_base rel), varlst))]);
             Rule(Pred("nos_" ^ (get_base rel), varlst),
                  [Rel(Pred( (get_nos_del target_rel rel), varlst))])
            ]
        else if (List.mem rel target_2_ins_nos_rels) && not (List.mem rel target_2_del_nos_rels)
          then
            [ Rule(Pred("nos_" ^ (get_base rel), varlst),
                  [Rel(Pred( (get_base rel), varlst));
                   Not(Pred( (get_nos_ins target_rel rel), varlst))])
            ]
        else if not (List.mem rel target_2_ins_nos_rels) && not (List.mem rel target_2_del_nos_rels)
            then [ Rule(Pred("nos_" ^ (get_base rel), varlst),
                        [Rel(Pred( (get_base rel), varlst))])
                 ]
        else
            []
    | _ -> []
  in

  (* Sb_nos' = (Sb' ∩ A2+') ∪ A2-' *)
  (* Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+ *)
  (* A2+' = A2+ ∩ ¬∆A2+- *)
  (* A2-' = A2- ∩ ¬∆A2-- *)
  let new_gen_s_b_nos source_preds_schevo source_ins_rels_bwd source_del_rels_bwd target_rel_2 target_2_ins_nos_rels target_2_del_nos_rels =

    (* Sb_nos' = (Sb' ∩ ¬A2+') ∪ A2-' *)
    let rec gen_s_b_nos source_preds_schevo target_rel_2 = match source_preds_schevo with
      | [] -> []
      | hd::rest -> (_1_gen_s_b_nos hd target_rel_2)
                    @ (gen_s_b_nos rest target_rel_2)

      and _1_gen_s_b_nos tm target_rel = match tm with
        | Pred(rel, varlst) ->

          let base = get_base rel in
          let nos_i = get_nos_ins target_rel_2 rel in
          let nos_d = get_nos_del target_rel_2 rel in

          if (List.mem rel target_2_ins_nos_rels) && (List.mem rel target_2_del_nos_rels)
            then
              [ Rule(Pred("pp_nos_" ^ base, varlst),
                    [Rel(Pred( ("pp_" ^ base), varlst));
                    Not(Pred( (nos_i), varlst))]);
                Rule(Pred("pp_nos_" ^ base, varlst),
                    [Rel(Pred( ("pp_" ^ nos_d), varlst))])
              ]
          else if not (List.mem rel target_2_ins_nos_rels) && (List.mem rel target_2_del_nos_rels)
            then
              [ Rule(Pred("pp_nos_" ^ base, varlst),
                    [Rel(Pred( ("pp_" ^ base), varlst))]);
                Rule(Pred("pp_nos_" ^ base, varlst),
                    [Rel(Pred( ("pp_" ^ nos_d), varlst))])
              ]
          else if (List.mem rel target_2_ins_nos_rels) && not (List.mem rel target_2_del_nos_rels)
            then
              [ Rule(Pred("pp_nos_" ^ base, varlst),
                    [Rel(Pred( ("pp_" ^ base), varlst));
                    Not(Pred( ("pp_" ^ nos_i), varlst))])
              ]
          else
              [ Rule(Pred("pp_nos_" ^ base, varlst),
                    [Rel(Pred( ("pp_" ^ base), varlst))])
              ]
      | _ -> []
    in

    (* Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+ *)
    let rec gen_base source_preds_schevo source_ins_rels_bwd source_del_rels_bwd = match source_preds_schevo with
      | [] -> []
      | hd::rest -> (_1_gen_base hd source_ins_rels_bwd source_del_rels_bwd)
                    @ (gen_base rest source_ins_rels_bwd source_del_rels_bwd)

      and _1_gen_base hd source_ins_rels_bwd source_del_rels_bwd = match hd with
        | Pred(rel, varlst) ->
            let base_rel = get_base rel in
            if (List.mem rel source_ins_rels_bwd) && (List.mem rel source_del_rels_bwd)
              then [ Rule (Pred(("pp_" ^ base_rel), varlst),
                           [Rel(Pred (base_rel, varlst)); Not(Deltadelete(base_rel, varlst))
                           ] );
                     Rule (Pred(("pp_" ^ base_rel), varlst),
                           [Rel(Deltainsert(base_rel, varlst))] )
                   ]
            else if (List.mem rel source_ins_rels_bwd) && not (List.mem rel source_del_rels_bwd)
              then [ Rule (Pred(("pp_" ^ base_rel), varlst),
                           [Rel(Pred (base_rel, varlst))] );
                     Rule (Pred(("pp_" ^ base_rel), varlst),
                           [Rel(Deltainsert(base_rel, varlst)) ] )
                   ]
            else if not (List.mem rel source_ins_rels_bwd) && (List.mem rel source_del_rels_bwd)
              then [  Rule (Pred(("pp_" ^ base_rel), varlst),
                           [Rel(Pred (base_rel, varlst)); Not(Deltadelete(base_rel, varlst))
                           ] )
                   ]
            else if not (List.mem rel source_ins_rels_bwd) && not (List.mem rel source_del_rels_bwd)
              then [ Rule (Pred(("pp_" ^ base_rel), varlst),
                          [Rel(Pred (base_rel, varlst))
                          ] )
                   ]
            else
              []

        | _ -> []
    in

    (* A2+' = A2+ ∩ ¬∆A2+- *)
    let rec gen_a2_ins source_preds_schevo target_rel_2 target_2_ins_nos_rels = match source_preds_schevo with
      | [] -> []
      | hd::rest -> (_1_gen_a2_ins hd target_rel_2 target_2_ins_nos_rels)
                    @ (gen_a2_ins rest target_rel_2 target_2_ins_nos_rels)

      and _1_gen_a2_ins pred target_rel_2 target_2_ins_nos_rels = match pred with
        | Pred (rel, varlst) ->
          let a2_ins_rel = get_nos_ins target_rel_2 rel in
          if List.mem rel target_1_ins_nos_rels
            then [Rule( Pred("pp_" ^ a2_ins_rel, varlst),
                        [ Rel(Pred(a2_ins_rel, varlst));
                          Not (Deltadelete(a2_ins_rel, varlst))
                        ])
                 ]
            else
              [Rule( Pred("pp_" ^ a2_ins_rel, varlst),
                          [ Rel(Pred(a2_ins_rel, varlst))
                          ])
              ]
        | _ -> []
    in

    (* A2-' = A2- ∩ ¬∆A2-- *)
    let rec gen_a2_del source_preds_schevo target_rel_2 target_2_del_nos_rels = match source_preds_schevo with
      | [] -> []
      | hd::rest -> (_1_gen_a2_del hd target_rel_2 target_2_del_nos_rels)
                    @ (gen_a2_del rest target_rel_2 target_2_del_nos_rels)

      and _1_gen_a2_del pred target_rel_2 target_2_del_nos_rels = match pred with
        | Pred (rel, varlst) ->
          let a2_del_rel = get_nos_del target_rel_2 rel in
          if (List.mem rel target_1_del_nos_rels) || (List.mem rel target_1_ins_nos_rels)
            then [Rule( Pred("pp_" ^ a2_del_rel, varlst),
                        [ Rel(Pred(a2_del_rel, varlst));
                          Not (Deltadelete(a2_del_rel, varlst))
                        ])
                 ]
            else
              [Rule( Pred("pp_" ^ a2_del_rel, varlst),
                          [ Rel(Pred(a2_del_rel, varlst))
                          ])
              ]
        | _ -> []
    in

    let new_s_b_nos = gen_s_b_nos source_preds_schevo target_rel_2 in
    let new_base = gen_base source_preds_schevo source_ins_rels_bwd source_del_rels_bwd in
    let new_a2_ins = gen_a2_ins source_preds_schevo target_rel_2 target_2_ins_nos_rels in
    let new_a2_del = gen_a2_del source_preds_schevo target_rel_2 target_2_del_nos_rels in

    let result = new_s_b_nos @ new_base @ new_a2_ins @ new_a2_del in
  result
  in


  (* change s to nos_base_s *)
  let rec gen_get_t1_sb sttl_schevo source_rels_schevo = match sttl_schevo with
    | [] -> []
    | hd::rest -> (_1_gen_get hd source_rels_schevo) @ (gen_get_t1_sb rest source_rels_schevo)

    and _1_gen_get stt source_rels_schevo = match stt with
      | Rule (Pred(rel, varlst), bodylst)
          -> [Rule (Pred("nos_" ^ rel, varlst), (_2_gen_get bodylst source_rels_schevo))]
      | _ -> []

    and _2_gen_get bodylst source_rels_schevo = match bodylst with
      | [] -> []
      | hd::rest -> (_3_gen_get hd source_rels_schevo)
                    @ (_2_gen_get rest source_rels_schevo)

    and _3_gen_get tm source_rels_schevo = match tm with
      | Rel(Pred(rel, varlst)) ->
           if List.mem rel source_rels_schevo
            then [Rel(Pred("nos_" ^ (get_base rel), varlst))]
            else [Rel(Pred("nos_" ^ rel, varlst))]
      | Not(Pred(rel, varlst)) ->
          if List.mem rel source_rels_schevo
            then [Not(Pred("nos_" ^ (get_base rel), varlst))]
            else [Not(Pred("nos_" ^ rel, varlst))]
      | _ -> [tm]
  in

  (* new_get *)
  let new_gen_get_t1_sb_nos ast_schevo source_preds_schevo source_rels_schevo =

    (* T'' = F1(Sb_nos') *)
    let rec gen sttl_schevo head_rels = match sttl_schevo with
      | [] -> []
      | hd::rest -> (_1_gen hd head_rels) @ (gen rest head_rels)

      and _1_gen stt head_rels = match stt with
        | Rule (Pred(rel, varlst), bodylst) ->
             [Rule (Pred("pp_" ^ rel, varlst), (_2_gen bodylst source_rels_schevo head_rels))]
        | _ -> []

    and _2_gen bodylst source_rels_schevo head_rels = match bodylst with
      | [] -> []
      | hd::rest -> (_3_gen hd source_rels_schevo head_rels)
                    @ (_2_gen rest source_rels_schevo head_rels)

    and _3_gen tm source_rels_schevo head_rels = match tm with
      | Rel(Pred(rel, varlst)) ->
          if (List.mem rel source_rels_schevo) && not (List.mem rel head_rels)
            then [Rel(Pred("pp_nos_" ^ (get_base rel), varlst))]
          else if not (List.mem rel source_rels_schevo) && (List.mem rel head_rels)
            then [Rel(Pred("pp_" ^ rel, varlst))]
          else
            [tm]
      | Not(Pred(rel, varlst)) ->
          if (List.mem rel source_rels_schevo) && not (List.mem rel head_rels)
            then [Not(Pred("pp_nos_" ^ (get_base rel), varlst))]
          else if not (List.mem rel source_rels_schevo) && (List.mem rel head_rels)
            then [Rel(Pred("pp_" ^ rel, varlst))]
          else
            [tm]
      | _ -> [tm]
    in

    let head_rels = get_rels_head ast_schevo in
    let new_get = gen (get_sttl ast_schevo) head_rels in

  new_get
  in

  (* T1 = get_t1( (Sb, A2+, A2-), Ad1+, Ad1-)
       = (get_t1_sb (Sb, A2+, A2-) ∩ ¬Ad1-) ∪ Ad1+ *)
  let gen_get_t1 target_pred =

    let t_rel = get_rel_from_pred target_pred in
    let vars = get_varlst_from_pred target_pred in
    let ad_ins = get_dif_ins t_rel in
    let ad_del = get_dif_del t_rel in

    let result =
      [Rule(Pred(t_rel, vars), [Rel(Pred( ("nos_" ^ t_rel), vars)); Not(Pred(ad_del, vars))]);
       Rule(Pred(t_rel, vars), [Rel(Pred(ad_ins, vars))])
      ]
    in
  result
  in

  (* -------------------------------------------------
    Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+
     ∆Sb+ = F1'+(Sb, ∆T1) ∩ ¬A2+
     ∆Sb- = F1'-(Sb, ∆T1) ∩ ¬A2+
  --------------------------------------------------- *)
  let gen_putdelta_base ast_bwd source_rels_schevo target_rel_1 target_rel_2 target_2_ins_nos_rels =

    let target_rel_lst = [target_rel_1; target_rel_2] in

    let rec gen sttl_bwd = match sttl_bwd with
    | [] -> []
    | hd::rest -> (_1_gen hd) @ (gen rest)

    and _1_gen stt = match stt with
      | Rule (Pred(rel, varlst), bodylst) ->
          let insdel_base_bodylst = insdel_base (source2base bodylst source_rels_schevo) target_rel_lst in
          [Rule (Pred(rel, varlst), insdel_base_bodylst)]

      | Rule (Deltainsert(rel, varlst), bodylst) ->
          let base_rel =
            if List.mem rel source_rels_schevo
              then get_base rel
              else rel
          in
          let pred_a2_ins = Pred ( (get_nos_ins target_rel_2 rel), varlst) in

          (* replacing body with "base_" and add A2+ *)
          let base_aux_bodylst =
            if (List.mem rel source_rels_schevo) && (List.mem rel target_2_ins_nos_rels)
              then (insdel_base (source2base bodylst source_rels_schevo) target_rel_lst) @ [Not (pred_a2_ins)]
            else if (List.mem rel source_rels_schevo) && not (List.mem rel target_2_ins_nos_rels)
              then insdel_base (source2base bodylst source_rels_schevo) target_rel_lst
            else
                   insdel_base (source2base bodylst source_rels_schevo) target_rel_lst
          in

          [Rule (Deltainsert(base_rel, varlst), base_aux_bodylst)]

      | Rule (Deltadelete(rel, varlst), bodylst) ->
          let base_rel =
            if List.mem rel source_rels_schevo
              then get_base rel
              else rel
          in
          let pred_a2_ins = Pred ( (get_nos_ins target_rel_2 rel), varlst) in

          (* replacing body with "base_" and add A2+ *)
          let base_aux_bodylst =
            if (List.mem rel source_rels_schevo) && (List.mem rel target_2_ins_nos_rels)
              then (insdel_base (source2base bodylst source_rels_schevo) target_rel_lst) @ [Not (pred_a2_ins)]
            else if (List.mem rel source_rels_schevo) && not (List.mem rel target_2_ins_nos_rels)
              then insdel_base (source2base bodylst source_rels_schevo) target_rel_lst
            else
                   insdel_base (source2base bodylst source_rels_schevo) target_rel_lst
        in

        [Rule (Deltadelete(base_rel, varlst), base_aux_bodylst)]

      | _ -> []
    in

    let result = gen (get_sttl ast_bwd) in
  result
  in

  (* ------------------------------------------------------------------
  % putdelta_a1_ins (when (+)s1)
  A1+' = (A1+ ∩ ¬∆A1+-) ∪ ∆A1++
    ∆A1++ = ∆Sb+
    ∆A1+- = ∆Sb-

  % putdelta_a1_del (when (-)s1)
    A1-' = A1- ∪ ∆A1-+
    ∆A1-+ = ∆Sb- ∩ ¬A1- ∩ ¬A1+

  % putdelta_a2_ins
    A2+' = A2+ ∩ ¬∆A2+-
    ∆A2+- = F1'+(Sb, ∆T1)

  % putdelta_a2_del
    A2-' = A2- ∩ ¬∆A2--
    ∆A2-- = F1'-(A2-, ∆T1) ∪ (∆Sb+ ∩ A2-)
  ------------------------------------------------------------------- *)
  let gen_putdelta_aux_nos source_preds_schevo source_rels_schevo target_rel_1 target_rel_2 =

    let target_rel_lst = [target_rel_1; target_rel_2] in

    let rec gen source_preds_schevo = match source_preds_schevo with
      | [] -> []
      | hd::rest -> (_1_gen hd) @ (gen rest)

      and _1_gen pred = match pred with
        | Pred(rel, varlst) ->

            (* relname of aux relations *)
            let base = get_base rel in
            let a1_ins = get_nos_ins target_rel_1 rel in
            let a1_del = get_nos_del target_rel_1 rel in
            let a2_ins = get_nos_ins target_rel_2 rel in
            let a2_del = get_nos_del target_rel_2 rel in

            (* Rules of F'+ and F'-*)
            let rules_f_prime_ins = get_sttl @@ get_one_query ast_bwd (Deltainsert(rel, varlst)) in
            let rules_f_prime_del = get_sttl @@ get_one_query ast_bwd (Deltadelete(rel, varlst)) in

              (* Jumpei-del *)
              print_endline "--- gen_putdelta_aux_nos ---";
              print_endline "ast_bwd:"; Expr.print_ast ast_bwd; printf "\n";
              print_endline "rules_f_prime_del:"; Expr.print_sttlst rules_f_prime_del; printf "\n";

            (* A1+' = (A1+ ∩ ¬∆A1+-) ∪ ∆A1++
                ∆A1++ = ∆Sb+
                ∆A1+- = ∆Sb-
            *)
            let putdelta_a1_ins =
              if    (List.mem rel target_1_ins_nos_rels)
                 && (List.mem rel target_1_del_nos_rels)
                then
                  [ Rule (Deltainsert(a1_ins, varlst),
                          [Rel(Deltainsert(base, varlst))]);
                    Rule (Deltadelete(a1_ins, varlst),
                          [Rel(Deltadelete(base, varlst))])
                  ]
              else if (List.mem rel target_1_ins_nos_rels)
                      && not (List.mem rel target_1_del_nos_rels)
                then
                  [ Rule (Deltainsert(a1_ins, varlst),
                          [Rel(Deltainsert(base, varlst))])
                  ]
              else if not (List.mem rel target_1_ins_nos_rels)
                      && (List.mem rel target_1_del_nos_rels)
                then
                  [ Rule (Deltadelete(a1_ins, varlst),
                          [Rel(Deltadelete(base, varlst))])
                  ]
              else if not (List.mem rel target_1_ins_nos_rels)
                      && not (List.mem rel target_1_del_nos_rels)
                then
                  []
              else
                  []
            in

            (* A1-' = A1- ∪ ∆A1-+
               ∆A1-+ = ∆Sb- ∩ ¬A1- ∩ ¬A1+
            *)
            let putdelta_a1_del =
              if List.mem rel target_1_del_nos_rels
                then
                  [ Rule( Deltainsert(a1_del, varlst),
                          [Rel(Deltadelete(base, varlst)); Not(Pred(a1_del, varlst)); Not(Pred(a1_ins, varlst)) ]
                        ) ]
                else
                  []
            in

            (* A2+' = A2+ ∩ ¬∆A2+-
               ∆A2+- = F1'+(Sb, ∆T1)
            *)
            let putdelta_a2_ins =
              if List.mem rel target_1_ins_nos_rels
                then begin
                  let rec transform rules_f_prime_ins = match rules_f_prime_ins with
                    | [] -> []
                    | hd::rest -> (_1_transform hd) @ (transform rest)

                    and _1_transform stt = match stt with
                      | Rule (Pred(fp_rel, fp_varlst), fp_bodylst) ->
                          if List.mem fp_rel source_rels_schevo
                            then [Rule (Pred((get_base fp_rel), fp_varlst),
                                        (insdel_base (source2base fp_bodylst source_rels_schevo) target_rel_lst ))]
                            else [Rule (Pred(fp_rel, fp_varlst),
                                       (insdel_base (source2base fp_bodylst source_rels_schevo) target_rel_lst  ))]
                      | Rule (Deltainsert(fp_rel, fp_varlst), fp_bodylst) ->
                          if fp_rel = rel
                            then [Rule (Deltadelete(a2_ins, varlst),
                                        (insdel_base (source2base fp_bodylst source_rels_schevo) target_rel_lst  ))]
                            else []
                      | _ -> []
                  in
                  transform rules_f_prime_ins
                end
                else
                  []
            in

            (* A2-' = A2- ∩ ¬∆A2--
               ∆A2-- = F1'-(A2-, ∆T1) ∪ (∆Sb+ ∩ A2-)
            *)
            let putdelta_a2_del =
                  (* Jumpei-del *)
                  printf "rel = %s\n" rel;
                  printf "target_1_del_nos_rels => ["; let print_el s = printf "%s; " s in
                  List.iter print_el target_2_del_nos_rels; printf "]\n";

              if List.mem rel target_1_del_nos_rels
                then begin
                  print_endline "List.mem rel target_1_del_nos_rels = true"; (* Jumpei-del *)

                  let rec transform rules_f_prime_del = match rules_f_prime_del with
                    | [] -> []
                    | hd::rest -> (_1_transform hd) @ (transform rest)

                    and _1_transform stt = match stt with
                      | Rule (Pred(fp_rel, fp_varlst), fp_bodylst) ->
                          if List.mem fp_rel source_rels_schevo
                            then [Rule (Pred((get_base fp_rel), fp_varlst),
                                       (insdel_base (source2new fp_bodylst rel source_rels_schevo a2_del) target_rel_lst  ))]
                            else [Rule (Pred(fp_rel, fp_varlst),
                                       (insdel_base (source2new fp_bodylst rel source_rels_schevo a2_del) target_rel_lst  ))]
                      | Rule (Deltadelete(fp_rel, fp_varlst), fp_bodylst) ->
                          if fp_rel = rel
                            then [Rule (Deltadelete(a2_del, varlst),
                                        (insdel_base (source2new fp_bodylst rel source_rels_schevo a2_del) target_rel_lst   ))]
                            else []
                      | _ -> []
                  in

                  let rule_a2_del =
                    if List.mem rel target_1_ins_nos_rels
                      then
                        [Rule (Deltadelete(a2_del, varlst),
                               [Rel(Deltainsert(base, varlst));
                                Rel(Pred(a2_del, varlst))]
                              )]
                      else
                        []
                  in

                  (transform rules_f_prime_del) @ rule_a2_del
                end
                else begin
                  print_endline "List.mem rel target_1_del_nos_rels = false"; (* Jumpei-del *)
                  []
                end
            in

            putdelta_a1_ins @ putdelta_a1_del @ putdelta_a2_ins @ putdelta_a2_del

        | _ -> []
    in

    let result = gen source_preds_schevo in
  result
  in

 (* --------------------------------------------------------------------
      % diff
      % putdelta_ad1_ins
      Ad1+' = (Ad1+ ∩ ¬∆Ad1+-) ∪ ∆Ad1++
        ∆Ad1++ = T1 ∩ ¬T1'' ∩ ¬Ad1+
        ∆Ad1+- = ¬T1 ∩ Ad1+

      % putdelta_ad1_del
      Ad1-' = (Ad1- ∩ ¬∆Ad1--) ∪ ∆Ad1-+
        ∆Ad1-+ = ¬T1 ∩ T1'' ∩ ¬Ad1-
        ∆Ad1-- = (T1 ∩ Ad1-) ∪ (¬T1'' ∩ Ad1-)

        T'' = F1(Sb_nos')
        Sb_nos' = (Sb' ∩ A2+') ∪ A2-'
  ---------------------------------------------------------------------- *)
  let putdelta_ad target_rel_1 target_vars_1 =

    let ad1_ins = get_dif_ins target_rel_1 in
    let ad1_del = get_dif_del target_rel_1 in
    let target_1_pred = Pred (target_rel_1, target_vars_1) in
    let new_target_1_pred = Pred ("pp_" ^ target_rel_1, target_vars_1) in

    (* ∆Ad1++ = T1 ∩ ¬T1'' ∩ ¬Ad1+ *)
    (* ∆Ad1+- = ¬T1 ∩ Ad1+ *)
    let putdelta_ad1_ins =
      [ Rule(Deltainsert(ad1_ins, target_vars_1),
             [ Rel (target_1_pred);
               Not (new_target_1_pred);
               Not (Pred(ad1_ins, target_vars_1))
             ]
            );
        Rule(Deltadelete(ad1_ins, target_vars_1),
             [ Not (target_1_pred);
               Rel (Pred(ad1_ins, target_vars_1))
             ]
            )
     ]
    in

  (* ∆Ad1-+ = ¬T1 ∩ T1'' ∩ ¬Ad1- *)
  (* ∆Ad1-- = (T1 ∩ Ad1-) ∪ (¬T1'' ∩ Ad1-) *)
  let putdelta_ad1_del =
      [ Rule(Deltainsert(ad1_del, target_vars_1),
             [ Not (target_1_pred);
               Rel (new_target_1_pred);
               Not (Pred(ad1_del, target_vars_1))
             ]
            );
        Rule(Deltadelete(ad1_del, target_vars_1),
             [ Rel (target_1_pred);
               Rel (Pred(ad1_del, target_vars_1))
             ]
            );
        Rule(Deltadelete(ad1_del, target_vars_1),
             [ Not (new_target_1_pred);
               Rel (Pred(ad1_del, target_vars_1))
             ]
            )
     ]
    in

  putdelta_ad1_ins @ putdelta_ad1_del
  in

  (* --------------------------------------------------------
    ∆T1+ = T1' ∩ ¬T1_tmp
    ∆T1- = ¬T1' ∩ T1_tmp
       T1_tm = get_t1( (Sb, A2+, A2-), Ad1+, Ad1-)
             = (get_t1_sb (Sb, A2+, A2-) ∩ ¬Ad1-) ∪ Ad1+
  ------------------------------------------------------------- *)
  let generate_insdel_target t_rel t_var get_t =

    let rule_insdel_t = [
        Rule(Pred(("ins_"^t_rel), t_var),
             [Rel(Pred(t_rel, t_var)); Not(Pred(("tmp_" ^ t_rel), t_var))]);
        Rule(Pred(("del_"^t_rel), t_var),
             [Not(Pred(t_rel, t_var)); Rel(Pred(("tmp_" ^ t_rel), t_var))]);
        ]
    in

    let rule_tmp_get_t =
      let rec transform get_t t_rel = match get_t with
        | [] -> []
        | hd::rest -> (_1_transform hd t_rel) @ (transform rest t_rel)

        and _1_transform stt t_rel = match stt with
          | Rule(Pred(rel, vars), bodylst) ->
            if rel = t_rel
            then
              [Rule(Pred("tmp_" ^ rel, vars), bodylst)]
            else
              [stt]
          | _ -> [stt]
      in
      transform get_t t_rel
    in

  rule_insdel_t @ rule_tmp_get_t
  in

  (* === sttl =========================================================== *)
  let schema_target =
    let sources = unique_element @@ List.fold_left  List.append [] (List.map get_source init_ast_lst_2) in
    let target = schema2schema @@ (Prog (get_target_schemas ast_schema)) in
    (get_sttl target) @ sources
  in

  (* T1 = get_t1( (Sb, A2+, A2-), Ad1+, Ad1-)
       = (get_t1_sb (Sb, A2+, A2-) ∩ ¬Ad1-) ∪ Ad1+ *)
  let get_t1 = gen_get_t1 target_pred_1 in

  (* get_t1_sb (Sb, A2+, A2-) = F1(Sb.nos) *)
  let get_t1_sb = gen_get_t1_sb (get_sttl ast_schevo) source_rels_schevo in

  (* Sb_nos = (Sb ∩ ¬A2+) ∪ A2- *)
  let s_b_nos = gen_s_b_nos source_preds_schevo target_rel_2 in

  (* putdelta ( (Sb, A1+, A1-, A2+, A2-, Ad1+, Ad1-, Ad2+, Ad2-), T1') *)
  let putdelta_base = gen_putdelta_base ast_bwd source_rels_schevo target_rel_1 target_rel_2 target_2_ins_nos_rels in

  let putdelta_aux_nos = gen_putdelta_aux_nos source_preds_schevo source_rels_schevo target_rel_1 target_rel_2 in
  let putdelta_ad = putdelta_ad target_rel_1 target_vars_1 in

  (* new_T1 = F1(Sb_nos_new) *)
  let new_get_t1_sb = new_gen_get_t1_sb_nos ast_schevo source_preds_schevo source_rels_schevo in

  (* Sb_nos_new = (Sb_new ∩ A2+_new) ∪ A2-_new *)
  let new_s_b_nos = new_gen_s_b_nos source_preds_schevo source_ins_rels_bwd source_del_rels_bwd target_rel_2 target_2_ins_nos_rels target_2_del_nos_rels in

  (* ∆T1+ = T1' ∩ ¬T1_tmp, ∆T1- = ¬T1' ∩ T1_tmp *)
  let insdel_target = generate_insdel_target target_rel_1 target_vars_1 get_t1 in

  (* constraints *)
  let stgy_constraints = (get_sttl ast_constraint_core) @ (get_sttl ast_constraint_pk) in

  let aux_constraints =
    let ast_pk_aux_constraint = generate_pk_constraint_aux_2 pk_lst target_pred_1 (Prog(get_t1_sb)) in
    let ast_ad_aux_constraint = generate_ad_aux_constraint_nos target_pred_1 in
    (get_sttl ast_pk_aux_constraint) @ (get_sttl ast_ad_aux_constraint)
  in

    (* Jumpei-del *)
    printf "putdelta_base: \n";  Expr.print_sttlst putdelta_base; printf "\n";
    printf "putdelta_aux_nos: \n";  Expr.print_sttlst putdelta_aux_nos; printf "\n";
    printf "putdelta_ad: \n";  Expr.print_sttlst putdelta_ad; printf "\n";




  (*-- main ----------------------------------------------------------------------------*)
  let ast = Prog (schema_target @
                  stgy_constraints @ aux_constraints @
                  get_t1 @ get_t1_sb @ s_b_nos @
                  putdelta_base @
                  putdelta_aux_nos @
                  putdelta_ad @
                  new_get_t1_sb @ new_s_b_nos @
                  insdel_target
                 )
  in
ast
;;
