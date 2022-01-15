(* @author: Jumpei Tanaka *)

  (* **************************************************************** *)
  (* Step 4: Target schema                                            *)
  (* **************************************************************** *)

open Expr;;
open Utils;;
open Tools;;
open View_common;;
open Printf;;


(* --------------------------------------------------------------
  Derive BIRdS program for taregt rel

  % schemas
    view t(X).            (* S: view *)
    source b_s(X).        (* Sb: base relation *)
    source dif_i_t(X).    (* Ad+: aux for diff *)
    source dif_d_t(X).    (* Ad-: aux for diff *)

  % constraint
     Ad1+ ∩ Ad1- = ∅

  % get
    T1 = get_t(Sb, Ad+, Ad-)
       = (get_t_sb(Sb) ∩ ¬Ad-) ∪ Ad+
          get_t_sb(Sb) = F(Sb)

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

  (* ================================================================= *)
  (*    functions                                                      *)
  (* ================================================================= *)
  (* change rel name of source to base *)
(*
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
  in
*)

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

  (* Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+ *)
  let new_gen_s_b source_preds_schevo source_ins_rels_bwd source_del_rels_bwd target_rel_2 =

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
          let insdel_base_bodylst = insdel_base @@ source2base bodylst source_rels_schevo in
          [Rule (Pred(rel, varlst), insdel_base_bodylst)]

      | Rule (Deltainsert(rel, varlst), bodylst) ->
          let base_rel =
            if List.mem rel source_rels_schevo
              then get_base rel
              else rel
          in

          (* replacing body with "base_"  *)
          let base_bodylst = insdel_base @@ source2base bodylst source_rels_schevo in

          [Rule (Deltainsert(base_rel, varlst), base_bodylst)]

      | Rule (Deltadelete(rel, varlst), bodylst) ->
          let base_rel =
            if List.mem rel source_rels_schevo
              then get_base rel
              else rel
          in
          let pred_a2_ins = Pred ( (get_nos_ins target_rel_2 rel), varlst) in

          (* replacing body with "base_"  *)
          let base_aux_bodylst = insdel_base @@ source2base bodylst source_rels_schevo in

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
    let sources = unique_element @@ List.fold_left  List.append [] (List.map get_source init_ast_lst_2) in
    let target = schema2schema @@ (Prog (get_target_schemas ast_schema)) in
    (get_sttl target) @ sources
  in

  (* T1 = get_t( Sb, Ad+, Ad-)
       = (get_t_sb(Sb) ∩ ¬Ad-) ∪ Ad+ *)
  let get_t = gen_get_t target_pred in

  (* get_t1_sb(Sb) = F1(Sb) *)
  let get_t_sb = gen_get_t_sb (get_sttl ast_schevo) source_rels_schevo in

  (* putdelta ( (Sb, Ad+, Ad1-), T') *)
  let putdelta_base = gen_putdelta_base ast_bwd source_rels_schevo target_rel_1 in
    (* printf "putdelta_base: \n";  Expr.print_sttlst putdelta_base; printf "\n"; *)

  let putdelta_ad = putdelta_ad target_rel_1 target_vars_1 in

  (* new_T1 = F1(Sb_new) *)
  let new_get_t1_sb = new_gen_get_t1_sb ast_schevo source_preds_schevo source_rels_schevo in

  (* Sb_new *)
  let new_s_b = new_gen_s_b source_preds_schevo source_ins_rels_bwd source_del_rels_bwd in

  (* ∆T1+ = T1' ∩ ¬T1_tmp, ∆T1- = ¬T1' ∩ T1_tmp *)
  let insdel_target = generate_insdel_target target_rel_1 target_vars_1 get_t1 in

  (* constraints *)
  let stgy_constraints = (get_sttl ast_constraint_core) @ (get_sttl ast_constraint_pk) in

  let aux_constraints =
    let ast_pk_aux_constraint = generate_pk_constraint_aux_2 pk_lst target_pred_1 (Prog(get_t1_sb)) in
    let ast_ad_aux_constraint = generate_ad_aux_constraint target_pred_1 in
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
