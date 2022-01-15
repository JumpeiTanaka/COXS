(* @author: Jumpei Tanaka *)

  (* ********************************************************** *)
  (* Step 3: Initial relations: derivation of views and schemas *)
  (* ********************************************************** *)

open Expr;;
open Utils;;
open Tools;;
open View_common;;
open Printf;;

(*
(*********************************************
  In: AST of schema, pred_list
  Out: AST of BIRDS program for schema
*********************************************)
let generate_schema ast_schemas pred =

  let rec _0_generate_schema ast_schamas pred = match ast_schemas with
    | Prog sttl -> _1_generate_schema sttl pred
    and _1_generate_schema sttl pred = match sttl with
      | [] -> []
      | hd::rest -> (_2_generate_schema hd pred) @ (_1_generate_schema rest pred)
    and _2_generate_schema hd pred = match hd with
        | Target_schema (_, rel, varlst) ->
            let rel_pred = get_rterm_predname pred in
            if rel = rel_pred
            then
              [View (rel, varlst); Source ("base_" ^ rel, varlst)]
            else
              []
        | Source_schema  (_, rel, varlst) ->
            let rel_pred = get_rterm_predname pred in
            if rel = rel_pred
            then
              [View (rel, varlst); Source ("base_" ^ rel, varlst)]
            else
              []
        | _ -> invalid_arg "function generate_schema called with other than Target_schema or Source_schema."
  in

  let result = _0_generate_schema ast_schemas pred in
result
;;
*)

(*********************************************
  In: AST of schema, pred_list, target_rel_1
  Out: AST of BIRDS program for schema
*********************************************)
let generate_schema_1 ast_schemas pred target_rel_1 target_vartyes_1 =

  let rec gen sttl pred target_rel_1 target_vartyes_1 = match sttl with
    | [] -> []
    | hd::rest -> (_1_gen hd pred target_rel_1 target_vartyes_1)
                  @ (gen rest pred target_rel_1 target_vartyes_1)

  and _1_gen stt pred target_rel_1 target_vartyes_1 = match stt with
    | Source_schema  (_, rel, varlst) ->
        let rel_pred = get_rterm_predname pred in
            if rel = rel_pred
            then
              [View (rel, varlst);                               (* S: view *)
               Source ("base_" ^ rel, varlst);                    (* Sb: base relation *)
               Source ( (get_dif_ins target_rel_1), target_vartyes_1);     (* Ad1+: aux for diff *)
               Source ( (get_dif_del target_rel_1), target_vartyes_1);     (* Ad1-: aux for diff *)
              ]
            else
              [Source ("base_" ^ rel, varlst)] (* Sb: base relation *)
    | _ -> []
  in

  let result = gen (get_sttl ast_schemas) pred target_rel_1 target_vartyes_1 in
result
;;

(*********************************************
  In: AST of schema, pred_list, target_rel_1, target_rel_2
  Out: AST of BIRDS program for schema
*********************************************)
let generate_schema_2 ast_schemas pred target_rel_1 target_vartypes_1 target_rel_2 target_vartypes_2 =

  let rec gen sttl pred target_rel_1 target_rel_2 = match sttl with
    | [] -> []
    | hd::rest -> (_1_gen hd pred target_rel_1 target_rel_2)
                  @ (gen rest pred target_rel_1 target_rel_2)

  and _1_gen stt pred target_rel_1 target_rel_2 = match stt with
    | Source_schema  (_, rel, varlst) ->
        let rel_pred = get_rterm_predname pred in
            if rel = rel_pred
            then
              [View (rel, varlst);                               (* S: view *)
               Source ("base_" ^ rel, varlst);                    (* Sb: base relation *)
               Source ( (get_nos_ins target_rel_1 rel), varlst); (* A1+: aux for no-share *)
               Source ( (get_nos_del target_rel_1 rel), varlst); (* A1-: aux for no-share *)
               Source ( (get_nos_ins target_rel_2 rel), varlst); (* A2+: aux for no-share *)
               Source ( (get_nos_del target_rel_2 rel), varlst); (* A2-: aux for no-share *)
               Source ( (get_dif_ins target_rel_1), target_vartypes_1);     (* Ad1+: aux for diff *)
               Source ( (get_dif_del target_rel_1), target_vartypes_1);     (* Ad1-: aux for diff *)
               Source ( (get_dif_ins target_rel_2), target_vartypes_2);     (* Ad2+: aux for diff *)
               Source ( (get_dif_del target_rel_2), target_vartypes_2)      (* Ad2-: aux for diff *)
              ]
            else
              [Source ("base_" ^ rel, varlst)]  (* Sb: base relation *)
    | _ -> []
  in

  let result = gen (get_sttl ast_schemas) pred target_rel_1 target_rel_2 in
result
;;

(*
(* **************************************************************
  Generate get_init
  (exampe)
  Input: [View(s1, [(X, Sint)]); Source(base_s1, [(X, Sint]) ]
  Output: s1(X) :- base_s1(X).
************************************************************** *)
let generate_get_init schema_init =

  let retrieve_view schema_init =
      let schema_view_lst = List.filter (fun x -> match x with View _ -> true | Source _ -> false | _ -> false) schema_init in
      let schema_view = List.hd schema_view_lst in
      let result = get_schema_rterm schema_view in
  result
  in

  let retrieve_source schema_init =
      let schema_source_lst = List.filter (fun x -> match x with View _ -> false | Source _ -> true | _ -> false) schema_init in
      let schema_source = List.hd schema_source_lst in
      let result = get_schema_rterm schema_source in
  result
  in

  let view_init = retrieve_view schema_init in
  let source_init = retrieve_source schema_init in
  let get_init = [Rule (view_init, [Rel(source_init)])] in

get_init
;;
*)


(* **************************************************************
  Generate get_init
  (exampe)
  Input: [View(s1, [(X, Sint)]); Source(base_s1, [(X, Sint]) ]
  Output: s1(X) :- base_s1(X).
************************************************************** *)
let generate_get_init schema_init =

  let retrieve_view schema_init =
      let schema_view_lst = List.filter (fun x -> match x with View _ -> true | Source _ -> false | _ -> false) schema_init in
      let schema_view = List.hd schema_view_lst in
      let result = get_schema_rterm schema_view in
  result
  in

  let retrieve_source view_init = match view_init with
      | Pred(rel, varlst) -> Rel( Pred("base_" ^ rel, varlst))
      | _ -> invalid_arg "function generate_get_init_2"
  in

  let view_init = retrieve_view schema_init in
  let source_init = retrieve_source view_init in
  let get_init = [Rule (view_init, [source_init])] in

get_init
;;

(*
(* **************************************************************
  Generate putdelta_init
  (exampe)
  Input: [View(s1, [(X, Sint)]); Source(base_s1, [(X, Sint]) ]
  Output: +base_s1(X) :- s1(X), not base_s1(X).
          -base_s1(X) :- not s1(X), base_s1(X).
************************************************************** *)
let generate_putdelta_init schema_init =

  let retrieve_view schema_init =
      let schema_view_lst = List.filter (fun x -> match x with View _ -> true | Source _ -> false | _ -> false) schema_init in
      let schema_view = List.hd schema_view_lst in
      let result = get_schema_rterm schema_view in
  result
  in

  let retrieve_source schema_init =
      let schema_source_lst = List.filter (fun x -> match x with View _ -> false | Source _ -> true | _ -> false) schema_init in
      let schema_source = List.hd schema_source_lst in
      let result = get_schema_rterm schema_source in
  result
  in

  let ins_source source_init = match source_init with
    | Pred (rel, varlst) -> Deltainsert(rel, varlst)
    | _ -> invalid_arg "function ins_source called without Pred."
  in

  let del_source source_init = match source_init with
    | Pred (rel, varlst) -> Deltadelete(rel, varlst)
    | _ -> invalid_arg "function del_source called without Pred."
  in

  let view_init = retrieve_view schema_init in
  let source_init = retrieve_source schema_init in
  let source_init_ins = ins_source source_init in
  let source_init_del = del_source source_init in

  let putdelta_init =
      [ Rule (source_init_ins, [Rel(view_init); Not(source_init)] );
        Rule (source_init_del, [Not(view_init); Rel(source_init)] ) ]
  in

putdelta_init
;;
*)

(* **************************************************************
  Generate putdelta_init
  (exampe)
  Input: [View(s1, [(X, Sint)]); Source(base_s1, [(X, Sint]) ]
  Output: +base_s1(X) :- s1(X), not base_s1(X).
          -base_s1(X) :- not s1(X), base_s1(X).
************************************************************** *)
let generate_putdelta_init_1 schema_init target_pred_1 ast_schevo_1 source_rels =

  (* --- functions ------------------------------------------- *)
  let retrieve_view schema_init =
      let schema_view_lst = List.filter (fun x -> match x with View _ -> true | Source _ -> false | _ -> false) schema_init in
      let schema_view = List.hd schema_view_lst in
      let result = get_schema_rterm schema_view in
  result
  in

  let retrieve_source view_init = match view_init with
      | Pred(rel, varlst) -> Pred("base_" ^ rel, varlst)
      | _ -> invalid_arg "function generate_get_init_2"
  in

  let ins_source source_init = match source_init with
    | Pred (rel, varlst) -> Deltainsert(rel, varlst)
    | _ -> invalid_arg "function ins_source called without Pred."
  in

  let del_source source_init = match source_init with
    | Pred (rel, varlst) -> Deltadelete(rel, varlst)
    | _ -> invalid_arg "function del_source called without Pred."
  in

  (* --- parts ------------------------------------------------ *)
  let target_rel_1 = get_rel_from_pred target_pred_1 in
  let target_vars_1 = get_varlst_from_pred target_pred_1 in

  let s = retrieve_view schema_init in
  let s_b = retrieve_source s in
  let s_b_ins = ins_source s_b in (* ∆Sb+ *)
  let s_b_del = del_source s_b in (* ∆Sb- *)

  let s_rel = get_rel_from_pred s in
  let s_varl = get_varlst_from_pred s in

  let ad1_del_rel = get_dif_del target_rel_1 in        (* Ad1- *)

   (* --- putdelta -------------------------------------------- *)
  let putdelta_base = [ Rule (s_b_ins, [Rel(s); Not(s_b)] );
                        Rule (s_b_del, [Not(s); Rel(s_b)] ) ] in


  (* ∆Ad1-- = ∆T1- ∩ Ad1-
     ∆T1- = F1(Sb) ∩ ¬F1(Sb') by naive method
     Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+ *)
  let putdelta_ad1_del =
    let prefix_base = "base_" in
    let ast_f_sb = gen_get_t_sb ast_schevo_1 source_rels prefix_base in
    let ast_f_sb_new = gen_get_t_sb_new ast_schevo_1 s_rel source_rels prefix_base in

    let sb_new =
      [ Rule (Pred("new_" ^ prefix_base ^ s_rel, s_varl),
              [Rel(Pred(prefix_base ^ s_rel, s_varl)); Not (s_b_del) ]
              );
        Rule (Pred("new_" ^ prefix_base ^ s_rel, s_varl),
                [Rel(s_b_ins) ]
              )
      ]
    in

    let t1_del =
      [ Rule (Pred("del_" ^ target_rel_1, target_vars_1),
              [Rel(Pred(target_rel_1, target_vars_1));
               Not (Pred("new_" ^ target_rel_1, target_vars_1))]
             )
      ]
    in

    let dif_d_del =
      [ Rule (Deltadelete(ad1_del_rel, target_vars_1),
              [Rel(Pred("del_" ^ target_rel_1, target_vars_1));
              Rel(Pred(ad1_del_rel, target_vars_1))]
             )
      ]
    in

    (get_sttl ast_f_sb) @ (get_sttl ast_f_sb_new) @ sb_new @ t1_del @ dif_d_del
  in


  (* --- main --- *)
  let putdelta_init =   putdelta_base
                      @ putdelta_ad1_del
  in

putdelta_init
;;


(* **************************************************************
  Generate constratint core
  (exampe)
  Input: [View(s2, [(X, Sint)]); Source(base_s2, [(X, Sint]) ]
         _|_ :- s2(X,Z), not s1(X,_).
  Output: _|_ :- s2(X,Z), not base_s1(X,_).
************************************************************** *)
let generate_const_core ast_constraint_core view_pred base_rel_lst =

  let rec convert sttl_constraint_core view_rel base_rel_lst = match sttl_constraint_core with
    | [] -> []
    | hd::rest -> (_1_convert hd view_rel base_rel_lst) @ (convert rest view_rel base_rel_lst)

    and _1_convert stt view_rel base_rel_lst  = match stt with
      | Rule (h, body) ->
          (* check whether view_rel appears in body as non-negated predicate *)
          let check = view_check body view_rel in
          if check <> []
            then [Rule (h, (_2_convert body view_rel base_rel_lst))]
            else []
      | _ -> []

    and view_check body view_rel = match body with
      | [] -> []
      | hd::rest -> (_1_view_check hd view_rel) @ (view_check rest view_rel)
    and _1_view_check tm view_rel = match tm with
      | Rel(Pred(rel, varlst)) ->
          if rel = view_rel
            then [rel]
            else []
      | _ -> []

    and _2_convert body2 view_rel base_rel_lst = match body2 with
      | [] -> []
      | hd::rest -> (_3_convert hd view_rel base_rel_lst) @ (_2_convert rest view_rel base_rel_lst)

    and _3_convert tm view_rel base_rel_lst = match tm with
      | Rel(Pred(rel, varlst)) ->
          if rel = view_rel
            then [tm]
            else if List.mem ("base_" ^ rel) base_rel_lst
              then [Rel(Pred("base_" ^ rel, varlst))]
              else [tm]
      | Rel(Deltainsert(rel, varlst)) ->
          if rel = view_rel
            then [tm]
            else if List.mem ("base_" ^ rel) base_rel_lst
              then [Rel(Deltainsert("base_" ^ rel, varlst))]
              else [tm]
      | Rel(Deltadelete(rel, varlst)) ->
          if rel = view_rel
            then [tm]
            else if List.mem ("base_" ^ rel) base_rel_lst
              then [Rel(Deltadelete("base_" ^ rel, varlst))]
              else [tm]
      | Not(Pred(rel, varlst)) ->
          if rel = view_rel
            then [tm]
            else if List.mem ("base_" ^ rel) base_rel_lst
              then [Not(Pred("base_" ^ rel, varlst))]
              else [tm]
      | Not(Deltainsert(rel, varlst)) ->
          if rel = view_rel
            then [tm]
            else if List.mem ("base_" ^ rel) base_rel_lst
              then [Not(Deltainsert("base_" ^ rel, varlst))]
              else [tm]
      | Not(Deltadelete(rel, varlst)) ->
          if rel = view_rel
            then [tm]
            else if List.mem ("base_" ^ rel) base_rel_lst
              then [Not(Deltadelete("base_" ^ rel, varlst))]
              else [tm]
      | _ -> [tm]
  in

  let view_rel = get_rel_from_pred view_pred in
  let result = Prog (convert (get_sttl ast_constraint_core) view_rel base_rel_lst) in
result
;;


(* **************************************************************
  Generate putdelta_init
  (exampe)
  Input: [View(s1, [(X, Sint)]); Source(base_s1, [(X, Sint]) ]
  Output: +base_s1(X) :- s1(X), not base_s1(X).
          -base_s1(X) :- not s1(X), base_s1(X).
************************************************************** *)
let generate_putdelta_init_2 schema_init ins_1 del_1 ins_2 del_2 target_pred_1 target_pred_2 ast_schevo_1 ast_schevo_2 source_rels =

  (* --- functions ------------------------------------------- *)
  let retrieve_view schema_init =
      let schema_view_lst = List.filter (fun x -> match x with View _ -> true | Source _ -> false | _ -> false) schema_init in
      let schema_view = List.hd schema_view_lst in
      let result = get_schema_rterm schema_view in
  result
  in

  let retrieve_source view_init = match view_init with
      | Pred(rel, varlst) -> Pred("base_" ^ rel, varlst)
      | _ -> invalid_arg "function generate_get_init_2"
  in

  let ins_source source_init = match source_init with
    | Pred (rel, varlst) -> Deltainsert(rel, varlst)
    | _ -> invalid_arg "function ins_source called without Pred."
  in

  let del_source source_init = match source_init with
    | Pred (rel, varlst) -> Deltadelete(rel, varlst)
    | _ -> invalid_arg "function del_source called without Pred."
  in

  (* --- parts ------------------------------------------------ *)
  let target_rel_1 = get_rel_from_pred target_pred_1 in
  let target_rel_2 = get_rel_from_pred target_pred_2 in
  let target_vars_1 = get_varlst_from_pred target_pred_1 in
  let target_vars_2 = get_varlst_from_pred target_pred_2 in

          (* printf "target_vars_1 => ["; let print_el s = printf "%s; " s in
          List.iter print_el (List.map string_of_var target_vars_1); printf "]\n";
          printf "target_vars_2 => ["; let print_el s = printf "%s; " s in
          List.iter print_el (List.map string_of_var target_vars_2); printf "]\n"; *)

  let s = retrieve_view schema_init in
  let s_b = retrieve_source s in
  let s_b_ins = ins_source s_b in (* ∆Sb+ *)
  let s_b_del = del_source s_b in (* ∆Sb- *)

  let s_rel = get_rel_from_pred s in
  let s_varl = get_varlst_from_pred s in

  let a1_ins_rel = get_nos_ins target_rel_1 s_rel in   (* A1+ *)
  let a1_del_rel = get_nos_del target_rel_1 s_rel in   (* A1- *)
  let a2_ins_rel = get_nos_ins target_rel_2 s_rel in   (* A2+ *)
  let a2_del_rel = get_nos_del target_rel_2 s_rel in   (* A2- *)
  let ad1_del_rel = get_dif_del target_rel_1 in        (* Ad1- *)
  let ad2_del_rel = get_dif_del target_rel_2 in        (* Ad2- *)

(*
     printf "s_rel => %s\n" s_rel;
     printf "s_varlst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map string_of_var s_varl);
        printf "]\n";
     printf "a1_ins => %s\n" a1_ins_rel;
     printf "a1_del => %s\n" a1_del_rel;
     printf "a2_ins => %s\n" a2_ins_rel;
     printf "a2_del => %s\n" a2_del_rel;
     printf "ad1_del => %s\n" ad1_del_rel;
     printf "ad2_del => %s\n" ad2_del_rel;
*)

   (* --- putdelta -------------------------------------------- *)
  let putdelta_base = [ Rule (s_b_ins, [Rel(s); Not(s_b)] );
                        Rule (s_b_del, [Not(s); Rel(s_b)] ) ] in

  (* ∆A1+- = A1+ ∩ ∆Sb- *)
  let putdelta_a1_ins =
    if List.mem s_rel ins_1
      then [ Rule (Deltadelete(a1_ins_rel, s_varl), [Rel(Pred(a1_ins_rel, s_varl)); Rel(s_b_del) ] ) ]
      else []
  in

  (* ∆A1-- = (A1- ∩ ∆Sb+) ∪ (A1- ∩ ∆Sb-) *)
  let putdelta_a1_del =
    if (List.mem s_rel ins_1) && (List.mem s_rel del_1)
      then
      [ Rule (Deltadelete(a1_del_rel, s_varl), [ Rel(Pred(a1_del_rel, s_varl)); Rel(s_b_ins) ]);
        Rule (Deltadelete(a1_del_rel, s_varl), [ Rel(Pred(a1_del_rel, s_varl)); Rel(s_b_del) ]) ]
    else if (List.mem s_rel ins_1) && (not (List.mem s_rel del_1))
      then
      [ Rule (Deltadelete(a1_del_rel, s_varl), [Rel(Pred(a1_del_rel, s_varl)); Rel(s_b_ins)]) ]
    else if (not (List.mem s_rel ins_1)) && (List.mem s_rel del_1)
      then
      [ Rule (Deltadelete(a1_del_rel, s_varl), [Rel(Pred(a1_del_rel, s_varl)); Rel(s_b_del)]) ]
    else
      []
  in

  (* ∆A2+- = A2+ ∩ ∆Sb- *)
  let putdelta_a2_ins =
    if List.mem s_rel ins_2
      then [ Rule (Deltadelete(a2_ins_rel, s_varl), [Rel(Pred(a2_ins_rel, s_varl)); Rel(s_b_del) ] ) ]
      else []
  in

  (* ∆A2-- = (A2- ∩ ∆Sb+) ∪ (A2- ∩ ∆Sb-) *)
  let putdelta_a2_del =
    if (List.mem s_rel ins_2) && (List.mem s_rel del_2)
      then
      [ Rule (Deltadelete(a2_del_rel, s_varl), [ Rel(Pred(a2_del_rel, s_varl)); Rel(s_b_ins) ]);
        Rule (Deltadelete(a2_del_rel, s_varl), [ Rel(Pred(a2_del_rel, s_varl)); Rel(s_b_del) ]) ]
    else if (List.mem s_rel ins_2) && (not (List.mem s_rel del_2))
      then
      [ Rule (Deltadelete(a2_del_rel, s_varl), [Rel(Pred(a2_del_rel, s_varl)); Rel(s_b_ins)]) ]
    else if (not (List.mem s_rel ins_2)) && (List.mem s_rel del_2)
      then
      [ Rule (Deltadelete(a2_del_rel, s_varl), [Rel(Pred(a2_del_rel, s_varl)); Rel(s_b_del)]) ]
    else
      []
  in

  (* ∆Ad1-- = ∆T1- ∩ Ad1-
     ∆T1- = F1(Sb) ∩ ¬F1(Sb') by naive method
     Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+ *)
  let putdelta_ad1_del =
    let prefix_base = "base_" in
    let ast_f_sb = gen_get_t_sb ast_schevo_1 source_rels prefix_base in
    let ast_f_sb_new = gen_get_t_sb_new ast_schevo_1 s_rel source_rels prefix_base in

    let sb_new =
      [ Rule (Pred("new_" ^ prefix_base ^ s_rel, s_varl),
              [Rel(Pred(prefix_base ^ s_rel, s_varl)); Not (s_b_del) ]
              );
        Rule (Pred("new_" ^ prefix_base ^ s_rel, s_varl),
                [Rel(s_b_ins) ]
              )
      ]
    in

    let t1_del =
      [ Rule (Pred("del_" ^ target_rel_1, target_vars_1),
              [Rel(Pred(target_rel_1, target_vars_1));
               Not (Pred("new_" ^ target_rel_1, target_vars_1))]
             )
      ]
    in

    let dif_d_del =
      [ Rule (Deltadelete(ad1_del_rel, target_vars_1),
              [Rel(Pred("del_" ^ target_rel_1, target_vars_1));
              Rel(Pred(ad1_del_rel, target_vars_1))]
             )
      ]
    in

    (get_sttl ast_f_sb) @ (get_sttl ast_f_sb_new) @ sb_new @ t1_del @ dif_d_del
  in

  (* ∆Ad2-- = ∆T2- ∩ Ad2-
     ∆T2- = F2(Sb) ∩ ¬F2(Sb') by naive method
     Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+ *)
  let putdelta_ad2_del =
    let prefix_base = "base_" in
    let ast_f_sb = gen_get_t_sb ast_schevo_2 source_rels prefix_base in
    let ast_f_sb_new = gen_get_t_sb_new ast_schevo_2 s_rel source_rels prefix_base in

    (*
    let sb_new =
      [ Rule (Pred("new_" ^ prefix_base ^ s_rel, s_varl),
              [Rel(Pred(prefix_base ^ s_rel, s_varl)); Not (s_b_del) ]
              );
        Rule (Pred("new_" ^ prefix_base ^ s_rel, s_varl),
                [Rel(s_b_ins) ]
              )
      ]
    in
    *)

    let t2_del =
      [ Rule (Pred("del_" ^ target_rel_2, target_vars_2),
              [Rel(Pred(target_rel_2, target_vars_2));
               Not (Pred("new_" ^ target_rel_2, target_vars_2))]
             )
      ]
    in

    let dif_d_del =
      [ Rule (Deltadelete(ad2_del_rel, target_vars_2),
              [Rel(Pred("del_" ^ target_rel_2, target_vars_2));
              Rel(Pred(ad2_del_rel, target_vars_2))]
             )
      ]
    in

    (get_sttl ast_f_sb) @ (get_sttl ast_f_sb_new) @ t2_del @ dif_d_del
   in

  (* --- main --- *)
  let putdelta_init =   putdelta_base
                      @ putdelta_a1_ins @ putdelta_a1_del @ putdelta_a2_ins @ putdelta_a2_del
                      @ putdelta_ad1_del @ putdelta_ad2_del
  in

putdelta_init
;;

(*
(* --------------------------------------------------------------
  Derive BIRdS program for initial relaitons for single target_rel
------------------------------------------------------------------*)
let derivation_init_birds ast_schemas ast_constraint init_pred_lst log =

  let rec get_base_rels ast_schema = match ast_schema with
      | [] -> []
      | hd::rest -> (_1_get_base_rels hd) @ (get_base_rels rest)
    and _1_get_base_rels stt = match stt with
      | Source(rel, varlst) -> [rel]
      | _ -> []
  in

  let rec derive_all_inits ast_schemas init_pred_lst log = match init_pred_lst with
    | [] -> []
    | hd::rest -> (derive_init ast_schemas hd log) @ (derive_all_inits ast_schemas rest log)

    and derive_init ast_schemas pred log =
      let schema_init = generate_schema ast_schemas pred in
      let get_init = generate_get_init schema_init in
      let putdelta_init = generate_putdelta_init schema_init in
      let base_rel_lst = get_base_rels schema_init in
      let constraint_init = generate_constraint (Prog schema_init) ast_constraint base_rel_lst in

      let ast = Prog (schema_init @ (get_sttl constraint_init) @ get_init @ putdelta_init) in
            if !log
            then begin
              print_endline "ast: "; Expr.print_ast ast; printf "\n";
            end
            else
              ();
      [ast]
  in

  let ast_lst = derive_all_inits ast_schemas init_pred_lst log in
ast_lst
;;
*)

(*
(* generate mapping of (schema_ver, rel_name) for base relations *)
let mpg_init init_pred_lst log physical =

  let rec mapping rel_lst physical = match rel_lst with
    | [] -> []
    | hd::rest -> (_1_mapping hd physical) @ (mapping rest physical)
    and _1_mapping rel physical =
        [(!physical, "base_" ^ rel )]
  in

  let rel_lst = get_rels init_pred_lst in
  let result = mapping rel_lst physical in

result
;;
*)

(* generate mapping of (schema_ver, rel_name) for base relations *)
let mpg_init rel_lst log physical =

  let rec mapping rel_lst physical = match rel_lst with
    | [] -> []
    | hd::rest -> (_1_mapping hd physical) @ (mapping rest physical)
    and _1_mapping rel physical =
        [(!physical, rel )]
  in

  let result = mapping rel_lst physical in
result
;;

(* retrive source (base relations) from init_ast *)
let get_base_rels prog_lst =

  let rec _0_get_base_rels prog_lst = match prog_lst with
    | [] -> []
    | hd::rest -> (_1_get_base_rels hd) @ (_0_get_base_rels rest)
    and _1_get_base_rels prog = match prog with
      | Prog sttl -> _2_get_base_rels sttl
    and _2_get_base_rels sttl = match sttl with
      | [] -> []
      | hd::rest -> (_3_get_base_rels hd) @ (_2_get_base_rels rest)
    and _3_get_base_rels stt = match stt with
      | Source _ -> [stt]
      | _ -> []
  in

  let result = _0_get_base_rels prog_lst in
result
;;


(* --------------------------------------------------------------
  Derive BIRdS program for initial relaitons for ONE target_rel

  % schemas
    view s1(X).            (* S: view *)
    source b_s1(X).        (* Sb: base relation *)
    source dif_i_t1(X).    (* Ad1+: aux for diff *)
    source dif_d_t1(X).    (* Ad1-: aux for diff *)

  % constraint

  % get
    S = get(Sb)
      = Sb

  % putdelta
    (Sb', Ad1+', Ad1-')
     = (Sb, Ad1+, Ad1-) ⨁ putdelta ( (Sb, Ad1+, Ad1-), S')

    % putdelta_base
    Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+
     ∆Sb+ = S' ∩ ¬Sb
     ∆Sb- = ¬S' ∩ Sb

    Ad1+' = Ad1+

    % putdelta_ad1_del
    Ad1-' = Ad1- ∩ ¬∆Ad1--
     ∆Ad1-- = ∆T1- ∩ Ad1-
        ∆T1- = F.inc.1-(∆Sb-, Sb') <- by incrementatilization
             = F1(Sb) ∩ ¬F1(Sb') <- naive method
 *)

(* ------------------------------------------------------------------*)
let derivation_init_birds_1 ast_schemas ast_constraint_core ast_constraint_pk init_pred_lst head_preds_target_1 target_pred_1 ast_schevo_1 source_rels log =

  (*-- functions  ----------------------------------------------------------------------------*)
  let rec get_base_rels ast_schema = match ast_schema with
      | [] -> []
      | hd::rest -> (_1_get_base_rels hd) @ (get_base_rels rest)
    and _1_get_base_rels stt = match stt with
      | Source(rel, varlst) -> [rel]
      | _ -> []
  in

  let rec derive_all_inits ast_schemas ast_constraint_core ast_constraint_pk init_pred_lst target_rel_1 target_vartypes_1  ast_schevo_1 = match init_pred_lst with
    | [] -> []
    | hd::rest -> (derive_init ast_schemas ast_constraint_core ast_constraint_pk hd target_rel_1 target_vartypes_1 ast_schevo_1)
    @ (derive_all_inits ast_schemas ast_constraint_core ast_constraint_pk rest target_rel_1 target_vartypes_1 ast_schevo_1)

    and derive_init ast_schemas ast_constraint_core ast_constraint_pk pred target_rel_1 target_vartypes_1 st_schevo_1 =
      let schema_init = generate_schema_1 ast_schemas pred target_rel_1 target_vartypes_1 in
      let base_rel_lst = get_base_rels schema_init in
      let get_init = generate_get_init schema_init in
      let putdelta_init = generate_putdelta_init_1 schema_init target_pred_1 ast_schevo_1 source_rels in
      let ast_constraint_core_source = generate_const_core ast_constraint_core pred base_rel_lst in
      let ast_constraint_pk_source = filter_pk ast_constraint_pk (get_rel_from_pred pred) in
      let constraints_init = (get_sttl ast_constraint_core_source) @
                             (get_sttl ast_constraint_pk_source) in

      let ast = Prog (schema_init  @ constraints_init @ get_init @ putdelta_init) in
            if !log
            then begin
              print_endline "ast: "; Expr.print_ast ast; printf "\n";
            end
            else
              ();
      [ast]
  in

  (*-- preperations ----------------------------------------------------------------------------*)
  (* target rel *)
  let target_rel_1 = get_rel_from_pred target_pred_1 in
  let target_vartypes_1 = get_vartypes_schema ast_schemas target_rel_1 in

  (*-- main ----------------------------------------------------------------------------*)
  let ast_lst = derive_all_inits ast_schemas ast_constraint_core ast_constraint_pk init_pred_lst target_rel_1 target_vartypes_1 ast_schevo_1 in
ast_lst
;;


(* --------------------------------------------------------------
  Derive BIRdS program for initial relaitons for two target_rels

  % schemas
    view s1(X).            (* S: view *)
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

  % get
    S = get(Sb)
      = Sb

  % putdelta
    (Sb', A1+', A1-', A2+'. A2-', Ad1+', Ad1-', Ad2+', Ad2-')
     = (Sb, A1+, A1-, A2+, A2-, Ad1+, Ad1-, Ad2+, Ad2-) ⨁
      putdelta ( (Sb, A1+, A1-, A2+, A2-, Ad1+, Ad1-, Ad2+, Ad2-), S')

    % putdelta_base
    Sb' = (Sb ∩ ¬∆Sb-) ∪ ∆Sb+
     ∆Sb+ = S' ∩ ¬Sb
     ∆Sb- = ¬S' ∩ Sb

    % putdelta_a1_ins
    A1+' = A1+ ∩ ¬∆A1+-
     ∆A1+- = A1+ ∩ ∆Sb-

    % putdelta_a1_del
    A1-' = A1- ∩ ¬∆A1--
     ∆A1-- = (A1- ∩ ∆Sb+) ∪ (A1- ∩ ∆Sb-)

    % putdelta_a2_ins
    A2+' = A2+ ∩ ¬∆A2+-
     ∆A2+- = A2+ ∩ ∆Sb-

    % putdelta_a2_del
    A2-' = A2- ∩ ¬∆A2--
     ∆A2-- = (A2- ∩ ∆Sb+) ∪ (A2- ∩ ∆Sb-)

    Ad1+' = Ad1+

    % putdelta_ad1_del
    Ad1-' = Ad1- ∩ ¬∆Ad1--
     ∆Ad1-- = ∆T1- ∩ Ad1-
        ∆T1- = F.inc.1-(∆Sb-, Sb') <- by incrementatilization
             = F1(Sb) ∩ ¬F1(Sb') <- naive method

    Ad2+' = Ad2+

    % putdelta_ad2_del
    Ad2-' = Ad2- ∩ ¬∆Ad2--
     ∆Ad2-- = ∆T2- ∩ Ad2-
        ∆T2- = F.inc.2-(∆Sb-, Sb') <- by incrementatilization
             = F2(Sb) ∩ ¬F2(Sb') <- naive method

    target_1_ins_nos_rels =ins_1,
    target_1_del_nos_rels =del_1,
    target_2_ins_nos_rels =ins_2,
    target_2_del_nos_rels =del_2)
 *)
(* ------------------------------------------------------------------*)
let derivation_init_birds_2 ast_schemas ast_constraint_core ast_constraint_pk init_pred_lst head_preds_target_1 head_preds_target_2 target_pred_1 target_pred_2 ast_schevo_1 ast_schevo_2 source_rels ins_1 del_1 ins_2 del_2 log =

  (*-- functions  ----------------------------------------------------------------------------*)
  let rec get_base_rels ast_schema = match ast_schema with
      | [] -> []
      | hd::rest -> (_1_get_base_rels hd) @ (get_base_rels rest)
    and _1_get_base_rels stt = match stt with
      | Source(rel, varlst) -> [rel]
      | _ -> []
  in

  let rec derive_all_inits ast_schemas ast_constraint_core ast_constraint_pk init_pred_lst target_rel_1 target_vartypes_1 target_rel_2 target_vartypes_2 ast_schevo_1 ast_schevo_2 = match init_pred_lst with
    | [] -> []
    | hd::rest -> (derive_init ast_schemas ast_constraint_core ast_constraint_pk hd target_rel_1 target_vartypes_1 target_rel_2 target_vartypes_2 ast_schevo_1 ast_schevo_2)
    @ (derive_all_inits ast_schemas ast_constraint_core ast_constraint_pk rest target_rel_1 target_vartypes_1 target_rel_2 target_vartypes_2 ast_schevo_1 ast_schevo_2)

    and derive_init ast_schemas ast_constraint_core ast_constraint_pk pred target_rel_1 target_vartypes_1 target_rel_2 target_vartypes_2 ast_schevo_1 ast_schevo_2 =
      let schema_init = generate_schema_2 ast_schemas pred target_rel_1 target_vartypes_1  target_rel_2 target_vartypes_2 in
      let base_rel_lst = get_base_rels schema_init in
      (* let constraint_init = generate_constraint (Prog schema_init) ast_constraint base_rel_lst in *)
      let get_init = generate_get_init schema_init in
      let putdelta_init = generate_putdelta_init_2 schema_init ins_1 del_1 ins_2 del_2 target_pred_1 target_pred_2 ast_schevo_1 ast_schevo_2 source_rels in
      let ast_constraint_core_source = generate_const_core ast_constraint_core pred base_rel_lst in
      let ast_constraint_pk_source = filter_pk ast_constraint_pk (get_rel_from_pred pred) in
      let constraints_init = (get_sttl ast_constraint_core_source) @
                             (get_sttl ast_constraint_pk_source) in

      let ast = Prog (schema_init  @ constraints_init @ get_init @ putdelta_init) in
            if !log
            then begin
              print_endline "ast: "; Expr.print_ast ast; printf "\n";
            end
            else
              ();
      [ast]
  in

  (*-- preperations ----------------------------------------------------------------------------*)
  (* target rel *)
  let target_rel_1 = get_rel_from_pred target_pred_1 in
  let target_rel_2 = get_rel_from_pred target_pred_2 in
  let target_vartypes_1 = get_vartypes_schema ast_schemas target_rel_1 in
  let target_vartypes_2 = get_vartypes_schema ast_schemas target_rel_2 in

(*
  (* list of source rels which reflected update from one target rel is not shared to another target rel *)
  let target_1_ins_nos_rels = unique_element @@ get_rels @@
        List.filter (fun x -> match x with Deltainsert_nos _ -> true | _ -> false) head_preds_target_1 in
  let target_1_del_nos_rels = unique_element @@ get_rels @@
        List.filter (fun x -> match x with Deltadelete_nos _ -> true | _ -> false) head_preds_target_1 in
  let target_2_ins_nos_rels = unique_element @@ get_rels @@
      List.filter (fun x -> match x with Deltainsert_nos _ -> true | _ -> false) head_preds_target_2 in
  let target_2_del_nos_rels = unique_element @@ get_rels @@
      List.filter (fun x -> match x with Deltadelete_nos _ -> true | _ -> false) head_preds_target_2 in

      printf "target_1_ins_nos_rels=> ["; let print_el s = printf "%s; " s in
      List.iter print_el target_1_ins_nos_rels; printf "]\n";

      printf "target_1_del_nos_rels => ["; let print_el s = printf "%s; " s in
      List.iter print_el target_1_del_nos_rels; printf "]\n";

      printf "target_2_ins_nos_rels=> ["; let print_el s = printf "%s; " s in
      List.iter print_el target_2_ins_nos_rels; printf "]\n";

      printf "target_2_del_nos_rels => ["; let print_el s = printf "%s; " s in
      List.iter print_el target_2_del_nos_rels; printf "]\n\n";
*)


  (*-- main ----------------------------------------------------------------------------*)
  let ast_lst = derive_all_inits ast_schemas ast_constraint_core ast_constraint_pk init_pred_lst target_rel_1 target_vartypes_1 target_rel_2 target_vartypes_2 ast_schevo_1 ast_schevo_2 in
ast_lst
;;
