(* @author: Jumpei Tanaka *)

  (* ********************************************************** *)
  (* Step 3: Initial relations: derivation of views and schemas *)
  (* ********************************************************** *)

open Expr;;
open Utils;;
open Tools;;
open View_common;;
open Printf;;

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


(* Derive BIRdS program for initial relaitons *)
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
