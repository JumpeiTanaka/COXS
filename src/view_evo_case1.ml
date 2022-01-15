(* @author: Jumpei Tanaka *)

  (* **************************************************************** *)
  (* Step 4-1: Evolutional relations: case1 - no backward propagation *)
  (* **************************************************************** *)

open Expr;;
open Utils;;
open Tools;;
open View_common;;
open Printf;;

(*********************************************
  In: AST of schema, pred of target schema, AST of rules for target schema
  Out: AST of BIRDS program for schema
*********************************************)
let generate_schema_1 ast_schemas target_pred ast_pred base_rel_sttl base_rel_lst =

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

  let rec generate_source ast_pred base_rel_sttl base_rel_lst = match ast_pred with
    | Prog sttl -> _1_generate_source sttl base_rel_sttl base_rel_lst
    and _1_generate_source sttl base_rel_sttl base_rel_lst = match sttl with
      | [] -> []
      | hd::rest -> (_2_generate_source hd base_rel_sttl base_rel_lst)
                    @ (_1_generate_source rest base_rel_sttl base_rel_lst)
    and _2_generate_source stt base_rel_sttl base_rel_lst = match stt with
      | Rule (Pred(rel, varlst), bodylst) -> _3_generate_source bodylst base_rel_sttl base_rel_lst
      | _ -> []
    and _3_generate_source bodylst base_rel_sttl base_rel_lst = match bodylst with
      | [] -> []
      | hd::rest -> (_4_generate_source hd base_rel_sttl base_rel_lst)
                      @ (_3_generate_source rest base_rel_sttl base_rel_lst)
    and _4_generate_source tm base_rel_sttl base_rel_lst = match tm with
      | Rel (Pred (rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then _5_generate_source rel base_rel_sttl
          else []
      | Not (Pred (rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then _5_generate_source rel base_rel_sttl
          else []
      | _ -> []
    and _5_generate_source rel base_rel_sttl = match base_rel_sttl with
      | [] -> []
      | hd::rest -> (_6_generate_source rel hd) @ (_5_generate_source rel rest)
    and _6_generate_source rel stt = match stt with
      | Source (rel_name, varlst) ->
          if rel_name = ("base_" ^ rel)
          then [stt]
          else []
      | _ -> []
  in

  let rec generate_aux ast_schemas pred_rel_name = match ast_schemas with
    | Prog sttl -> _1_generate_aux sttl pred_rel_name
    and _1_generate_aux sttl pred_rel_name = match sttl with
      | [] -> []
      | hd::rest -> (_2_generate_aux hd pred_rel_name) @ (_1_generate_aux rest pred_rel_name)
    and _2_generate_aux stt pred_rel_name = match stt with
      | Target_schema (_, rel, varlst) ->
          if rel = pred_rel_name
          then [Source( ("ins_" ^ rel), varlst); Source( ("del_" ^ rel), varlst) ]
          else []
      | _ -> []
  in

  let pred_rel_name = get_predname target_pred in
  let view_sttl = generate_view ast_schemas pred_rel_name in
  let source_sttl = unique_element @@ generate_source ast_pred base_rel_sttl base_rel_lst in
  let aux_sttl = generate_aux ast_schemas pred_rel_name in
  let ast_schema_1 = Prog (view_sttl @ source_sttl @ aux_sttl) in

      (*
      print_endline "ast_schemas:"; Expr.print_ast ast_schemas; printf "\n";
      printf "pred_rel_name = %s\n" pred_rel_name;
      print_endline "view_sttl:"; Expr.print_sttlst view_sttl; printf "\n";
      print_endline "source_sttl:"; Expr.print_sttlst source_sttl; printf "\n";
      print_endline "aux_sttl:"; Expr.print_sttlst aux_sttl; printf "\n";
      print_endline "ast_schema_1:"; Expr.print_ast ast_schema_1; printf "\n";
      *)

ast_schema_1
;;

(* **************************************************************
  Generate get_1
  Input: list of rules, e.g. t1(A,B) :- s1(A,B), B=1. ,
         predicate of evolved relation,
         list of base relation names
  Output: list of rules, e.g.
          tmp_t1(A,B) :- base_s1(A,B), B=1.
          t1(A,B) :- tmp_t1(A,B), not del_t1(A,B).
          t1(A,B) :- ins_t1(A,B).
************************************************************** *)
let generate_get1 ast pred base_rel_lst =

  let rec reform ast pred base_rel_lst = match ast with
    | Prog sttl -> _1_reform sttl pred base_rel_lst

    and _1_reform sttl pred base_rel_lst = match sttl with
      | [] -> []
      | hd::rest -> (_2_reform hd pred base_rel_lst) @ (_1_reform rest pred base_rel_lst)

    and _2_reform stt pred base_rel_lst = match stt with
      | Rule (Pred(rel, varlst), bodylst ) ->
           if Pred(rel, varlst) = pred
           then
              [ Rule (Pred( ("tmp_" ^ rel), varlst), (_3_reform bodylst base_rel_lst ));
                Rule (Pred (rel, varlst), [ Rel(Pred( ("tmp_" ^ rel), varlst)); Not(Pred( ("del_" ^ rel), varlst)) ]  );
                Rule (Pred (rel, varlst), [ Rel(Pred( ("ins_" ^ rel), varlst)) ]  )
              ]
           else
              [Rule (Pred(rel, varlst), (_3_reform bodylst base_rel_lst ))]
      | _ -> invalid_arg "function reform_ast_pred called without rules in ast"

    and _3_reform bodylst base_rel_lst = match bodylst with
      | [] -> []
      | hd::rest -> (_4_reform hd base_rel_lst) @ (_3_reform rest base_rel_lst)

    and _4_reform tm base_rel_lst = match tm with
      | Rel (Pred(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then [Rel (Pred (("base_" ^ rel), varlst))]
          else [tm]
      | Not (Pred(rel, varlst)) ->
          if List.mem ("base_" ^ rel) base_rel_lst
          then [Not (Pred(("base_" ^ rel), varlst))]
          else [tm]
      | _ -> [tm]
    in

  let result = Prog (reform ast pred base_rel_lst) in
result
;;

(* **************************************************************
  Generate putdelta_1
  Input: target predicate, e.g. t1(A,B)
  Output: list of rules, e.g.
          +ins_t(A,B) :- t(A,B), not tmp_t(A,B), not ins_t(A,B).
          -ins_t(A,B) :- not t(A,B), ins_t(A,B).
          +del_t(A,B) :- not t(A,B), tmp_t(A,B), not del_t(A,B).
          -del_t(A,B) :- not t(A,B), del_t(A,B).
          _|_ :- ins_t(A,B), des_t(A,B).
************************************************************** *)
let generate_putdelta1 target_pred =

    let generate target_pred = match target_pred with
      | Pred (rel, varlst) ->
          [ Rule ( Deltainsert( ("ins_" ^ rel), varlst),
                   [Rel(Pred(rel, varlst)); Not(Pred(("tmp_" ^ rel), varlst)); Not(Pred(("ins_" ^ rel), varlst)) ]   );
            Rule ( Deltadelete( ("ins_" ^ rel), varlst),
                     [Not(Pred(rel, varlst));  Rel(Pred(("ins_" ^ rel), varlst)) ]   );
            Rule ( Deltainsert( ("del_" ^ rel), varlst),
                     [Not(Pred(rel, varlst)); Rel(Pred(("tmp_" ^ rel), varlst)); Not(Pred(("del_" ^ rel), varlst)) ]   );
            Rule ( Deltadelete( ("del_" ^ rel), varlst),
                     [Rel(Pred(rel, varlst));  Rel(Pred(("del_" ^ rel), varlst)) ]   );
            Rule ( get_empty_pred,
                     [Rel(Pred(("ins_" ^ rel), varlst)); Rel(Pred(("del_" ^ rel), varlst)) ]  )
          ]
      | _ -> invalid_arg "function generate_putdelta1 called without Pred"
    in

    let putdelta1 = Prog (generate target_pred) in

putdelta1
;;

(* Derive BIRdS program for case 1 relaitons *)
let derivation_case1_birds ast_schemas ast_constraint ast_schevo case1_pred_lst base_rel_sttl log =

  let rec derive_all_case1 ast_schemas ast_constraint ast_schevo pred_lst base_rel_sttl base_rel_lst log = match pred_lst with
    | [] -> []
    | hd::rest ->
        (_1_derive_case1 ast_schemas ast_constraint ast_schevo hd base_rel_sttl base_rel_lst log)
        @ (derive_all_case1 ast_schemas ast_constraint ast_schevo rest base_rel_sttl base_rel_lst log)

    and _1_derive_case1 ast_schemas ast_constraint ast_schevo target_pred base_rel_sttl base_rel_lst log =
      let ast_pred = get_one_query ast_schevo target_pred in
      let schema_1 = generate_schema_1 ast_schemas target_pred ast_pred base_rel_sttl base_rel_lst in
      let get_1 = generate_get1 ast_pred target_pred base_rel_lst in
      let putdelta_1 = generate_putdelta1 target_pred in
      let constraint_1 = generate_constraint schema_1 ast_constraint base_rel_lst in

      let ast = List.fold_left merge_ast (Prog []) [schema_1; constraint_1; get_1; putdelta_1]  in
      (* let ast = merge_ast schema_1 get_1  in *)

            if !log
            then begin
              print_endline "ast: "; Expr.print_ast ast; printf "\n";
            end
            else
              ();

      [ast]
  in

  let base_rel_lst = get_rels @@ Expr.source2pred base_rel_sttl in
  let ast_lst = derive_all_case1 ast_schemas ast_constraint ast_schevo case1_pred_lst base_rel_sttl base_rel_lst log in

    (*
      if !log
      then begin
       print_endline "base_rel_sttl:";  print_sttlst base_rel_sttl; printf "\n";
      end
      else
        ();
    *)

ast_lst
;;

(* generate mapping of (schema_ver, rel_name) for case1 relations *)
let mpg_1 case1_pred_lst log physical =

  let rec mapping rel_lst physical = match rel_lst with
    | [] -> []
    | hd::rest -> (_1_mapping hd physical) @ (mapping rest physical)
    and _1_mapping rel physical =
      [(!physical, "ins_" ^ rel); (!physical, "del_" ^ rel)]
  in

  let rel_lst = get_rels case1_pred_lst in
  let aux_mpg = mapping rel_lst physical in

      (*
            printf "aux_mpg => [";
            let print_el s = printf "(%s, %s); " (fst s) (snd s) in
            List.iter print_el aux_mpg;
            printf "]\n\n";
      *)

aux_mpg
;;
