(* @author: Jumpei Tanaka *)

  (* **************************************************************** *)
  (* Common tools for derivation of views and schemas                 *)
  (* **************************************************************** *)

open Expr;;
open Utils;;
open Tools;;
open Printf;;


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
  Output: _|_ :- t1(A,B), A=1. _|_ :- s1(A,B), s1(A,B1), not B=B1.
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
