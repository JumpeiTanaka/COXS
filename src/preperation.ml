(* @author: Jumpei Tanaka *)

open Expr;;
open Utils;;
open Tools;;
open Printf;;



(* make a pair (dbschema, relname) from Source_schema or Target_schema *)
let rec get_sch_rel schema = match schema with
  | Source_schema (dbschema, relname, _) -> (dbschema, relname)
  | Target_schema (dbschema, relname, _) -> (dbschema, relname)
  | _ -> invalid_arg "function Strategy.get_sch_rel"

(* string of (schema, rel) mapping *)
let rec string_of_mpg lst = match lst with
 | [] -> ""
 | hd::rest -> "(" ^ (fst hd) ^ "," ^ (snd hd) ^ "); " ^ (string_of_mpg rest)
;;

(* *************************************************************************
  preperation
****************************************************************************)
(* preprocess to make constraint to rule *)
let constraint2rule prog =

    let rec to_rule prog bwd_ins_lst = match prog with
      | Prog stt_lst -> _1_to_rule stt_lst bwd_ins_lst
      and _1_to_rule sttl_lst bwd_ins_lst = match sttl_lst with
        | [] -> []
        | hd::rest -> (_2_to_rule hd bwd_ins_lst) @ (_1_to_rule rest bwd_ins_lst)
      and _2_to_rule hd bwd_ins_lst = match hd with
        | Rule _ -> [hd]
        | Constraint _ -> [rule_of_constraint hd]
        | Pk (relname, attrlst) ->
          (* generate datalog rules for a primary key *)
          let schema_stt =
            try (List.find (fun x -> relname = (get_schema_name x)) (get_schema_stts prog) )
            with Not_found -> raise (SemErr ("Not found the relation "^relname^ " in the primary key constraint \n"^ string_of_stt hd))
          in
          let allattrlst = get_schema_attrs schema_stt in
          let allattrlst2 = List.map (fun x -> if (List.mem x attrlst) then x else x^"2") allattrlst in
          let nonkeyattrlst = List.filter (fun x -> not (List.mem x attrlst)) allattrlst in
          let derive_key_const x =
                if List.mem relname bwd_ins_lst
                then
                  Rule(get_empty_pred,
                                      [Rel (Deltainsert(relname, List.map (fun t -> NamedVar t) allattrlst));
                                       Rel (Pred(relname, List.map (fun t -> NamedVar t) allattrlst2));
                                       Ineq ("<>", Var (NamedVar x), Var (NamedVar (x^"2")))]
                      )
                else
                  Rule(get_empty_pred,
                                      [Rel (Pred(relname, List.map (fun t -> NamedVar t) allattrlst));
                                       Rel (Pred(relname, List.map (fun t -> NamedVar t) allattrlst2));
                                       Ineq ("<>", Var (NamedVar x), Var (NamedVar (x^"2")))]
                      )
          in
          let result = List.map derive_key_const nonkeyattrlst in
          result
          (* (List.map (fun x -> Rule(get_empty_pred, [Rel (Pred(relname, List.map (fun t -> NamedVar t) allattrlst)); Rel (Pred(relname, List.map (fun t -> NamedVar t) allattrlst2)); Equal(Var (NamedVar x), Var (NamedVar (x^"2")))] )) nonkeyattrlst )@lst *)
        | Query _ -> [hd]
        | Source _ -> [hd]
        | View _ -> [hd]
        | Source_schema _ -> [hd]
        | Target_schema _ -> [hd]
    in

    let bwd_ins_lst = unique_element @@ list_conjunction (get_bwd_ins_lst prog)   (get_target_schema_rels prog) in

    let updated_stt_lst = to_rule prog bwd_ins_lst in

    Prog(updated_stt_lst)
;;


(* get pk list *)
let get_pk_pred prog log =

    let rec get sttl = match sttl with
      | [] -> []
      | hd::rest -> (_1_get hd) @ (get rest)
      and _1_get stt = match stt with
        | Pk (relname, attrlst) -> [(relname, attrlst)]
        | _ -> []
    in

    let pk_lst = get (get_sttl prog) in

      if !log
      then begin
        printf "pk_lst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map fst pk_lst);
        printf "]\n\n"
      end
      else
        ();

pk_lst
;;


(* --- schema mapping --------------------------------------- *)
let schema_mapping prog log =
    (* schema mapping *)
    let source_schema = get_source_schemas prog in
    let source_rels_mpg = List.map (get_sch_rel) source_schema in
    let target_schema = get_target_schemas prog in
    let target_rels_mpg = List.map (get_sch_rel) target_schema in
    let schema_mpg = source_rels_mpg @ target_rels_mpg in

        (* print *)
        if !log
        then begin
          (* print_endline "source_schema = ";
          printf "%s\n" (List.fold_right (^) (List.map string_of_stt source_schema) ""); *)
          printf "source_rels_mpg = %s\n\n" ("[" ^ (string_of_mpg source_rels_mpg) ^ "]");

          (* print_endline "target_schema = ";
          printf "%s\n" (List.fold_right (^) (List.map string_of_stt target_schema) ""); *)
          printf "target_rels_mpg = %s\n\n" ("[" ^ (string_of_mpg target_rels_mpg) ^ "]")
        end
        else
          ();

schema_mpg
;;


(* --- get predicates (rterm) in source schema --------------------------------------- *)
let get_source_preds prog log =
  let source_pred_lst = Utils.get_source_rterms prog in
      (* print *)
      if !log
      then begin
        printf "source_pred_lst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map string_of_rterm source_pred_lst);
        printf "]\n\n"
      end
      else
        ();

source_pred_lst
;;

(* --- get rel list of insert to source --------------------------------------- *)
let get_source_ins_rels prog source_rels log =

  let rec get sttl source_rels = match sttl with
    |  [] -> []
    | hd::rest -> (_1_get hd source_rels ) @ (get rest source_rels)
    and _1_get stt source_rels = match stt with
      | Rule (Deltainsert(rel, _), _) ->
          if List.mem rel source_rels
            then [rel]
            else []
      | _ -> []
  in

  let source_ins_rels = get (get_sttl prog) source_rels in

      if !log
      then begin
        printf "source_ins_rels => [";
        let print_el s = printf "%s; " s in
        List.iter print_el source_ins_rels;
        printf "]\n\n"
      end
      else
        ();

source_ins_rels
;;

(* --- get rel list of insert to source --------------------------------------- *)
let get_source_del_rels prog source_rels log =

  let rec get sttl source_rels = match sttl with
    |  [] -> []
    | hd::rest -> (_1_get hd source_rels) @ (get rest source_rels)
    and _1_get stt source_rels = match stt with
      | Rule (Deltadelete(rel, _), _) ->
          if List.mem rel source_rels
            then [rel]
            else []
      | _ -> []
  in

  let source_del_rels = get (get_sttl prog) source_rels in

      if !log
      then begin
        printf "source_del_rels => [";
        let print_el s = printf "%s; " s in
        List.iter print_el source_del_rels;
        printf "]\n\n"
      end
      else
        ();

source_del_rels
;;

(* --- get predicates (rterm) in target schema --------------------------------------- *)
let get_target_preds prog log =
  let target_pred_lst = Utils.get_target_rterms prog in
      (* print *)
      if !log
      then begin
        printf "target_pred_lst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map string_of_rterm target_pred_lst);
        printf "]\n\n"
      end
      else
        ();

target_pred_lst
;;

(* --- get predicates (rterm) of head relations --------------------------------------- *)
let get_head_preds prog log =
  let rule_lst = Expr.get_rule_stts prog in
  let head_pred_lst = Utils.get_rulehead_rterms prog in
      (* print *)
      if !log
      then begin
        printf "head_pred_lst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map string_of_rterm head_pred_lst);
        printf "]\n\n"
      end
      else
       ();

head_pred_lst
;;

(* --- get predicates (rterm) of initial relations --------------------------------------- *)
let get_init_preds source_pred_lst target_pred_lst head_pred_lst log =
  let s_init_pred_lst = list_setminus source_pred_lst head_pred_lst in
  let t_init_pred_lst = list_setminus target_pred_lst head_pred_lst in
  let init_pred_lst = s_init_pred_lst @  t_init_pred_lst in

      (* print *)
      if !log
      then begin
        printf "init_pred_lst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map string_of_rterm init_pred_lst);
        printf "]\n\n";
      end
      else
        ();

init_pred_lst
;;

(* --- get predicates (rterm) of evolved relations --------------------------------------- *)
let get_evolved_preds target_pred_lst init_pred_lst log =
  let evolved_pred_lst = list_setminus target_pred_lst init_pred_lst in

      (* print *)
      if !log
      then begin
        printf "evolved_pred_lst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map string_of_rterm evolved_pred_lst);
        printf "]\n\n";
      end
      else
        ();

evolved_pred_lst
;;

(* --- get predicates (rterm) of evolved relations with backward propagation rules -------- *)
let get_evolved_bwd_preds evolved_pred_lst ast_bwd log =

  let bwd_delta_ins_lst = unique_element @@ get_bwd_ins_lst ast_bwd in
  let bwd_delta_del_lst = unique_element @@ get_bwd_del_lst ast_bwd in
  let evolved_rel_lst = get_rels evolved_pred_lst in
  let evolved_bwd_rel_lst = unique_element @@ (list_conjunction evolved_rel_lst bwd_delta_ins_lst ) @ (list_conjunction evolved_rel_lst bwd_delta_del_lst ) in

  let evolved_bwd_pred_lst = filter_pred_rellst evolved_pred_lst evolved_bwd_rel_lst in

      (* print *)
      if !log
      then begin
        printf "evolved_bwd_pred_lst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map string_of_rterm evolved_bwd_pred_lst);
        printf "]\n\n";
      end
      else
        ();

evolved_bwd_pred_lst
;;

(* pred (rterm) of evolved relations without backward propagation rules *)
let get_case1_preds target_pred_lst init_pred_lst evolved_bwd_pred_lst log =
  let case1_pred_lst = List.fold_left list_setminus target_pred_lst
                       [init_pred_lst; evolved_bwd_pred_lst] in

      if !log
      then begin
        printf "case1_pred_lst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map string_of_rterm case1_pred_lst);
        printf "]\n\n";
      end
      else
        ();

  case1_pred_lst
;;



(* --- schemas --------------------------------------- *)
let get_schemas ast  log =

  let rec filter ast = match ast with
    | Prog sttl -> _1_filter sttl

    and _1_filter sttl = match sttl with
      | [] -> []
      | hd::rest -> (_2_filter hd) @ (_1_filter rest)

    and _2_filter hd  = match hd with
      | Source _ -> [hd]
      | View _ -> [hd]
      | Source_schema _ -> [hd]
      | Target_schema _ -> [hd]
      | _ -> []
  in

  let ast_schemas = Prog (filter ast) in
      (* print *)
      if !log
      then begin
        print_endline "--- function: get_schemas ---";
        print_endline "ast_schemas: "; Expr.print_ast ast_schemas; printf "\n";
      end
      else
        ();

ast_schemas
;;


(* --- rules of constraints --------------------------------------- *)
let get_constraints ast log =

  let rec filter ast = match ast with
    | Prog sttl -> _1_filter sttl

    and _1_filter sttl = match sttl with
      | [] -> []
      | hd::rest -> (_2_filter hd) @ (_1_filter rest)

    and _2_filter hd  = match hd with
      | Rule (h, b) ->
          if h == Expr.get_empty_pred
          then [Rule (h, b)]
          else []
      | _ -> []
  in

  let ast_constraint = Prog (filter ast) in
      (* print *)
      if !log
      then begin
        print_endline "--- function: get_constraints ---";
        print_endline "ast_constraint: "; Expr.print_ast ast_constraint; printf "\n";
      end
      else
        ();

ast_constraint
;;


(*********************************************
  In: AST,
      Prog [Rule(Pred(name1, varlst1), bodylst1); Rule(Pred(name3, varlst3), bodylst3);...],
      [name_a, name_b], // relation names which are being in body of rules in Prog
      [name_x, name_y], // relation names which are being in body of rules in Prog but not to be cared
  Out: Prog [Rule(Pred(name1, varlst1), bodylst1); Rule(Pred(name3, varlst3), bodylst3);...;
             Rule(Pred(name_a, varlst_a), bodylst_a); Rule(Pred(name_a, varlst_a), bodylst_a); ... ;
           ...; ]
*********************************************)
let schevo_queries ast rules rels exclude_rels =

  let rec get_schevo_rules ast rel_lst = match ast with
    | Prog sttl -> _1_get_schevo_rules sttl rel_lst

    and _1_get_schevo_rules sttl rel_lst = match sttl with
        | [] -> []
        | hd::rest -> (_2_get_schevo_rules hd rel_lst) @ (_1_get_schevo_rules rest rel_lst)

    and _2_get_schevo_rules hd rel_lst = match hd with
        | Rule (Pred(rel, varlst), bodylst) ->
                  if List.mem rel rel_lst
                  then [Rule (Pred(rel, varlst), bodylst)]
                  else []
        | _ -> []
    in

  let rec _1_all_queries ast rules rels exclude_rels =
    let rels_schevo = list_setminus rels exclude_rels in
    let new_rules = get_schevo_rules ast rels_schevo in
    let new_rels = unique_element (get_rels_body (Prog (new_rules))) in
    let total_rules = Prog (unique_element ((Expr.get_sttl rules) @ new_rules)) in
        (*
        printf "rels_schevo => [";
        let print_el s = printf "%s; " s in
        List.iter print_el rels_schevo;
        printf "]\n\n";

        print_endline "new_rules : "; Expr.print_ast (Prog(new_rules)); printf "\n";

        printf "new_rels => [";
        let print_el s = printf "%s; " s in
        List.iter print_el new_rels;
        printf "]\n\n";

        print_endline "total_rules : "; Expr.print_ast total_rules; printf "\n";
        *)

    if List.length new_rules == 0
    then
      total_rules
    else
      _1_all_queries ast total_rules new_rels exclude_rels
  in

  let result = _1_all_queries ast rules rels exclude_rels in
result
;;

(* --- rules of schema evolution --------------------------------------- *)
let get_schevo_rules ast target_pred_lst source_pred_lst log =

  let rec filter ast target_pred_lst = match ast with
    | Prog sttl -> _1_filter sttl target_pred_lst

    and _1_filter sttl target_pred_lst = match sttl with
      | [] -> []
      | hd::rest -> (_2_filter hd target_pred_lst) @ (_1_filter rest target_pred_lst)

    and _2_filter hd target_pred_lst = match hd with
      | Rule (h, b) ->
          if List.mem h target_pred_lst
          then [Rule (h, b)]
          else []
      | _ -> []
  in

  let schevo_rules_init = Prog (filter ast target_pred_lst) in
  let body_rels_init = get_rels_body schevo_rules_init in
  let source_rels_excluded = get_rels source_pred_lst in
  let ast_schevo = schevo_queries ast schevo_rules_init body_rels_init source_rels_excluded in

      (* print *)
      if !log
      then begin
        print_endline "--- function: get_schevo_rules ---";
        print_endline "ast_schevo : "; Expr.print_ast ast_schevo; printf "\n";
      end
      else
        ();

ast_schevo
;;

(* --- rules of backward propagation --------------------------------------- *)
let get_bwd_rules ast ast_schemas ast_constraint ast_schevo log =
  let ast1 = Expr.subtract_ast ast ast_schemas in
  let ast2 = Expr.subtract_ast ast1 ast_constraint in
  let ast_bwd = Expr.subtract_ast ast2 ast_schevo in
      (* print *)
      if !log
      then begin
        print_endline "--- function: get_bwd_rules ---";
        print_endline "ast_bwd: "; Expr.print_ast ast_bwd; printf "\n";
      end
      else
        ();

ast_bwd
;;

(* --- check a written strategy --------------------------------------- *)
let check prog_bwd evolved_pred_lst log =

  (* checks number of evolved relations in target schema, return error msg is more than two *)
  (* This check is being eliminated by Jumpei Tanaka *)
  (*
  let one_evolved_rel_lst =
    let num = List.length evolved_pred_lst in
    if num >= 2
      then
        let msg_error = ["Target schema contains more than two evolved relations."] in
        msg_error
      else
        let msg_sound = [] in
        msg_sound
     in
  *)

  (* --- checks linear restriction --- *)
  (* t as an evolved predicate *)
  (* check no t or not t in a rule body of backward propagation *)

  let rec no_pred prog_bwd evolved_pred_lst = match prog_bwd with
    | Prog sttl -> _1_no_pred sttl evolved_pred_lst
    and _1_no_pred sttl evolved_pred_lst = match sttl with
        | [] -> []
        | rd::rest -> (_2_no_pred rd evolved_pred_lst) @ (_1_no_pred rest evolved_pred_lst)
    and _2_no_pred rd evolved_pred_lst = match rd with
        | Rule(_, bodylst) -> _3_no_pred bodylst evolved_pred_lst
        | _ -> invalid_arg "A function no_pred is called without rules."
    and _3_no_pred bodylst evolved_pred_lst = match bodylst with
        | [] -> []
        | hd::rest -> (_4_no_pred hd evolved_pred_lst) @ (_3_no_pred rest evolved_pred_lst)
    and _4_no_pred hd evolved_pred_lst = match hd with
        | Rel (Pred(rel, varlst)) ->
            if List.mem (Pred(rel, varlst)) evolved_pred_lst
            then
              ["Error: An evolved predicte occurs as an ordinary predicate in rule body of backward propagation."]
            else
              []
        | Not (Pred(rel, varlst)) ->
            if List.mem (Pred(rel, varlst)) evolved_pred_lst
            then
              ["Error: An evolved predicte occurs as an ordinary predicate in rule body of backward propagation."]
            else
              []
        | _ -> []
  in

  let atmost_one prog_bwd evolved_pred_lst =

    let rec _0_atmost_one prog_bwd evolved_rel_lst = match prog_bwd with
        | Prog sttl -> _1_atmost_one sttl evolved_rel_lst
      and _1_atmost_one sttl evolved_rel_lst = match sttl with
        | [] -> []
        | hd::rest -> (_2_atmost_one hd evolved_rel_lst) @ (_1_atmost_one rest evolved_rel_lst)
      and _2_atmost_one stt evolved_rel_lst = match stt with
        | Rule(_, bodylst) -> _3_atmost_one bodylst evolved_rel_lst
        | _ -> invalid_arg "A function atmost_one is called without rules."
      and _3_atmost_one bodylst evolved_rel_lst =
        let rels_inbody_lst = _4_atmost_one bodylst evolved_rel_lst in
        if (List.length rels_inbody_lst) >= 2
        then
          ["Error: Delta predicates occur more than twice in body of backward propagation rules."]
        else
          []
      and _4_atmost_one bodylst evolved_rel_lst = match bodylst with
        | [] -> []
        | hd::rest -> (_5_atmost_one hd evolved_rel_lst) @ (_4_atmost_one rest evolved_rel_lst)
      and _5_atmost_one tm evolved_res_lst = match tm with
        | Rel(Deltainsert(rel, _))
        | Rel(Deltadelete(rel, _))
            -> if List.mem rel evolved_res_lst
               then
                  [rel]
               else
                  []
         | _ -> []
    in

    let evolved_rel_lst = get_rels evolved_pred_lst in
    let result = _0_atmost_one prog_bwd evolved_rel_lst in
    result
  in

  (* checks monotone restriction *)
  let monotone prog_bwd =

    let rec _0_monotone prog_bwd = match prog_bwd with
      | Prog sttl -> _1_monotone sttl
      and _1_monotone sttl = match sttl with
        | [] -> []
        | hd::rest -> (_2_monotone hd) @ (_1_monotone rest)
      and _2_monotone stt =
        let monotonicity_opposite = opp_monotone stt in
        let monotonicity_same_ins = same_ins_monotone stt in
        let monotonicity_same_del = same_del_monotone stt in

        (*
          If a rule of head is +/- delta predicate and has opposide side of -/+ delta predicate in body,
           monotonicity_opposite has some rel names in a lsit, [rel; rel;...].
          If a rule of head is +/- delta predicate and does not have +/- delta predicate in body,
          monotonicity_same_ins/del is []
        *)
        if (  (List.length monotonicity_opposite != 0)  ||
              ( (List.length monotonicity_same_ins = 0)  && (List.length monotonicity_same_del = 0) )
           )
        then
          ["Error: Some backward propagation rules are not monotone."]
        else
          []

      and opp_monotone stt = match stt with
        | Rule (Deltainsert (rel, varlst), bodylst ) -> opp_ins_monotone bodylst
        | Rule (Deltadelete (rel, varlst), bodylst ) -> opp_del_monotone bodylst
        | _ -> []
      and opp_ins_monotone bodylst = match bodylst with
        | [] -> []
        | hd::rest -> (_1_opp_ins_monotone hd) @ (opp_ins_monotone rest)
      and _1_opp_ins_monotone tm = match tm with
        | Rel (Deltadelete (rel, varlst)) -> [rel]
        | _ -> []
      and opp_del_monotone bodylst = match bodylst with
        | [] -> []
        | hd::rest -> (_1_opp_del_monotone hd) @ (opp_del_monotone rest)
      and _1_opp_del_monotone tm = match tm with
        | Rel (Deltainsert (rel, varlst)) -> [rel]
        | _ -> []

      and same_ins_monotone stt = match stt with
        | Rule (Deltainsert (rel, varlst), bodylst) -> _1_same_ins_monotone bodylst
        | _ -> ["dummy"]
      and _1_same_ins_monotone bodylst = match bodylst with
        | [] -> []
        | hd::rest -> (_2_same_ins_monotone hd) @ (_1_same_ins_monotone rest)
      and _2_same_ins_monotone tm = match tm with
        | Rel (Deltainsert (rel, varlst)) -> [rel]
        | _ -> []

      and same_del_monotone stt = match stt with
        | Rule (Deltadelete (rel, varlst), bodylst) -> _1_same_del_monotone bodylst
        | _ -> ["dummy"]
      and _1_same_del_monotone bodylst = match bodylst with
        | [] -> []
        | hd::rest -> (_2_same_del_monotone hd) @ (_1_same_del_monotone rest)
      and _2_same_del_monotone tm = match tm with
        | Rel (Deltadelete (rel, varlst)) -> [rel]
        | _ -> []
      in

    let result = _0_monotone prog_bwd in
    result
  in

  let init_lst = [] in

  let linear_const_lst = unique_element (init_lst
                              @ (no_pred prog_bwd evolved_pred_lst))
                              @ (unique_element @@ atmost_one prog_bwd evolved_pred_lst)
                              @ (unique_element @@ monotone prog_bwd)
  in

  let prep_check_lst = linear_const_lst in

prep_check_lst
;;
