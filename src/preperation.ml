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
(* not care +/- or (+)/(-) to generate PK constraint rule *)
let constraint2rule prog =

    let rec to_rule prog = match prog with
      | Prog stt_lst -> _1_to_rule stt_lst
      and _1_to_rule sttl_lst = match sttl_lst with
        | [] -> []
        | hd::rest -> (_2_to_rule hd) @ (_1_to_rule rest)
      and _2_to_rule hd = match hd with
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

    let updated_stt_lst = to_rule prog  in

    Prog(updated_stt_lst)
;;

(* -- having rule to check +/- in backward then apply _|_ :- +t1(X,Y), t1(X,Y1), not Y=Y1.
   -- but not care about (+)/(-)
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

        printf "bwd_ins_lst1 => [";
        let print_el s = printf "%s; " s in
        List.iter print_el bwd_ins_lst;
        printf "]\n";

    let updated_stt_lst = to_rule prog bwd_ins_lst in

    Prog(updated_stt_lst)
;;
*)

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
        printf "]\n"
      end
      else
        ();

pk_lst
;;

(* get pk list *)
let get_pk_pred_var prog log =

    let rec get sttl = match sttl with
      | [] -> []
      | hd::rest -> (_1_get hd) @ (get rest)
      and _1_get stt = match stt with
        | Pk (relname, attrlst) -> [(relname, (make_var attrlst))]
        | _ -> []
    in

    let pk_lst = get (get_sttl prog) in

      if !log
      then begin
        printf "pk_lst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map fst pk_lst);
        printf "]\n"
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
  let source_pred_lst = unique_element @@ Utils.get_source_rterms prog in
      (* print *)
      if !log
      then begin
        printf "source_pred_lst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map string_of_rterm source_pred_lst);
        printf "]\n"
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

  let source_ins_rels = unique_element @@ get (get_sttl prog) source_rels in

      if !log
      then begin
        printf "source_ins_rels => [";
        let print_el s = printf "%s; " s in
        List.iter print_el source_ins_rels;
        printf "]\n"
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

  let source_del_rels = unique_element @@ get (get_sttl prog) source_rels in

      if !log
      then begin
        printf "source_del_rels => [";
        let print_el s = printf "%s; " s in
        List.iter print_el source_del_rels;
        printf "]\n"
      end
      else
        ();

source_del_rels
;;

(* --- get predicates (rterm) in target schema --------------------------------------- *)
let get_target_preds prog log =
  let target_pred_lst = unique_element @@ Utils.get_target_rterms prog in
      (* print *)
      if !log
      then begin
        printf "target_pred_lst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map string_of_rterm target_pred_lst);
        printf "]\n"
      end
      else
        ();

target_pred_lst
;;

(* --- get predicates (rterm) of head relations --------------------------------------- *)
let get_head_preds prog log =
  let rule_lst = Expr.get_rule_stts prog in
  let head_pred_lst = unique_element @@ Utils.get_rulehead_rterms prog in
      (* print *)
      if !log
      then begin
        printf "head_pred_lst => [";
        let print_el s = printf "%s; " s in
        List.iter print_el (List.map string_of_rterm head_pred_lst);
        printf "]\n"
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
        printf "]\n";
      end
      else
        ();

unique_element @@ init_pred_lst
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
        printf "]\n";
      end
      else
        ();

unique_element @@ evolved_pred_lst
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
        printf "]\n";
      end
      else
        ();

unique_element @@ evolved_bwd_pred_lst
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
        printf "]\n";
      end
      else
        ();

  unique_element @@ case1_pred_lst
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
        print_endline "\n--- function: get_schemas ---";
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
      | Constraint (h, b) -> [Rule (h,b )]
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

(*
(* --- check a written strategy --------------------------------------- *)
let check prog_bwd evolved_pred_lst log =

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
                            (*  @ (unique_element @@ monotone prog_bwd) *)
  in

  let prep_check_lst = linear_const_lst in

prep_check_lst
;;
*)

(* --- check a written strategy --------------------------------------- *)
let check2 prog_bwd evolved_pred_lst source_rels log =

  (* check whether a rule of backward propagation for a relation of source schema *)
  let rec check_source bwd_sttl source_rels log = match bwd_sttl with
    | [] -> []
    | hd::rest -> (_1_check_source hd source_rels log)
                  @ (check_source rest source_rels log)

    and _1_check_source stt source_rels log = match stt with
      | Rule(head, bodylst) -> _2_check_source head source_rels stt log
      | _ -> invalid_arg "A function check_source is called without rules."

    and _2_check_source head source_rels stt log = match head with
      | Deltainsert (rel, _) ->
          if List.mem rel source_rels
            then []
            else ["Error: rule head is not in source schema: " ^ (string_of_stt stt)]
      | Deltadelete (rel, _) ->
          if List.mem rel source_rels
            then []
            else ["Error: rule head is not in source schema: " ^ (string_of_stt stt)]
      | _ -> []
  in

  (* check whether deleta relation in a rule body for relation of target schema *)
  let rec check_target bwd_sttl evolved_rel_lst log = match bwd_sttl with
    | [] -> []
    | hd::rest -> (_1_check_target hd evolved_rel_lst log)
                  @ (check_target rest evolved_rel_lst log)

    and _1_check_target stt evoloved_rel_lst log = match stt with
      | Rule( (Deltainsert _), bodylst ) -> _2_check_target bodylst evoloved_rel_lst stt log
      | Rule( (Deltadelete _), bodylst ) -> _2_check_target bodylst evoloved_rel_lst stt log
      | _ -> []

    and _2_check_target bodylst evolved_rel_lst stt log = match bodylst with
      | [] -> []
      | hd::rest -> (_3_check_target hd evolved_rel_lst stt log)
                    @ (_2_check_target rest evolved_rel_lst stt log)

    and _3_check_target hd evolved_rel_lst stt log = match hd with
      | Rel(Deltainsert (rel, varlst) ) ->
          if List.mem rel evolved_rel_lst
            then []
            else ["Error: A delta relation in body is not in target schema: " ^ (string_of_stt stt)]
      | Rel(Deltadelete (rel, varlst) ) ->
          if List.mem rel evolved_rel_lst
            then []
            else ["Error: A delta relation in body is not in target schema: " ^ (string_of_stt stt)]
      | Not(Deltainsert (rel, varlst) ) ->
          if List.mem rel evolved_rel_lst
            then []
            else ["Error: A delta relation in body is not in target schema: " ^ (string_of_stt stt)]
      | Not(Deltadelete (rel, varlst) ) ->
          if List.mem rel evolved_rel_lst
            then []
            else ["Error: A delta relation in body is not in target schema: " ^ (string_of_stt stt)]
      | _ -> []
  in

  (* check lineality predicate of +/- appears once *)
  let rec check_linear bwd_sttl log = match bwd_sttl with
    | [] -> []
    | hd::rest -> (_1_check_linear hd log)
                  @ (check_linear rest log)

    and _1_check_linear stt log = match stt with
      | Rule( (Deltainsert _), bodylst) ->
        let number_insdel = List.length (_2_check_linear bodylst log) in
        if number_insdel = 1
          then []
          else ["Error: deleta relation in rule body is not linear." ^ (string_of_stt stt)]
      | Rule( (Deltadelete _), bodylst) ->
        let number_insdel = List.length (_2_check_linear bodylst log) in
        if number_insdel = 1
          then []
          else ["Error: deleta relation in rule body is not linear." ^ (string_of_stt stt)]
      | _ -> []

    and _2_check_linear bodylst log = match bodylst with
      | [] -> []
      | hd::rest -> (_3_check_linear hd log) @ (_2_check_linear rest log)

    and _3_check_linear hd log = match hd with
      | Rel(Deltainsert _) -> [hd]
      | Rel(Deltadelete _) -> [hd]
      | _ -> []
  in

  (* --------------------------------------------------------
    check monotonicity
    (not allowed)
    +s1(X,Y) :- -t(X,Y), not s1(X,Y).

    allowed
    +s1(X,Y) :- +t(X,Y), not s1(X,Y).
    -s1(X,Y) :- -t(X,Y), not s1(X,Y).

    allowed (by two rules)
    -s1(X,Y) :- +t(X,Y), not s1(X,Y).
    +s1(X,Y) :- +t(X,Y), not s1(X,Y).
  ----------------------------------------------------------- *)
  let rec check_monotone bwd_sttl bwd_sttl2 log = match bwd_sttl with
    | [] -> []
    | hd::rest -> (_1_check_monotone hd bwd_sttl2 log)
                  @ (check_monotone rest bwd_sttl2 log)

    and _1_check_monotone stt bwd_sttl log = match stt with
      | Rule( Deltainsert (rel, varlst), bodylst) -> _2_check_monotone_ins stt rel bodylst
      | Rule( Deltadelete (rel, varlst), bodylst) -> _2_check_monotone_del stt rel varlst bodylst bwd_sttl
      | _ -> []

    (* When a rule head is delta insertion, check whether rule body does not have delta deletion *)
    and _2_check_monotone_ins stt rel bodylst = match bodylst with
      | [] -> []
      | hd::rest -> (_3_check_monotone_ins stt rel hd)
                    @ (_2_check_monotone_ins stt rel rest)

    and _3_check_monotone_ins stt rel tm = match tm with
      | Rel(Deltainsert _) -> []
      | Rel(Deltadelete _) -> ["Error: Not monotone:" ^ (string_of_stt stt)]
      | _ -> []

    (* When a rule head is delta deletion, check whether rule body has delta deletion. *)
    (* If rule body has delta insertion, check whether corresponding rule of delta insertion *)
    (* has delta insertion in its body. *)
    and _2_check_monotone_del stt rel varlst bodylst bwd_sttl = match bodylst with
      | [] -> []
      | hd::rest -> (_3_check_monotone_del stt rel varlst hd bwd_sttl)
                    @ (_2_check_monotone_del stt rel varlst rest bwd_sttl)

    and _3_check_monotone_del stt rel varlst tm bwd_sttl = match tm with
      | Rel(Deltainsert (del_rel, _)) ->
         (* derive corresponding rules which head is delta insertion *)
         let rule_ins = get_ins_rules rel varlst bwd_sttl in
          printf "rule_ins => \n"; print_sttlst rule_ins; printf "\n";

         if List.length rule_ins = 0
          then ["Error: Not monotone:" ^ (string_of_stt stt)]
          else begin
            let monotone_del = _4_check_monotone_del stt rule_ins del_rel in
                (*
                printf "del_rel = %s; " del_rel;
                printf "monotone_del => [";
                let e = printf "%s; " in
                List.iter e (List.map string_of_term monotone_del);
                printf "]\n";
                *)
            if List.length monotone_del <> 0
              then []
              else ["Error: Not monotone-kk:" ^ (string_of_stt stt)]
           end

  | Rel(Deltadelete _) -> []
      | _ -> []

    and _4_check_monotone_del stt rule_ins del_rel = match rule_ins with
      | [] -> []
      | hd::rest -> (_5_check_monotone_del stt hd del_rel)
                    @ (_4_check_monotone_del stt rest del_rel)

    and _5_check_monotone_del stt stt2 del_rel = match stt2 with
      | Rule ((Deltainsert _), bodylst ) -> _6_check_monotone_del bodylst del_rel
      | _ -> []

    and _6_check_monotone_del bodylst del_rel = match bodylst with
      | [] -> []
      | hd::rest -> (_7_check_monotone_del hd del_rel)
                    @ (_6_check_monotone_del rest del_rel)

    and _7_check_monotone_del tm del_rel = match tm with
      | Rel(Deltainsert (rel, _)) ->
          if (rel = del_rel)
            then [tm]
            else []
      | _ -> []

    (* derive corresponding rules which head is delta insertion *)
    and get_ins_rules rel varlst bwd_sttl = match bwd_sttl with
      | [] -> []
      | hd::rest -> (_1_get_ins_rules rel varlst hd)
                    @ (get_ins_rules rel varlst rest)

    and _1_get_ins_rules rel varlst stt = match stt with
      | Rule (Deltainsert (rel_ins, varlst_ins), bodylst) ->
          if (rel_ins = rel) && (varlst_ins = varlst)
            then [stt]
            else []
      | _ -> []
  in


  let evolved_rel_lst = get_rels evolved_pred_lst in
  let bwd_sttl = get_sttl prog_bwd in
  let init_lst = [] in
  let prep_check_lst =  unique_element (
                            init_lst
                            @ (check_source bwd_sttl source_rels log)
                            @ (check_target bwd_sttl evolved_rel_lst log)
                            @ (check_linear bwd_sttl log)
                            @ (check_monotone bwd_sttl bwd_sttl log)
                        ) in

prep_check_lst
;;

(* ---------------------------------------------------------------------
Goal: Retrive pairs of ins/del.
input:
  +s1(X,Y) :- +t1(X,Y), L1, L2.
  -s1(X,Y) :- -t1(X,Y), L1, L2.
  +s2(X,Y) :- +t2(X,Y), L1, L2.
  -s2(X,Y) :- -t2(X,Y), L1, L2.
  +s2(X,Y) :- +t2(X,Y), L1, L2.
  -s2(X,Y) :- -t2(X,Y), L1, L2.

output:
  [
    [+s1(X,Y) :- +t1(X,Y), L1, L2.; -s1(X,Y) :- -t1(X,Y), L1, L2.];
    [+s2(X,Y) :- +t2(X,Y), L1, L2.; -s2(X,Y) :- -t2(X,Y), L1, L2.];
    [+s2(X,Y) :- +t2(X,Y), L1, L2; -s2(X,Y) :- -t2(X,Y), L1, L2.];
  ]
-------------------------------------------------------------------- *)
let get_delta_pair ast_schemas ast_constraint ast_schevo ast_bwd evolved_bwd_pred_lst log =

  let rec get schema_sttl constraint_sttl ast_schevo bwd_sttl evolved_bwd_rel_lst = match evolved_bwd_rel_lst with
    | [] -> [[]]
    | hd::rest ->
        let target_rel = get_rel_from_pred hd in
        let schevo_lst = get_sttl (get_one_query ast_schevo hd) in
        let pair_lst = _1_get bwd_sttl target_rel in
        let pair_lst_source = unique_element @@ lst_source pair_lst bwd_sttl target_rel in
        let remaining_sttl = list_setminus bwd_sttl pair_lst_source in

        let pair_lst_source_rels = unique_element (get_pair_rels pair_lst_source) in
        let pair_schema_sttl = get_pair_schema schema_sttl target_rel pair_lst_source_rels in

        let pair_constraint_sttl = get_pair_constraint constraint_sttl pair_lst_source_rels in
          (*
          printf "pair_lst => [\n";
          print_sttlst pair_lst;
          printf "]\n\n";

          printf "pair_lst_source => [\n";
          print_sttlst pair_lst_source;
          printf "]\n\n";

          printf "remaining_stt => [\n";
          print_sttlst remaining_sttl;
          printf "]\n\n";

          printf "pair_lst_source_rels => [";
          let print_el s = printf "%s; " s in
          List.iter print_el pair_lst_source_rels;
          printf "]\n\n";
          *)

        let each_rule = pair_schema_sttl @ pair_constraint_sttl @ schevo_lst @ pair_lst_source in
          (*
          printf "each_rule => [\n";
          print_sttlst each_rule;
          printf "]\n\n";
          *)
        [each_rule] @ (get schema_sttl constraint_sttl ast_schevo remaining_sttl rest)


    (* list of rules which has +hd(X) or -hd(X) in body *)
    and _1_get bwd_sttl target_rel = match bwd_sttl with
      | [] -> []
      | hd::rest -> (_2_get hd target_rel) @ (_1_get rest target_rel)

    and _2_get stt target_rel = match stt with
      | Rule(Deltainsert (rel, varlst), bodylst) -> _3_get bodylst stt target_rel
      | Rule(Deltadelete (rek, varlst), bodylst) -> _3_get bodylst stt target_rel
      | _ -> []

    and _3_get bodylst stt target_rel = match bodylst with
      | [] -> []
      | hd::rest -> (_4_get hd stt target_rel) @ (_3_get rest stt target_rel)

    and _4_get tm stt target_rel = match tm with
      | Rel(Deltainsert(rel, varlst)) ->
         if rel = target_rel
          then [stt]
          else []
      | Rel (Deltadelete(rel, varlst)) ->
         if rel = target_rel
          then [stt]
          else []
      | _ -> []

    (* query of pair_lst *)
    and lst_source pair_lst bwd_sttl target_rel =
      let head_rel_lst = unique_element @@ get_rels_head (Prog(pair_lst)) in
      _1_lst_source pair_lst head_rel_lst bwd_sttl target_rel

    and _1_lst_source pair_lst head_rel_lst bwd_sttl target_rel = match head_rel_lst with
      | [] -> []
      | hd::rest -> (_2_lst_source pair_lst hd bwd_sttl target_rel)
                    @ (_1_lst_source pair_lst rest bwd_sttl target_rel)

    and _2_lst_source pair_lst source_rel bwd_sttl target_rel = match pair_lst with
      | [] -> []
      | hd::rest -> (_3_lst_source hd source_rel bwd_sttl target_rel)
                    @ (_2_lst_source rest source_rel bwd_sttl target_rel)

    and _3_lst_source stt source_rel bwd_sttl target_rel = match stt with
      | Rule (Deltainsert(rel, varlst), bodylst) ->
          if (rel = source_rel)
            then begin
              let result1 = get_sttl (get_one_query (Prog(bwd_sttl)) (Deltainsert(rel, varlst)) ) in
              let result = filter_query result1 result1 target_rel in
              (* printf "Rule (Deltainsert(rel, varlst), _) ->\n"; *)
              (* print_sttlst result; *)
              result
            end
            else []
      | Rule (Deltadelete(rel, varlst), bodylst) ->
          if (rel = source_rel)
            then begin
              let result1 = get_sttl (get_one_query (Prog(bwd_sttl)) (Deltadelete(rel, varlst)) ) in
              let result = filter_query result1 result1 target_rel in
              (* printf "Rule (Deltadelete(rel, varlst), _) ->\n"; *)
              (* print_sttlst result; *)
              result
            end
            else []
      | _ -> []

    and _4_lst_source tml = match tml with
      | [] -> []
      | hd::rest -> (_5_lst_source hd) @ (_4_lst_source rest)
      and _5_lst_source tm = match tm with
        | Rel(Deltainsert(rel, varlst)) -> [rel]
        | Rel(Deltadelete(rel, varlst)) -> [rel]
        | _ -> []

  and get_pair_rels pair_lst_source = match pair_lst_source with
    | [] -> []
    | hd::rest -> (_1_get_pair_rels hd) @ (get_pair_rels rest)

    and _1_get_pair_rels stt = match stt with
      | Rule (Pred(var, varlst), bodylst) -> [var] @ (_2_get_pair_rels bodylst)
      | Rule (Deltainsert(var, varlst), bodylst) -> [var] @ (_2_get_pair_rels bodylst)
      | Rule (Deltadelete(var, varlst), bodylst) -> [var] @ (_2_get_pair_rels bodylst)
      | _ -> []

    and _2_get_pair_rels bodylst = match bodylst with
      | [] -> []
      | hd::rest -> (_3_get_pair_rels hd) @ (_2_get_pair_rels rest)

    and _3_get_pair_rels tm = match tm with
      | Rel(Pred(rel, varlst))
      | Rel(Deltainsert(rel, varlst))
      | Rel(Deltadelete(rel, varlst))
      | Not(Pred(rel, varlst))
      | Not(Deltainsert(rel, varlst))
      | Not(Deltadelete(rel, varlst)) -> [rel]
      | _ -> []

  (* filter schema which has targe relations in delta relations in paried rules *)
  and get_pair_schema schema_sttl target_rel pair_lst_source_rels = match schema_sttl with
    | [] -> []
    | hd::rest -> (_1_get_pair_schema hd target_rel pair_lst_source_rels)
                  @ (get_pair_schema rest target_rel pair_lst_source_rels)
    and _1_get_pair_schema stt target_rel pair_lst_source_rels = match stt with
      | Target_schema (_, rel, varlst) ->
          if rel = target_rel
            then [View (rel, varlst)]
                  (* Source (("ins_" ^ rel), varlst);
                     Source (("del_" ^ rel), varlst) *)
            else [Source (rel, varlst)]
      | Source_schema (_, rel, varlst) ->
          if List.mem rel pair_lst_source_rels
            then [Source (rel, varlst)]
            else []
      | _ -> []

  (* filter constraint which has relations in paired rules *)
  and get_pair_constraint constraint_sttl pair_lst_source_rels = match constraint_sttl with
    | [] -> []
    | hd::rest -> (_1_get_pair_constraint hd pair_lst_source_rels)
                  @ (get_pair_constraint rest pair_lst_source_rels)

    and _1_get_pair_constraint stt pair_lst_source_rels = match stt with
      | Rule (get_empty_pred, bodylst) ->
          let rel_lst = _2_get_pair_constraint bodylst in
          if list_inclusion rel_lst pair_lst_source_rels
            then [stt]
            else []
      | _ -> []

    and _2_get_pair_constraint bodylst = match bodylst with
      | [] -> []
      | hd::rest -> (_3_get_pair_constraint hd) @ (_2_get_pair_constraint rest)

    and _3_get_pair_constraint tm = match tm with
      | Rel(Pred(rel, varlst))
      | Rel(Deltainsert(rel, varlst))
      | Rel(Deltadelete(rel, varlst))
      | Not(Pred(rel, varlst))
      | Not(Deltainsert(rel, varlst))
      | Not(Deltadelete(rel, varlst)) -> [rel]
      | _ -> []

    (* filter query which have delta relation of taget_rel *)
    and filter_query sttl1 sttl2 target_rel =
      let filtered_query = _1_filter_query sttl1 target_rel in
      let result = unique_element @@ query_filter_query filtered_query filtered_query in
          (*
          printf "filtered_query   => \n[\n";
          print_sttlst filtered_query ;
          printf "]\n\n";

          printf "result  => \n[\n";
          print_sttlst result;
          printf "]\n\n";
          *)
      result

      (* exclude rules which do not have target_rel of delta relaion in their body *)
      and _1_filter_query sttl1 target_rel = match sttl1 with
        | [] -> []
        | hd::rest -> (_2_filter_query hd target_rel) @ (_1_filter_query rest target_rel)
      and _2_filter_query stt target_rel = match stt with
        | Rule (Deltainsert _, bodylst) -> _3_filter_query stt bodylst target_rel
        | Rule (Deltadelete _, bodylst) -> _3_filter_query stt bodylst target_rel
        | _ -> [stt]
      and _3_filter_query stt body_lst target_rel =
        let deltarel_lst = _4_filter_query body_lst in
        if List.mem target_rel deltarel_lst
          then [stt]
          else []
      and _4_filter_query body_lst = match body_lst with
        | [] -> []
        | hd::rest -> (_5_filter_query hd) @ (_4_filter_query rest)
      and _5_filter_query tm = match tm with
        | Rel(Deltainsert(rel, varlst))
        | Rel(Deltadelete(rel, varlst)) -> [rel]
        | _ -> []

      and query_filter_query sttl1 sttl2 = match sttl1 with
        | [] -> []
        | hd::rest -> (_1_query_filter_query hd sttl2) @ (query_filter_query rest sttl2)
      and _1_query_filter_query stt sttl2 = match stt with
        | Rule (Deltainsert (rel, varlst), bodylst) ->
              get_sttl (get_one_query (Prog(sttl2)) (Deltainsert(rel, varlst)) )
        | Rule (Deltadelete (rel, varlst), bodylst) ->
              get_sttl (get_one_query (Prog(sttl2)) (Deltadelete(rel, varlst)) )
        | _ -> []
  in


  let sttl_delta_pair1 = get (get_sttl ast_schemas) (get_sttl ast_constraint) ast_schevo (get_sttl ast_bwd) evolved_bwd_pred_lst in
  let sttl_delta_pair = list_setminus sttl_delta_pair1 [[]] in

        if !log
        then begin
          printf "sttl_delta_pair => \n[\n";
          let e s =
              printf "[";
              print_sttlst s;
              printf "];\n"
          in
          List.iter e sttl_delta_pair;
          printf "]\n\n";
        end
        else
          ();

sttl_delta_pair
;;

(* --------------------------------------------------*)
(* preperation for disjoitness check                 *)
(* input: stt list of paired delta rules             *)
(* output: stt list paired delta rules to be checked *)
(* --------------------------------------------------*)
let prep_disjoint sttl_delta log =

  let rec filter sttl_delta log = match sttl_delta with
    | [] -> [[]]
    | hd::rest -> [unique_element @@ _1_filter hd log] @ (filter rest log)

  and _1_filter sttl log =
    let paired_rules = _2_filter sttl sttl log in
    if List.length paired_rules = 0
      then []
      else begin
          (*
          printf "paired_rules => \n[\n";
          print_sttlst paired_rules;
          printf "]\n\n";
          *)
        paired_rules
      end

  (* For a rule of -s in head and +t in body, find a paired rule of +s in head and +t in body *)
  and _2_filter sttl1 sttl2 log = match sttl1 with
    | [] -> []
    | hd::rest -> (_3_filter hd sttl2 log) @ (_2_filter rest sttl2 log)

  and _3_filter stt sttl2 log = match stt with
    | Rule (Deltainsert(rel, varlst), bodylst) -> []
    | Rule (Deltadelete(rel, varlst), bodylst) ->
        let ins_rels = get_ins_rel bodylst in

        (*
        printf "ins_rels => [";
        let e = printf "%s; " in
        List.iter e ins_rels;
        printf "]\n\n";
        *)

        if List.length ins_rels = 0
          then []
          else begin
            let ins_rel = List.hd ins_rels in
            let ins_rule = _4_filter sttl2 ins_rel in

            let paired_sttl = ins_rule @ [stt] in
            let paired_sttl_query = unique_element @@ make_query paired_sttl sttl2 in
            let filter_paired_sttl_query = filter_insrel ins_rel paired_sttl_query in
                (*
                printf "paired_sttl => \n[\n";
                print_sttlst paired_sttl;
                printf "]\n\n";

                printf "paired_sttl_query  => \n[\n";
                print_sttlst paired_sttl_query;
                printf "]\n\n";

                printf "filter_paired_sttl_query  => \n[\n";
                print_sttlst filter_paired_sttl_query;
                printf "]\n\n";
                *)

            let e = change2ins ins_rel in
            let paired_sttl_query_ins = List.map e filter_paired_sttl_query in
            let tmp_log = ref false in
            let schema_sttl = get_sttl @@ get_schemas (Prog(sttl2)) tmp_log in
            let ins_schema = schema2ins schema_sttl in
            let constraint_sttl = get_sttl @@ get_constraints (Prog(sttl2)) tmp_log in
            let ins_constraint = const2ins constraint_sttl in

            ins_schema @ ins_constraint @ paired_sttl_query_ins
          end
    | _ -> []

  and _4_filter sttl2 ins_rel = match sttl2 with
    | [] -> []
    | hd::rest -> (_5_filter hd ins_rel) @ (_4_filter rest ins_rel)

  and _5_filter stt ins_rel = match stt with
    | Rule ((Deltainsert _), bodylst) ->
      let body_rels = get_rels_body_tml bodylst in
      if List.mem ins_rel body_rels
        then begin
          [stt]
        end
        else []
    | _ -> []

  (* retrieve delta insertion from bodylst *)
  and get_ins_rel bodylst = match bodylst with
    | [] -> []
    | hd::rest -> (_1_get_ins_rel hd) @ (get_ins_rel rest)
  and _1_get_ins_rel tm = match tm with
    | Rel (Deltainsert(rel, varlst)) -> [rel]
    | _ -> []

  (* change +rel to ins_rel in body *)
  and change2ins ins_rel stt = match stt with
    | Rule (rt, bodylst) ->
        let new_bodylst = _1_change2ins ins_rel bodylst  in
        Rule(rt, new_bodylst)
    | _ -> stt

  and _1_change2ins ins_rel bodylst = match bodylst with
    | [] -> []
    | hd::rest -> (_2_change2ins ins_rel hd)
                  @ (_1_change2ins ins_rel rest)

  and _2_change2ins ins_rel tm = match tm with
    | Rel(Deltainsert(rel, varlst)) ->
        if rel = ins_rel
        then [Rel(Pred( ("ins_" ^ rel), varlst))]
        else [tm]
    | _ -> [tm]

  and make_query paired_sttl sttl = match paired_sttl with
    | [] -> []
    | hd::rest -> (_1_make_query hd sttl) @ (make_query rest sttl)

  and _1_make_query stt sttl = match stt with
    | Rule (Deltainsert(rel, varlst), bodylst) ->
        (*
        let result = get_sttl @@ get_one_query (Prog(sttl)) (Deltainsert(rel, varlst)) in
        printf "stt = %s\n" (string_of_stt stt);
        printf "query_result = \n"; print_sttlst result; printf "\n";
        result
        *)
        get_sttl @@ get_one_query (Prog(sttl)) (Deltainsert(rel, varlst))
    | Rule (Deltadelete(rel, varlst), bodylst) ->
        (*
        let result = get_sttl @@ get_one_query (Prog(sttl)) (Deltadelete(rel, varlst)) in
        printf "stt = %s\n" (string_of_stt stt);
        printf "query_result = \n"; print_sttlst result; printf "\n";
        result
        *)
        get_sttl @@ get_one_query (Prog(sttl)) (Deltadelete(rel, varlst))
    | _ -> []

  and filter_insrel ins_rel sttl = match sttl with
    | [] -> []
    | hd::rest -> (_1_filter_insrel ins_rel hd) @ (filter_insrel ins_rel rest)

    and _1_filter_insrel ins_rel stt = match stt with
      | Rule( (Deltainsert _), bodylst) ->
          let body_check = _2_filter_insrel ins_rel bodylst in
          if List.length body_check = 0
            then []
            else [stt]
      | Rule( (Deltadelete _), bodylst) ->
          let body_check = _2_filter_insrel ins_rel bodylst in
          if List.length body_check = 0
            then []
            else [stt]

      | _ -> [stt]
    and _2_filter_insrel ins_rel bodylst = match bodylst with
      | [] -> []
      | hd::rest -> (_3_filter_insrel ins_rel hd) @ (_2_filter_insrel ins_rel rest)
    and _3_filter_insrel ins_rel tm = match tm with
      | Rel (Deltainsert (rel, varlst)) ->
          if rel = ins_rel
            then [tm]
            else []
      | Rel (Deltadelete (rel, varlst)) -> []
      | _ -> []

  and schema2ins schema_sttl = match schema_sttl with
    | [] -> []
    | hd::rest -> (_1_schema2ins hd) @ (schema2ins rest)
    and _1_schema2ins stt = match stt with
      | View (rel, varlst)
          -> [View (("ins_" ^ rel), varlst); Source(rel, varlst)]
      | _ -> [stt]

  and const2ins constraint_sttl = match constraint_sttl with
    | [] -> []
    | hd::rest -> (_1_const2ins hd) @ (const2ins rest)
    and _1_const2ins stt = match stt with
      | Rule (get_empty_pred, bodylst) ->
        let ins_bodylst = _2_const2ins bodylst in
        [Rule (get_empty_pred, ins_bodylst)]
      | _ -> []
    and _2_const2ins bodylst = match bodylst with
      | [] -> []
      | hd::rest -> (_3_const2ins hd) @ (_2_const2ins rest)
    and _3_const2ins tm = match tm with
      | Rel (Deltainsert(rel, varlst)) -> [Rel (Pred( ("ins_" ^ rel), varlst))]
      | Rel (Deltadelete(rel, varlst)) -> [Rel (Pred( ("del_" ^ rel), varlst))]
      | Not (Deltainsert(rel, varlst)) -> [Not (Pred( ("ins_" ^ rel), varlst))]
      | Not (Deltadelete(rel, varlst)) -> [Not (Pred( ("del_" ^ rel), varlst))]
      | _ -> [tm]
  in

  let filtered_pair_sttl = list_setminus (filter sttl_delta log) [[]] in
        if !log
        then begin
          printf "filtered_pair_sttl => \n[\n";
          let e s =
              printf "[";
              print_sttlst s;
              printf "];\n"
          in
          List.iter e filtered_pair_sttl;
          printf "]\n\n";
        end
        else
          ();

  let prep_dijoint_lst = filtered_pair_sttl in

prep_dijoint_lst
;;

(* --------------------------------------------------*)
(* get delta predicate                               *)
(* input: [s1(X,Y); s2(X,Z)]                         *)
(* output:[+s1(X,Y); -s1(X,Y); +s2(X,Z); -s2(X,Z)]   *)
(*         (+)s1(X,Y); (-)s1(X,Y); (+)s2(X,Z); (-)s2(X,Z)]   *)
(* --------------------------------------------------*)
let get_delta pred_lst =

  let rec get pred_lst = match pred_lst with
    | [] -> []
    | hd::rest -> (_1_get hd) @ (get rest)

    and _1_get rt = match rt with
      | Pred(rel, varlst)
          -> [Deltainsert(rel, varlst); Deltadelete(rel, varlst);
              Deltainsert_nos(rel, varlst); Deltadelete_nos(rel, varlst)]
      | _ -> []
  in

  let delta_pred = get pred_lst in
delta_pred
;;

(* --------------------------------------------------*)
(* get delta rule                                    *)
(* input: [+s1(X,Y,Z) :- +t1(X,Y,Z), not s1(X,Y,Z).] *)
(*        t1                                         *)
(* output:[+s1(X,Y,Z) :- +t1(X,Y,Z), not s1(X,Y,Z).] *)
(* --------------------------------------------------*)
let get_target_delta_rules ast target_rel =

  let rec get sttl target_rel = match sttl with
    | [] -> []
    | hd::rest -> (_1_get hd target_rel) @ (get rest target_rel)

    and _1_get hd target_rel = match hd with
      | Rule (rt, tml) ->
          let delta_rels_tml = get_delta_rels_body (Prog([hd])) in
          if List.mem target_rel delta_rels_tml
            then [hd]
            else []
      | _ -> invalid_arg "A function get_target_delta_rules is called without rules"
  in

  let rules_target_rel = unique_element @@ get (get_sttl ast) target_rel in
rules_target_rel
;;

(* --------------------------------------------------*)
(* get backwarrd rules                               *)
(* input:  ast, list of delta rels                   *)
(* output: ast of backward rules                     *)
(* --------------------------------------------------*)
let get_backward_rules ast delta_pred_lst =

  let rec get sttl ast delta_pred_lst = match sttl with
    | [] -> []
    | hd::rest -> (_1_get hd ast delta_pred_lst) @ (get rest ast delta_pred_lst)

    and _1_get stt ast delta_pred_lst = match stt with
      | Rule (rt, tml) ->
        if List.mem rt delta_pred_lst
          then begin
            get_sttl @@ get_one_query ast rt
            end
          else []
      | _ -> []

  in

  let ast_backward = Prog (unique_element @@ get (get_sttl ast) ast delta_pred_lst) in
ast_backward
;;

(* --------------------------------------------------*)
(* get schema for twin                               *)
(* input:  ast of schema definition, source_rels, target_rels *)
(* output: ast of twtin                              *)
(* --------------------------------------------------*)
let get_schema_twin ast source_rels target_rel =

  let rec get sttl source_rels target_rels = match sttl with
    | [] -> []
    | hd::rest -> (_1_get hd source_rels target_rel) @ (get rest source_rels target_rel)

    and _1_get stt source_rels target_rel = match stt with
      | Source_schema (schema, rel, varlst) ->
          if List.mem rel source_rels
            then [stt]
            else []
      | Target_schema (schema, rel, varlst) ->
          if rel = target_rel
            then [stt]
            else []
      | _ -> []
  in

  let ast_schema = Prog (get (get_sttl ast) source_rels target_rel) in
ast_schema
;;

(* get mapping of varname and stype
  Input: source ver1#s1('X':string, 'Y':int).
  Output: [(X, sting), (Y, int)]
*)
let get_var_stype ast =

  let rec gen sttl = match sttl with
    | [] -> []
    | hd::rest -> (_1_gen hd) @ (gen rest)
  and _1_gen hd = match hd with
    | Source_schema (schema, rel, varlst)
    | Target_schema (schema, rel, varlst) -> varlst
    | _ -> []
  in

  let result = unique_element @@ gen (get_sttl ast) in
result
;;
