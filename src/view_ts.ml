(* @author: Jumpei Tanaka *)
(* target-side database instance *)
  (* **************************************************************** *)
  (* Step 3: Source schema                                            *)
  (* **************************************************************** *)

(* ================= example of co-existence strategy  =================
% Schema evolution
t(X,Y,Z) :- s1(X,Y,Z,W).

% backward update sharing
+s1(X,Y,Z,W) :- +t(X,Y,Z), not s1(X,Y,Z,_), Y<100, W=''.
-s1(X,Y,Z,W) :- -t(X,Y,Z), s1(X,Y,Z,W), Y<100.

% PK constraint
pk(t,['X']).
pk(s1,['X']).

% constraint
_|_ :- s1(X,Y,Z,W), Y<=0.
_|_ :- t(X,Y,Z), Y<=0.
============================================================== *)


open Expr;;
open Utils;;
open Tools;;
open View_common;;
open Printf;;


(* Derive vars of auxc for each S of source schema *)
let get_auxc_varlst pk_lst_var target_rel target_vars init_pred_lst =

  (* derive varlst from pk lst *)
  let rec get_pk_varl pk_lst_notar rel = match pk_lst_notar with
    | [] -> []
    | hd::rest -> (_1_get_pk_varl hd rel) @ (get_pk_varl rest rel)
    and _1_get_pk_varl hd rel =
      if rel = (fst hd)
        then snd hd
        else []
  in

  let rec gen_tar pk_lst_var target_rel = match pk_lst_var with
    | [] -> []
    | hd::rest -> (_1_gen_tar hd target_rel) @ (gen_tar rest target_rel)
    and _1_gen_tar hd target_rel =
      let target_pk =
        if target_rel = (fst hd)
          then
            [hd]
          else []
      in
      target_pk
  in

  let rec gen init_pred_lst target_rel target_vars pk_tar pk_lst_var  =
      if List.length pk_tar = 0
        then
          _a_gen init_pred_lst target_rel target_vars pk_tar pk_lst_var
        else
          _0_gen init_pred_lst target_rel target_vars pk_tar pk_lst_var

    and _a_gen init_pred_lst target_rel target_vars pk_tar pk_lst_var = match init_pred_lst with
      | [] -> []
      | hd::rest -> (_b_gen hd target_rel target_vars pk_tar pk_lst_var)
                  @ (_a_gen rest target_rel target_vars pk_tar pk_lst_var)
    and _b_gen src_pred target_rel target_vars pk_tar pk_lst_var =
          let src_rel = get_rel_from_pred src_pred in
          let src_varsl = get_varlst_from_pred src_pred in
          let common = list_conjunction src_varsl target_vars in
          let diff = list_setminus src_varsl target_vars in
          [(src_rel, (common @ diff))]

    and _0_gen init_pred_lst target_rel target_vars pk_tar pk_lst_var = match init_pred_lst with
      | [] -> []
      | hd::rest -> (_1_gen hd target_rel target_vars pk_tar pk_lst_var)
                  @ (_0_gen rest target_rel target_vars pk_tar pk_lst_var)
    and _1_gen src_pred target_rel target_vars pk_tar pk_lst_var =
      let src_rel = get_rel_from_pred src_pred in
      let src_varsl = get_varlst_from_pred src_pred in
      let pk_tar_varl = get_pk_varl pk_lst_var target_rel in
      let pk_src_varl = get_pk_varl pk_lst_var src_rel in
      let common = list_conjunction src_varsl target_vars in
      let diff = list_setminus src_varsl target_vars in

           printf "target_varsl=> [";
           printf "%s, " target_rel;
           let print_el s = printf "%s, " s in
           List.iter print_el (List.map string_of_var target_vars);
           printf "]\n";

           printf "src_varsl=> [";
           printf "%s, " src_rel;
           let print_el s = printf "%s, " s in
           List.iter print_el (List.map string_of_var src_varsl);
           printf "]\n";

           printf "pk_tar_varsl=> [";
           printf "%s, " target_rel;
           let print_el s = printf "%s, " s in
           List.iter print_el (List.map string_of_var pk_tar_varl);
           printf "]\n";

           printf "pk_src_varsl=> [";
           printf "%s, " src_rel;
           let print_el s = printf "%s; " s in
           List.iter print_el (List.map string_of_var pk_src_varl);
           printf "]\n";

           printf "common_varsl=> [";
           printf "common, ";
           let print_el s = printf "%s, " s in
           List.iter print_el (List.map string_of_var common);
           printf "]\n";

           printf "diff_varsl=> [";
           printf "diff, ";
           let print_el s = printf "%s, " s in
           List.iter print_el (List.map string_of_var diff);
           printf "]\n";

      if (List.length pk_tar_varl <> 0) && (List.length pk_src_varl <> 0)
        then begin
          if (list_inclusion pk_tar_varl pk_src_varl) && (list_inclusion pk_src_varl pk_tar_varl)
            then begin
              printf "(pk_rel, (pk_src_varl @ diff))\n\n";
              [(src_rel, (pk_src_varl @ diff) )]
            end
            else begin
              printf "(src_rel, (common @ diff))\n\n";
              [(src_rel, (common @ diff) )]
            end
        end
        else begin
          printf "(src_rel, (common @ diff))\n\n";
          [(src_rel, (common @ diff) )]
        end
      in

  let pk_tar = gen_tar pk_lst_var target_rel in

  let result = gen init_pred_lst target_rel target_vars pk_tar pk_lst_var in

result
;;

(* Derive key of auxc for each S of source schema *)
let get_auxc_keylst pk_lst_var target_rel target_vars init_pred_lst =

  (* derive varlst from pk lst *)
  let rec get_pk_varl pk_lst_notar rel = match pk_lst_notar with
    | [] -> []
    | hd::rest -> (_1_get_pk_varl hd rel) @ (get_pk_varl rest rel)
    and _1_get_pk_varl hd rel =
      if rel = (fst hd)
        then snd hd
        else []
  in

  let rec gen_tar pk_lst_var target_rel = match pk_lst_var with
    | [] -> []
    | hd::rest -> (_1_gen_tar hd target_rel) @ (gen_tar rest target_rel)
    and _1_gen_tar hd target_rel =
      let target_pk =
        if target_rel = (fst hd)
          then
            [hd]
          else []
      in
      target_pk
  in

  let rec gen init_pred_lst target_rel target_vars pk_tar pk_lst_var  =
      if List.length pk_tar = 0
        then
          _a_gen init_pred_lst target_rel target_vars pk_tar pk_lst_var
        else
          _0_gen init_pred_lst target_rel target_vars pk_tar pk_lst_var

    and _a_gen init_pred_lst target_rel target_vars pk_tar pk_lst_var = match init_pred_lst with
      | [] -> []
      | hd::rest -> (_b_gen hd target_rel target_vars pk_tar pk_lst_var)
                  @ (_a_gen rest target_rel target_vars pk_tar pk_lst_var)
    and _b_gen src_pred target_rel target_vars pk_tar pk_lst_var =
          let src_rel = get_rel_from_pred src_pred in
          let src_varsl = get_varlst_from_pred src_pred in
          let common = list_conjunction src_varsl target_vars in
          let diff = list_setminus src_varsl target_vars in
          [(src_rel, (common @ diff))]

    and _0_gen init_pred_lst target_rel target_vars pk_tar pk_lst_var = match init_pred_lst with
      | [] -> []
      | hd::rest -> (_1_gen hd target_rel target_vars pk_tar pk_lst_var)
                  @ (_0_gen rest target_rel target_vars pk_tar pk_lst_var)
    and _1_gen src_pred target_rel target_vars pk_tar pk_lst_var =
      let src_rel = get_rel_from_pred src_pred in
      let src_varsl = get_varlst_from_pred src_pred in
      let pk_tar_varl = get_pk_varl pk_lst_var target_rel in
      let pk_src_varl = get_pk_varl pk_lst_var src_rel in
      let common = list_conjunction src_varsl target_vars in
      let diff = list_setminus src_varsl target_vars in

           printf "target_varsl=> [";
           printf "%s, " target_rel;
           let print_el s = printf "%s, " s in
           List.iter print_el (List.map string_of_var target_vars);
           printf "]\n";

           printf "src_varsl=> [";
           printf "%s, " src_rel;
           let print_el s = printf "%s, " s in
           List.iter print_el (List.map string_of_var src_varsl);
           printf "]\n";

           printf "pk_tar_varsl=> [";
           printf "%s, " target_rel;
           let print_el s = printf "%s, " s in
           List.iter print_el (List.map string_of_var pk_tar_varl);
           printf "]\n";

           printf "pk_src_varsl=> [";
           printf "%s, " src_rel;
           let print_el s = printf "%s; " s in
           List.iter print_el (List.map string_of_var pk_src_varl);
           printf "]\n";

           printf "common_varsl=> [";
           printf "common, ";
           let print_el s = printf "%s, " s in
           List.iter print_el (List.map string_of_var common);
           printf "]\n";

           printf "diff_varsl=> [";
           printf "diff, ";
           let print_el s = printf "%s, " s in
           List.iter print_el (List.map string_of_var diff);
           printf "]\n";

      if (List.length pk_tar_varl <> 0) && (List.length pk_src_varl <> 0)
        then begin
          if (list_inclusion pk_tar_varl pk_src_varl) && (list_inclusion pk_src_varl pk_tar_varl)
            then begin
              printf "(pk_rel, (pk_src_varl))\n\n";
              [(src_rel, (pk_src_varl) )]
            end
            else begin
              printf "(src_rel, (common))\n\n";
              [(src_rel, (common) )]
            end
        end
        else begin
          printf "(src_rel, (common))\n\n";
          [(src_rel, (common) )]
        end
      in

  let pk_tar = gen_tar pk_lst_var target_rel in

  let result = gen init_pred_lst target_rel target_vars pk_tar pk_lst_var in

result
;;

(* derive varlst of auxc *)
let get_auxc_var rel auxc_varlst =

  let rec gen rel auxc_varlst = match auxc_varlst with
    | [] -> []
    | hd::rest -> (_1_gen rel hd) @ (gen rel rest)
  and _1_gen rel hd =
    let aux_rel = fst hd in
    let aux_varlst = snd hd in
    if rel = aux_rel
      then aux_varlst
      else []
  in

  let result = gen rel auxc_varlst in
result
;;

(* derive varlst-stype of auxc *)
let get_auxc_var_stype rel auxc_varlst var_stype =

  let rec make aux_varl var_stype = match aux_varl with
    | [] -> []
    | hd::rest -> (_1_make hd var_stype) @ (make rest var_stype)
    and _1_make hd var_stype = match hd with
      | NamedVar(var) -> _2_make var var_stype
      | _ -> []
    and _2_make var var_stype = match var_stype with
      | [] ->  []
      | hd::rest -> (_3_make var hd) @ (_2_make var rest)
    and _3_make var hd =
      if var = (fst hd)
        then [(var,(snd hd))]
        else []
  in

  let rec gen rel auxc_varlst = match auxc_varlst with
    | [] -> []
    | hd::rest -> (_1_gen rel hd) @ (gen rel rest)
  and _1_gen rel hd =
    let aux_rel = fst hd in
    let aux_varl = snd hd in
    if rel = aux_rel
      then make aux_varl var_stype
      else []
  in

  let result = gen rel auxc_varlst in
result
;;



(*********************************************
  In: AST of schema, pred_list, target_rel_1
  Out: AST of BIRDS program for schema
*********************************************)
let generate_ts_schema ast_schemas pred target_rel_1 target_vartyes_1 auxc_varlst var_stype =

  let rec gen sttl pred target_rel_1 target_vartyes_1 auxc_varlst var_stype = match sttl with
    | [] -> []
    | hd::rest -> (_1_gen hd pred target_rel_1 target_vartyes_1 auxc_varlst var_stype)
                  @ (gen rest pred target_rel_1 target_vartyes_1 auxc_varlst var_stype)

  and _1_gen stt pred target_rel_1 target_vartyes_1 auxc_varlst var_stype = match stt with
    | Source_schema  (_, rel, varlst) ->
        let rel_pred = get_rterm_predname pred in
            if rel = rel_pred
            then
              [View (rel, varlst);                               (* S: view *)
               Source ("b_" ^ target_rel_1, target_vartyes_1);   (* Tb: base relation *)
               Source ( (get_aux_lost rel), varlst);     (* Alost_s *)
               Source ( (get_aux_gain rel), varlst);     (* Again_s *)
               Source ( (get_aux_c rel), (get_auxc_var_stype rel auxc_varlst var_stype ));  (* Ac_s *)
               Source ( (get_aux_lost target_rel_1), target_vartyes_1);     (* Alost_t *)
               Source ( (get_aux_gain target_rel_1), target_vartyes_1)    (* Again_t *)
              ]
            else
              [
               Source ( (get_aux_lost rel), varlst);     (* Alost_s *)
               Source ( (get_aux_gain rel), varlst);     (* Again_s *)
               Source ( (get_aux_c rel), (get_auxc_var_stype rel auxc_varlst var_stype ))   (* Ac_s *)
              ]
    | _ -> []
  in

  let result = gen (get_sttl ast_schemas) pred target_rel_1 target_vartyes_1 auxc_varlst var_stype in
result
;;

(* **************************************************************
  Generate get_t_src
 (example)
  s1(X,Y,Z,W) :- s1_0(X,Y,Z,W).
************************************************************** *)
let generate_get_t_src  pred  =

  let src_rel = get_rel_from_pred pred in
  let src_vars = get_varlst_from_pred pred in
  let get_t_src = [
      Rule(Pred(src_rel, src_vars) , [Rel(Pred(src_rel ^ "_0", src_vars))])
  ]
 in

get_t_src
;;


(* **************************************************************
  Generate get_t_src0
 (example)
  s1_0(X,Y,Z,W) :- s1_evo(X,Y,Z,W), not again_s1(X,Y,Z,W).
  s1_0(X,Y,Z,W) :- alost_s1(X,Y,Z,W).
  s1_evo (X,Y,Z,W) :- b_t(X,Y,Z), ac_s1(X,W).
************************************************************** *)
let generate_get_t_src0  init_pred_lst target_rel target_vars auxc_varlst =

  let rec gen init_pred_lst target_rel target_vars auxc_varlst = match init_pred_lst with
    | [] -> []
    | hd::rest -> (_1_gen hd target_rel target_vars auxc_varlst)
                  @ (gen rest target_rel target_vars auxc_varlst)

    and _1_gen pred target_rel target_vars auxc_varlst =
      let src_rel = get_rel_from_pred pred in
      let src_vars = get_varlst_from_pred pred in

      let get_t_src_i = [
        Rule(Pred(src_rel ^ "_0", src_vars), [Rel(Pred(src_rel ^ "_evo", src_vars));
                                              Not(Pred("a_gain_" ^ src_rel, src_vars))] );

        Rule(Pred(src_rel ^ "_0", src_vars), [Rel(Pred("a_lost_" ^ src_rel, src_vars))] );

        Rule(Pred(src_rel ^ "_evo", src_vars), [Rel(Pred("b_" ^ target_rel, target_vars));
                                                Rel(Pred("a_c_" ^ src_rel, (get_auxc_var src_rel auxc_varlst) ))] )
      ]
      in
      get_t_src_i
  in

  let get_t_src0 = gen init_pred_lst target_rel target_vars auxc_varlst in

get_t_src0
;;

(* **************************************************************
 Generate put_rt0
 (example)
 Input: t(X,Y,Z) :- s1(X,Y,Z,W).
 Output: t_0(X,Y,Z) :- s1_0(X,Y,Z,W).
************************************************************** *)

let generate_pre_schevo ast_schevo_1 ast_schevo_1 init_rel_lst target_rel  =


  let rec gen sttl init_rel_lst target_rel = match  sttl with
    | [] -> []
    | hd::rest -> (_1_gen hd init_rel_lst target_rel)
                  @ (gen rest init_rel_lst target_rel)
    and _1_gen  hd init_rel_lst target_rel  = match hd with
      | Rule (Pred(hrel, hvarlst), tl) ->
        if hrel = target_rel
          then begin
            let new_hrel = hrel ^ "_0" in
            let new_tl = _2_gen tl init_rel_lst in
            [Rule (Pred(new_hrel, hvarlst), new_tl)]
          end
          else begin
            let new_tl = _2_gen tl init_rel_lst in
            [Rule (Pred(hrel, hvarlst), new_tl)]
          end
      | _ -> []

    and _2_gen tl init_rel_lst = match tl with
      | [] -> []
      | hd::rest -> (_3_gen hd init_rel_lst) @ (_2_gen rest init_rel_lst)
    and _3_gen tm init_rel_lst = match tm with
      | Rel(Pred(rel, varlst)) ->
          if List.mem rel init_rel_lst
            then [Rel(Pred(rel ^ "_0", varlst)) ]
            else [tm]
      | Not(Pred(rel, varlst)) ->
          if List.mem rel init_rel_lst
            then [Not(Pred(rel ^ "_0", varlst)) ]
            else [tm]
      | _ ->[tm]
  in

  let put_rt = gen (get_sttl ast_schevo_1) init_rel_lst target_rel  in

put_rt
;;

(* **************************************************************
 Generate put_rt0
 (example)
 Input: t(X,Y,Z) :- s1(X,Y,Z,W).
 Output: t(X,Y,Z) :- s1(X,Y,Z,W).
         replace s2_0 if exist.
************************************************************** *)
let generate_put_rt sttl_schevo pred init_rel_lst =

  let rec gen sttl src_rel src_vars init_rel_lst = match sttl with
    | [] -> []
    | hd::rest -> (_1_gen hd src_rel src_vars init_rel_lst)
                   @ (gen rest src_rel src_vars init_rel_lst)

    and _1_gen stt src_rel src_vars init_rel_lst = match stt with
      | Rule (head, body) -> [Rule (head, (_2_gen body src_rel src_vars init_rel_lst))]
      | _ -> []

    and _2_gen body src_rel src_vars init_rel_lst = match body with
      | [] -> []
      | hd::rest -> (_3_gen hd src_rel src_vars init_rel_lst)
                     @ (_2_gen rest src_rel src_vars init_rel_lst)

    and _3_gen hd src_rel src_vars init_rel_lst = match hd with
      | Rel(Pred(rel, vars)) ->
        if (List.mem rel init_rel_lst) && (rel <> src_rel)
          then [Rel(Pred(rel ^ "_0", vars))]
          else [hd]
      | Not(Pred(rel, vars)) ->
        if (List.mem rel init_rel_lst) && (rel <> src_rel)
          then [Not(Pred(rel ^ "_0", vars))]
          else [hd]
      | _ -> [hd]

  in

  let src_rel = get_rel_from_pred pred in
  let src_vars = get_varlst_from_pred pred in

  let put_rt = gen sttl_schevo src_rel src_vars init_rel_lst in

put_rt
;;


(* **************************************************************
 Generate put_base
 (example)
 Output:
+b_t(X,Y,Z) :- t(X,Y,Z), not t_evo(X,Y,Z), not b_t(X,Y,Z).
-b_t(X,Y,Z) :- not t(X,Y,Z), t_evo(X,Y,Z), b_t(X,Y,Z).
new_b_t(X,Y,Z) :- b_t(X,Y,Z), not -b_t(X,Y,Z).
new_b_t(X,Y,Z) :- -b_t(X,Y,Z).
************************************************************** *)
let generate_put_base target_rel target_vars =

  let put_base = [
    Rule(Deltainsert("b_" ^ target_rel, target_vars),
        [Rel(Pred(target_rel, target_vars));
         Not(Pred(target_rel ^ "_0", target_vars));
         Not(Pred("b_" ^ target_rel, target_vars))
        ] );

     Rule(Deltadelete("b_" ^ target_rel, target_vars),
         [Not(Pred(target_rel, target_vars));
          Rel(Pred(target_rel ^ "_0", target_vars));
          Rel(Pred("b_" ^ target_rel, target_vars))
         ] );

     Rule(Pred("new_b_" ^ target_rel, target_vars),
         [Rel(Pred("b_" ^ target_rel, target_vars));
          Not(Deltadelete("b_" ^ target_rel, target_vars));
         ] );

     Rule(Pred("new_b_" ^ target_rel, target_vars),
         [Rel(Deltainsert("b_" ^ target_rel, target_vars));
         ] );
  ] in


put_base
;;

(* **************************************************************
 Generate put_auxc
 (example)
 Output:
  ins_s1(X,Y,Z,W) :- s1(X,Y,Z,W), not s1_0(X,Y,Z,W).
  del_s1(X,Y,Z,W) :- not s1(X,Y,Z,W), s1_0(X,Y,Z,W).
  +a_c_s1(X,W) :- ins_s1(X,Y,Z,W), +b_t(X,Y,Z), not a_c_s1(X,W).
  -a_c_s1(X,W) :- del_s1(X,Y,Z,W), -b_t(X,Y,Z), a_c_s1(X,W).
  new_a_c_s1(X,W) :- a_c_s1(X,W), not -a_c_s1(X,W).
  new_a_c_s1(X,W) :- +a_c_s1(X,W).
************************************************************** *)
let generate_put_auxc pred target_rel target_vars auxc_varlst =

(*
  let rec gen_c src_rel auxc_varlst = match auxc_varlst with
    | [] -> []
    | hd::rest -> (_1_gen_c src_rel hd) @ (gen_c src_rel rest)
    and _1_gen_c src_rel hd =
      if src_rel = (fst hd)
        then [snd hd]
        else []
  in
*)

  let src_rel = get_rel_from_pred pred in
  let src_vars = get_varlst_from_pred pred in
  let a_c_s_varlst = get_auxc_var src_rel auxc_varlst in

  let put_aux_c = [
    Rule(Pred("ins_" ^ src_rel, src_vars ),
      [
        Rel(Pred(src_rel, src_vars));
        Not(Pred(src_rel ^ "_0", src_vars));
      ] );

    Rule(Pred("del_" ^ src_rel, src_vars ),
      [
        Not(Pred(src_rel, src_vars));
        Rel(Pred(src_rel ^ "_0", src_vars));
      ] );

    Rule(Deltainsert("a_c_" ^ src_rel, a_c_s_varlst ),
      [
        Rel(Pred("ins_" ^ src_rel, src_vars));
        Rel(Deltainsert("b_" ^ target_rel, target_vars));
        Not(Pred("a_c_" ^ src_rel, a_c_s_varlst));
      ] );

    Rule(Deltadelete("a_c_" ^ src_rel, a_c_s_varlst ),
      [
        Rel(Pred("del_" ^ src_rel, src_vars));
        Rel(Deltadelete("b_" ^ target_rel, target_vars));
        Rel(Pred("a_c_" ^ src_rel, a_c_s_varlst));
      ] );

    Rule(Pred("new_a_c_" ^ src_rel, a_c_s_varlst ),
      [
        Rel(Pred("a_c_" ^ src_rel,  a_c_s_varlst));
        Not(Deltadelete("a_c_" ^ src_rel,  a_c_s_varlst));
      ] );

    Rule(Pred("new_a_c_" ^ src_rel, a_c_s_varlst ),
      [
        Rel(Deltainsert("a_c_" ^ src_rel,  a_c_s_varlst));
      ] );

  ]
  in

put_aux_c
;;


(* **************************************************************
 Generate put_aux
 (example)
 Output:
  pp_s1(X,Y,Z,W) :- new_b_t(X,Y,Z), new_a_c_s1(X,W).
  +a_lost_s1(X,Y,Z,W) :- s1(X,Y,Z,W), not pp_s1(X,Y,Z,W), not a_lost_s1(X,Y,Z,W).
  -a_lost_s1(X,Y,Z,W) :- not s1(X,Y,Z,W), a_lost_s1(X,Y,Z,W).
  +a_gain_s1(X,Y,Z,W) :- not s1(X,Y,Z,W), pp_s1(X,Y,Z,W), not a_gain_s1(X,Y,Z,W).
  -a_gain_s1(X,Y,Z,W) :- s1(X,Y,Z,W), a_gain_s1(X,Y,Z,W).
  -a_gain_s1(X,Y,Z,W) :- not pp_s1(X,Y,Z,W), a_gain_s1(X,Y,Z,W).

  -a_lost_t(X,Y,Z) :- +b_t(X,Y,Z), a_lost_t(X,Y,Z).
  -a_lost_t(X,Y,Z) :- -b_t(X,Y,Z), a_lost_t(X,Y,Z).
  -a_gain_t(X,Y,Z) :- +b_t(X,Y,Z), a_gain_t(X,Y,Z).
  -a_gain_t(X,Y,Z) :- -b_t(X,Y,Z), a_gain_t(X,Y,Z).
************************************************************** *)
let generate_put_aux pred target_rel target_vars auxc_varlst =


  let src_rel = get_rel_from_pred pred in
  let src_vars = get_varlst_from_pred pred in
  let a_c_s_varlst = get_auxc_var src_rel auxc_varlst in

  let put_aux = [
    Rule(Pred("pp_" ^ src_rel, src_vars ),
      [
        Rel(Pred("new_b_" ^ target_rel, target_vars));
        Rel(Pred("new_a_c_" ^ src_rel, a_c_s_varlst));
      ] );

    Rule(Deltainsert("a_lost_" ^ src_rel, src_vars),
      [
        Rel(Pred(src_rel, src_vars));
        Not(Pred("pp_" ^ src_rel, src_vars));
        Not(Pred("a_lost_" ^ src_rel, src_vars));
      ] );

    Rule(Deltadelete("a_lost_" ^ src_rel, src_vars),
      [
        Not(Pred(src_rel, src_vars));
        Rel(Pred("a_lost_" ^ src_rel, src_vars));
      ] );

    Rule(Deltainsert("a_gain_" ^ src_rel, src_vars),
      [
        Not(Pred(src_rel, src_vars));
        Rel(Pred("pp_" ^ src_rel, src_vars));
        Not(Pred("a_gain_" ^ src_rel, src_vars));
      ] );

    Rule(Deltadelete("a_gain_" ^ src_rel, src_vars),
      [
        Rel(Pred(src_rel, src_vars));
        Rel(Pred("a_gain_" ^ src_rel, src_vars));
      ] );

    Rule(Deltadelete("a_gain_" ^ src_rel, src_vars),
      [
        Not(Pred("pp_" ^ src_rel, src_vars));
        Rel(Pred("a_gain_" ^ src_rel, src_vars));
      ] );

    Rule(Deltadelete("a_lost_" ^ target_rel, target_vars),
      [
        Rel(Deltainsert("b_" ^ target_rel, target_vars));
        Rel(Pred("a_lost_" ^ target_rel, target_vars));
      ] );

    Rule(Deltadelete("a_lost_" ^ target_rel, target_vars),
      [
        Rel(Deltadelete("b_" ^ target_rel, target_vars));
        Rel(Pred("a_lost_" ^ target_rel, target_vars));
      ] );

    Rule(Deltadelete("a_gain_" ^ target_rel, target_vars),
      [
        Rel(Deltainsert("b_" ^ target_rel, target_vars));
        Rel(Pred("a_gain_" ^ target_rel, target_vars));
      ] );

    Rule(Deltadelete("a_gain_" ^ target_rel, target_vars),
      [
        Rel(Deltadelete("b_" ^ target_rel, target_vars));
        Rel(Pred("a_gain_" ^ target_rel, target_vars));
      ] );


  ] in

put_aux
;;


(* **************************************************************
 Generate cs
 (example)
 Input:
  _|_ :- s1(X,Y,Z,W), Y<=0.
  _|_ :- t(X,Y,Z), Y<=0.
 Output:
  _|_ :- s1(X,Y,Z,W), Y<=0.
*************************************************************** *)
let generate_cs sttl_constraint_core target_rel pred init_rel_lst =

  let rec gen sttl target_rel src_rel init_rel_lst = match sttl with
    | [] -> []
    | hd::rest -> (_1_gen hd target_rel src_rel init_rel_lst)
                  @ (gen rest target_rel src_rel init_rel_lst)

    and _1_gen hd target_rel src_rel init_rel_lst = match hd with
      | Rule (get_empty_pred, body) ->
        let rel_lst_body = get_rels_body_nonnegate (Prog([hd])) in
        if List.mem target_rel rel_lst_body
          then []
          else begin
            if List.mem src_rel rel_lst_body
              then begin
                let new_body = _2_gen body src_rel init_rel_lst in
                [Rule (get_empty_pred, new_body)]
              end
              else []
          end
      | _-> []

    and _2_gen body src_rel init_rel_lst = match body with
      | [] -> []
      | hd::rest -> (_3_gen hd src_rel init_rel_lst)
                    @ (_2_gen rest src_rel init_rel_lst)
    and _3_gen tm src_rel init_rel_lst = match tm with
      | Rel(Pred(rel, vars)) ->
        if (List.mem rel init_rel_lst) && (rel <> src_rel)
          then [Rel(Pred(rel ^ "_0", vars)) ]
          else [tm]
      | Not(Pred(rel, vars)) ->
        if (List.mem rel init_rel_lst) && (rel <> src_rel)
          then [Not(Pred(rel ^ "_0", vars)) ]
          else [tm]
      | _ -> [tm]
  in

  let src_rel = get_rel_from_pred pred in
  let cs = gen sttl_constraint_core target_rel src_rel init_rel_lst in

cs
;;

(* **************************************************************
 Generate cs
 (example)
 Input:
  ⊥() :- t(X,Y,Z), t(X,Y2,Z2), Y <> Y2.
  ⊥() :- t(X,Y,Z), t(X,Y2,Z2), Z <> Z2.
  ⊥() :- s1(X,Y,Z,W), s1(X,Y2,Z2,W2), Y <> Y2.
  ⊥() :- s1(X,Y,Z,W), s1(X,Y2,Z2,W2), Z <> Z2.
  ⊥() :- s1(X,Y,Z,W), s1(X,Y2,Z2,W2), W <> W2.
 Output:
  if s2 exist, it is turned to s2_0
*************************************************************** *)
let generate_cs_pk sttl_constraint_pk pred init_rel_lst =

  let rec gen sttl src_rel init_rel_lst = match sttl with
    | [] -> []
    | hd::rest -> (_1_gen hd src_rel init_rel_lst) @ (gen rest src_rel init_rel_lst)

    and _1_gen hd src_rel init_rel_lst = match hd with
      | Rule (get_empty_pred, body) ->
          let new_body = _2_gen body src_rel init_rel_lst in
          [Rule (get_empty_pred, new_body)]
      | _ -> []

    and _2_gen body src_rel init_rel_lst = match body with
      | [] -> []
      | hd::rest -> (_3_gen hd src_rel init_rel_lst)
                    @ (_2_gen rest src_rel init_rel_lst)
    and _3_gen hd src_rel init_rel_lst = match hd with
      | Rel(Pred(rel, vars)) ->
        if (List.mem rel init_rel_lst)  && (rel <> src_rel)
          then [Rel(Pred(rel ^ "_0", vars))]
          else [hd]
      | Not(Pred(rel, vars)) ->
        if (List.mem rel init_rel_lst)  && (rel <> src_rel)
          then [Rel(Pred(rel ^ "_0", vars))]
          else [hd]
      | _ -> [hd]
  in

  let src_rel = get_rel_from_pred pred in
  let cs_pk = gen sttl_constraint_pk src_rel init_rel_lst in

cs_pk
;;

(* **************************************************************
 Generate cs_aux
 (example)
 Output:
  _|_ :- a_lost_s1(X,Y,Z,W), a_gain_s1(X,Y,Z,W).
  _|_ :- a_gain_s1(X,Y,Z,W), not s1_evo(X,Y,Z,W).
*************************************************************** *)
let generate_cs_aux pred =

  let src_rel = get_rel_from_pred pred in
  let src_vars = get_varlst_from_pred pred in

  let cs_aux =  [
    Rule(get_empty_pred,
      [
        Rel(Pred("a_lost_" ^ src_rel, src_vars));
        Rel(Pred("a_gain_" ^ src_rel, src_vars));
      ]  );

    Rule(get_empty_pred,
      [
        Rel(Pred("a_gain_" ^ src_rel, src_vars));
        Not(Pred(src_rel ^ "_evo", src_vars));
      ]  );

  ] in

cs_aux
;;

(* ======================================================================================== *)
(* Algorithm 5.2 Deriving BX between Target-Side Database and View Instance of Source Schema *)
(* ======================================================================================== *)
(*
% --- schema ---------------------------------------------------
source b_t('X':string, 'Y':int).
source a_lost_s1('X':string, 'Y':int).
source a_gain_s1('X':string, 'Y':int).
source a_lost_t('X':string, 'Y':int).
source a_gain_t('X':string, 'Y':int).
view s1('X':string, 'Y':int).


--- get --------------------------------------------
s1(X,Y) :- s1_evo(X,Y).
  s1_evo(X,Y) :- b_t1(X,Y), not a_gain_s1(X,Y).
  s1_evo(X,Y) :- a_lost_s1(X,Y).


--- put --------------------------------------------
t_0(X,Y,Z) :- s1_0(X,Y,Z,W).
t(X,Y,Z) :- s1(X,Y,Z,W).

+b_t(X,Y,Z) :- t(X,Y,Z), not t_evo(X,Y,Z), not b_t(X,Y,Z).
-b_t(X,Y,Z) :- not t(X,Y,Z), t_evo(X,Y,Z), b_t(X,Y,Z).
new_b_t(X,Y,Z) :- b_t(X,Y,Z), not -b_t(X,Y,Z).
new_b_t(X,Y,Z) :- -b_t(X,Y,Z).

ins_s1(X,Y,Z,W) :- s1(X,Y,Z,W), not s1_0(X,Y,Z,W).
del_s1(X,Y,Z,W) :- not s1(X,Y,Z,W), s1_0(X,Y,Z,W).
+a_c_s1(X,W) :- ins_s1(X,Y,Z,W), +b_t(X,Y,Z), not a_c_s1(X,W).
-a_c_s1(X,W) :- del_s1(X,Y,Z,W), -b_t(X,Y,Z), a_c_s1(X,W).
new_a_c_s1(X,W) :- a_c_s1(X,W), not -a_c_s1(X,W).
new_a_c_s1(X,W) :- +a_c_s1(X,W).

pp_s1(X,Y,Z,W) :- new_b_t(X,Y,Z), new_a_c_s1(X,W).
+a_lost_s1(X,Y,Z,W) :- s1(X,Y,Z,W), not pp_s1(X,Y,Z,W), not a_lost_s1(X,Y,Z,W).
-a_lost_s1(X,Y,Z,W) :- not s1(X,Y,Z,W), a_lost_s1(X,Y,Z,W).
+a_gain_s1(X,Y,Z,W) :- not s1(X,Y,Z,W), pp_s1(X,Y,Z,W), not a_gain_s1(X,Y,Z,W).
-a_gain_s1(X,Y,Z,W) :- s1(X,Y,Z,W), a_gain_s1(X,Y,Z,W).
-a_gain_s1(X,Y,Z,W) :- not pp_s1(X,Y,Z,W), a_gain_s1(X,Y,Z,W).

-a_lost_t(X,Y,Z) :- +b_t(X,Y,Z), a_lost_t(X,Y,Z).
-a_lost_t(X,Y,Z) :- -b_t(X,Y,Z), a_lost_t(X,Y,Z).
-a_gain_t(X,Y,Z) :- +b_t(X,Y,Z), a_gain_t(X,Y,Z).
-a_gain_t(X,Y,Z) :- -b_t(X,Y,Z), a_gain_t(X,Y,Z).

_|_ :- s1(X,Y,Z,W), Y<=0.

  _|_ :- a_lost_s1(X,Y,Z,W), a_gain_s1(X,Y,Z,W).
  _|_ :- a_gain_s1(X,Y,Z,W), not s1_evo(X,Y,Z,W).

⊥() :- s1(X, Y, Z, W) , s1(X, Y2, Z2, W2) , Y <> Y2.
⊥() :- s1(X, Y, Z, W) , s1(X, Y2, Z2, W2) , Z <> Z2.
⊥() :- s1(X, Y, Z, W) , s1(X, Y2, Z2, W2) , W <> W2.

*)
(* ======================================================================================== *)
let derivation_source_birds ast_schemas ast_constraint_core ast_constraint_pk init_pred_lst head_preds_target_1 target_pred_1 ast_schevo_1 source_rels pk_lst_1 pk_lst_var var_stype log =

  (*-- functions  ----------------------------------------------------------------------------*)
  let rec get_base_rels ast_schema = match ast_schema with
      | [] -> []
      | hd::rest -> (_1_get_base_rels hd) @ (get_base_rels rest)
    and _1_get_base_rels stt = match stt with
      | Source(rel, varlst) -> [rel]
      | _ -> []
  in

  let rec derive_all_bx_ts_src
            ast_schemas
            ast_constraint_core
            ast_constraint_pk
            init_pred_lst
            init_pred_lst2
            init_rel_lst
            target_rel
            target_vars
            target_vartypes
            ast_schevo_1
            pk_lst_1
            auxc_varlst
            var_stype
    = match init_pred_lst with
    | [] -> []
    | hd::rest -> (derive_bx_ts_src ast_schemas ast_constraint_core ast_constraint_pk hd init_pred_lst2 init_rel_lst target_rel target_vars target_vartypes ast_schevo_1 pk_lst_1 auxc_varlst var_stype)
    @ (derive_all_bx_ts_src ast_schemas ast_constraint_core ast_constraint_pk rest init_pred_lst2 init_rel_lst target_rel target_vars target_vartypes ast_schevo_1 pk_lst_1 auxc_varlst var_stype)

    and derive_bx_ts_src ast_schemas ast_constraint_core ast_constraint_pk pred init_pred_lst2 init_rel_lst target_rel target_vars target_vartypes st_schevo_1 pk_lst_1 auxc_varlst var_stype =

      let ts_schema = generate_ts_schema ast_schemas pred target_rel target_vartypes auxc_varlst var_stype in
      let get_t_src =  generate_get_t_src pred in
      let get_t_src0 =  generate_get_t_src0 init_pred_lst2 target_rel target_vars auxc_varlst in
      let put_rt0 = generate_pre_schevo ast_schevo_1 ast_schevo_1 init_rel_lst target_rel  in
      let put_rt = generate_put_rt (get_sttl ast_schevo_1) pred init_rel_lst  in
      let put_base = generate_put_base target_rel target_vars in
      let put_auxc = generate_put_auxc pred target_rel target_vars auxc_varlst in
      let put_aux = generate_put_aux pred target_rel target_vars auxc_varlst in
      let cs = generate_cs (get_sttl ast_constraint_core) target_rel pred init_rel_lst in
      let cs_aux = generate_cs_aux pred in
      let cs_pk = generate_cs_pk (get_sttl ast_constraint_pk) pred init_rel_lst in

      let ast = Prog (ts_schema @
                      get_t_src @ get_t_src0 @
                      put_rt0 @ put_rt @ put_base @ put_auxc @ put_aux @
                      cs @ cs_aux @ cs_pk
                     ) in
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
  let init_rel_lst = get_rels init_pred_lst in
  let target_rel = get_rel_from_pred target_pred_1 in
  let target_vars = get_varlst_from_pred target_pred_1 in
  let target_vartypes = get_vartypes_schema ast_schemas target_rel in
  let auxc_varlst = get_auxc_varlst pk_lst_var target_rel target_vars init_pred_lst in (* eg, (s1,[X]), (s2, [X,Y]) *)

  (*-- main ----------------------------------------------------------------------------*)
  let ast_lst = derive_all_bx_ts_src
                ast_schemas
                ast_constraint_core
                ast_constraint_pk
                init_pred_lst
                init_pred_lst
                init_rel_lst
                target_rel
                target_vars
                target_vartypes
                ast_schevo_1
                pk_lst_1
                auxc_varlst
                var_stype
  in
ast_lst
;;

(* ---------------------------------------------------------------------------------------------*)
(* ---------------------------------------------------------------------------------------------*)
(* ---------------------------------------------------------------------------------------------*)
(* ---------------------------------------------------------------------------------------------*) (* ---------------------------------------------------------------------------------------------*)


(*********************************************
  In: AST of schema, pred_list, target_rel_1
  Out: AST of BIRDS program for target schema
*********************************************)
let generate_ts_schema_tar ast_schemas pred target_rel_1 target_vartyes_1 auxc_varlst var_stype =

  let rec gen sttl pred target_rel_1 target_vartyes_1 auxc_varlst var_stype = match sttl with
    | [] -> []
    | hd::rest -> (_1_gen hd pred target_rel_1 target_vartyes_1 auxc_varlst var_stype)
                  @ (gen rest pred target_rel_1 target_vartyes_1 auxc_varlst var_stype)

  and _1_gen stt pred target_rel_1 target_vartyes_1 auxc_varlst var_stype = match stt with
    | Source_schema  (_, rel, varlst) ->
        let rel_pred = get_rterm_predname pred in
            if rel = rel_pred
            then
              [
               Source ("b_" ^ target_rel_1, target_vartyes_1);   (* Tb: base relation *)
               Source ( (get_aux_lost rel), varlst);     (* Alost_s *)
               Source ( (get_aux_gain rel), varlst);     (* Again_s *)
               Source ( (get_aux_c rel), (get_auxc_var_stype rel auxc_varlst var_stype ));  (* Ac_s *)
               Source ( (get_aux_lost target_rel_1), target_vartyes_1);     (* Alost_t *)
               Source ( (get_aux_gain target_rel_1), target_vartyes_1)    (* Again_t *)
              ]
            else
              [
               Source ( (get_aux_lost rel), varlst);     (* Alost_s *)
               Source ( (get_aux_gain rel), varlst);     (* Again_s *)
               Source ( (get_aux_c rel), (get_auxc_var_stype rel auxc_varlst var_stype ))   (* Ac_s *)
              ]
    | Target_schema (_, rel, varlst) ->
        [
          Source ( "b_" ^ rel, varlst);              (* b_t *)
          Source ( (get_aux_lost rel), varlst);     (* Alost_t *)
          Source ( (get_aux_gain rel), varlst);     (* Again_t *)
          View (rel, varlst);
        ]
    | _ -> []
  in

  let result = gen (get_sttl ast_schemas) pred target_rel_1 target_vartyes_1 auxc_varlst var_stype in
result
;;

(* **************************************************************
  Generate get_t_trg
 (example)
  t(X,Y,Z,W) :- t_0(X,Y,Z).
************************************************************** *)
let generate_get_t_trg pred  =

  let tar_rel = get_rel_from_pred pred in
  let tar_vars = get_varlst_from_pred pred in
  let get_t_trg = [
      Rule(Pred(tar_rel, tar_vars) , [Rel(Pred(tar_rel ^ "_0", tar_vars))])
      (*
      Rule(Pred(tar_rel, tar_vars), [Rel(Pred("b_" ^ tar_rel, tar_vars));
                                            Not(Pred("a_gain_" ^ tar_rel, tar_vars))] );

      Rule(Pred(tar_rel, tar_vars), [Rel(Pred("a_lost_" ^ tar_rel, tar_vars))] );
      *)
  ]
 in

get_t_trg
;;

(* **************************************************************
  Generate get_t_trg0
 (example)
  t_0(X,Y,Z) :- b_t(X,Y,Z), not a_t_del(X,Y,Z).
  t_0(X,Y,Z) :- a_t_ins(X,Y,Z).
************************************************************** *)
let generate_get_t_trg0  tar_pred =

  let tar_rel = get_rel_from_pred tar_pred in
  let tar_vars = get_varlst_from_pred tar_pred in

  let t_trg0 = [
      Rule(Pred(tar_rel ^ "_0", tar_vars), [Rel(Pred("b_" ^ tar_rel, tar_vars));
                                            Not(Pred("a_gain_" ^ tar_rel, tar_vars))] );

      Rule(Pred(tar_rel ^ "_0", tar_vars), [Rel(Pred("a_lost_" ^ tar_rel, tar_vars))] );
    ]
  in

t_trg0
;;

(* **************************************************************
  Generate put_t_rdt
 (example)
  ins_t(X,Y,Z) :- t(X,Y,Z), not t_0(X,Y,Z).
  del_t(X,Y,Z) :- not t(X,Y,Z), t_0(X,Y,Z).
************************************************************** *)
let generate_put_t_rdt tar_pred =
  let tar_rel = get_rel_from_pred tar_pred in
  let tar_vars = get_varlst_from_pred tar_pred in

  let rdt = [
      Rule(Pred("ins_" ^ tar_rel, tar_vars), [Rel(Pred(tar_rel, tar_vars));
                                              Not(Pred(tar_rel ^"_0", tar_vars))] );

      Rule(Pred("del_" ^ tar_rel, tar_vars), [Not(Pred(tar_rel, tar_vars));
                                              Rel(Pred(tar_rel ^"_0", tar_vars))] );
    ]
  in

rdt
;;


(* **************************************************************
  Generate put_t_rds
  Input:
    +s1(X,Y,Z,W) :- +t(X,Y,Z), not s1(X,Y,Z,_), Y < 100, W=''.
    -s1(X,Y,Z,W) :- -t(X,Y,Z), s1(X,Y,Z,W), Y < 100.
  Output:
    ins_s1(X,Y,Z,W) :- ins_t(X,Y,Z), not s1(X,Y,Z,_), Y < 100, W=''.
    del_s1(X,Y,Z,W) :- del_t(X,Y,Z), s1(X,Y,Z,W), Y < 100.
************************************************************** *)
let generate_put_t_rds ast_bwd =

  let rec gen sttl_bwd = match sttl_bwd with
    | [] -> []
    | hd::rest -> (_1_gen hd) @ (gen rest)

    and _1_gen stt_bwd = match stt_bwd with
      | Rule (Pred(rel,vars), body) ->
          let new_body = _2_gen body in
          [Rule (Pred(rel,vars), new_body)]
      | Rule (Deltainsert(rel,vars), body) ->
          let new_body = _2_gen body in
          [Rule (Pred("ins_" ^ rel,vars), new_body)]
      | Rule (Deltadelete(rel,vars), body) ->
          let new_body = _2_gen body in
          [Rule (Pred("del_" ^ rel,vars), new_body)]
      | _ -> []

    and _2_gen body = match body with
      | [] -> []
      | hd::rest -> (_3_gen hd) @ (_2_gen rest)
    and _3_gen tm = match tm with
      | Rel(Deltainsert(rel, vars)) -> [Rel(Pred("ins_" ^ rel, vars))]
      | Rel(Deltadelete(rel, vars)) -> [Rel(Pred("del_" ^ rel, vars))]
      | Not(Deltainsert(rel, vars)) -> [Not(Pred("ins_" ^ rel, vars))]
      | Not(Deltadelete(rel, vars)) -> [Not(Pred("del_" ^ rel, vars))]
      | _ -> [tm]
  in

  let sttl_bwd = get_sttl ast_bwd in
  let put_rds = gen sttl_bwd in

put_rds
;;

(* **************************************************************
  Generate put_t_ri
  example:
  +b_t(X,Y,Z) :- ins_s1(X,Y,Z,W), ins_t(X,Y,Z), not b_t(X,Y,Z).
  -b_t(X,Y,Z) :- del_s1(X,Y,Z,W), del_t(X,Y,Z), b_t(X,Y,Z).
  +a_c_s1(X,W) :- ins_s1(X,Y,Z,W), not a_c_s1(X,W).
  -a_c_s1(X,W) :- del_s1(X,Y,Z,W), not ins_s1(X,_,_,_), a_c_s1(X,W).
************************************************************** *)
let generate_put_t_ri tar_pred init_pred_lst auxc_keylst auxc_varlst back_ins_rels back_del_rels =

  let rec get_ins_s_var s_vars var_keys = match s_vars with
    | [] -> []
    | hd::rest -> (_1_get_ins_s_var hd var_keys)
                  @ (get_ins_s_var rest var_keys)

    and _1_get_ins_s_var var var_keys = match var with
      | NamedVar (str) ->
          if List.mem var var_keys
            then [var]
            else [AnonVar]
      | _ -> [var]
  in


  let rec gen tar_rel tar_vars init_pred_lst auxc_keylst auxc_varlst back_ins_rels back_del_rels = match init_pred_lst with
    | [] -> []
    | hd::rest -> (_1_gen tar_rel tar_vars hd auxc_keylst auxc_varlst back_ins_rels back_del_rels)
                  @ (gen tar_rel tar_vars rest auxc_keylst auxc_varlst back_ins_rels back_del_rels)

    and _1_gen tar_rel tar_vars src_pred auxc_keylst auxc_varlst back_ins_rels back_del_rels = match src_pred with
      | Pred(src_rel, src_vars)->
        let var_auxc = get_auxc_var src_rel auxc_varlst in
        let var_keys = get_auxc_var src_rel auxc_keylst in
        let ins_s_var = get_ins_s_var src_vars var_keys in

          (*
              printf "src_rel = %s\n" src_rel;

               printf "var_auxc=> [";
               printf "%s, " src_rel;
               let print_el s = printf "%s; " s in
               List.iter print_el (List.map string_of_var var_auxc);
               printf "]\n";

               printf "var_keys=> [";
               printf "%s, " src_rel;
               let print_el s = printf "%s; " s in
               List.iter print_el (List.map string_of_var var_keys);
               printf "]\n";

               printf "ins_s_var=> [";
               printf "%s, " src_rel;
               let print_el s = printf "%s; " s in
               List.iter print_el (List.map string_of_var ins_s_var);
               printf "]\n";
        *)

        if (List.mem src_rel back_ins_rels) && (List.mem src_rel back_del_rels)
          then begin
                [
                  Rule(Deltainsert("b_" ^ tar_rel, tar_vars),
                         [Rel(Pred("ins_" ^ src_rel, src_vars));
                          Rel(Pred("ins_" ^ tar_rel, tar_vars));
                          Not(Pred("b_" ^ tar_rel, tar_vars))
                         ]);

                  Rule(Deltadelete("b_" ^ tar_rel, tar_vars),
                         [Rel(Pred("del_" ^ src_rel, src_vars));
                          Rel(Pred("del_" ^ tar_rel, tar_vars));
                          Rel(Pred("b_" ^ tar_rel, tar_vars))
                         ]);

                  Rule(Deltainsert("a_c_" ^ src_rel, var_auxc),
                         [Rel(Pred("ins_" ^ src_rel, src_vars));
                          Not(Pred("a_c_" ^ src_rel, var_auxc));
                         ]);

                  Rule(Deltadelete("a_c_" ^ src_rel, var_auxc),
                         [Rel(Pred("del_" ^ src_rel, src_vars));
                          Not(Pred("ins_" ^ src_rel, ins_s_var));
                          Rel(Pred("a_c_" ^ src_rel, var_auxc));
                         ]);
                ]
          end

          else begin
            if (List.mem src_rel back_ins_rels) && (not (List.mem src_rel back_del_rels))
              then begin
                [
                  Rule(Deltainsert("b_" ^ tar_rel, tar_vars),
                         [Rel(Pred("ins_" ^ src_rel, src_vars));
                          Rel(Pred("ins_" ^ tar_rel, tar_vars));
                          Not(Pred("b_" ^ tar_rel, tar_vars))
                         ]);

                  Rule(Deltainsert("a_c_" ^ src_rel, var_auxc),
                         [Rel(Pred("ins_" ^ src_rel, src_vars));
                          Not(Pred("a_c_" ^ src_rel, var_auxc));
                         ]);
                ]
              end

              else begin
                if (not (List.mem src_rel back_ins_rels)) && (List.mem src_rel back_del_rels)
                  then begin
                  [
                    Rule(Deltadelete("b_" ^ tar_rel, tar_vars),
                           [Rel(Pred("del_" ^ src_rel, src_vars));
                            Rel(Pred("del_" ^ tar_rel, tar_vars));
                            Rel(Pred("b_" ^ tar_rel, tar_vars))
                           ]);

                    Rule(Deltadelete("a_c_" ^ src_rel, var_auxc),
                           [Rel(Pred("del_" ^ src_rel, src_vars));
                            Not(Pred("a_c_" ^ src_rel, var_auxc));
                           ]);
                  ]
                  end
                  else begin
                    []
                  end
              end
          end
      | _ -> []
  in


         printf "back_ins_rels=> [";
         let print_el s = printf "%s; " s in
         List.iter print_el back_ins_rels;
         printf "]\n";

         printf "back_del_rels=> [";
         let print_el s = printf "%s; " s in
         List.iter print_el back_del_rels;
         printf "]\n";

  let tar_rel = get_rel_from_pred tar_pred in
  let tar_vars = get_varlst_from_pred tar_pred in
  let put_t_ri = gen tar_rel tar_vars init_pred_lst auxc_keylst auxc_varlst back_ins_rels back_del_rels in

put_t_ri
;;

(* **************************************************************
  Generate put_t_rp_base
  example:
  b_t_p(X,Y,Z) :- b_t(X,Y,Z), not -b_t(X,Y,Z).
  b_t_p(X,Y,Z) :- +b_t(X,Y,Z).
************************************************************** *)
let generate_put_t_rp_base tar_pred t_rback_ins_rel t_rback_del_rel =
  let tar_rel = get_rel_from_pred tar_pred in
  let tar_vars = get_varlst_from_pred tar_pred in
  let bt_rel = "b_" ^ tar_rel in

  let put_t_rp_base =
    if (List.mem bt_rel t_rback_ins_rel) && (List.mem bt_rel t_rback_del_rel)
      then begin
             [
              Rule(Pred("b_" ^ tar_rel ^ "_p", tar_vars),
                   [Rel(Pred("b_" ^ tar_rel, tar_vars));
                    Not(Deltadelete("b_" ^ tar_rel, tar_vars));
                  ]);

              Rule(Pred("b_" ^ tar_rel ^ "_p", tar_vars),
                   [Rel(Deltainsert("b_" ^ tar_rel, tar_vars));
                  ]);
              ]
      end

      else begin
        if (List.mem bt_rel t_rback_ins_rel) && (not (List.mem bt_rel t_rback_del_rel))
          then begin
               [
                Rule(Pred("b_" ^ tar_rel ^ "_p", tar_vars),
                     [Rel(Pred("b_" ^ tar_rel, tar_vars));
                    ]);

                Rule(Pred("b_" ^ tar_rel ^ "_p", tar_vars),
                     [Rel(Deltadelete("b_" ^ tar_rel, tar_vars));
                    ]);
                ]
          end

          else begin
            if (not (List.mem bt_rel t_rback_ins_rel)) && (List.mem bt_rel t_rback_del_rel)
              then begin
                 [
                  Rule(Pred("b_" ^ tar_rel ^ "_p", tar_vars),
                       [Rel(Pred("b_" ^ tar_rel, tar_vars));
                        Not(Deltadelete("b_" ^ tar_rel, tar_vars));
                      ]);
                  ]
              end

              else  begin
                 [
                  Rule(Pred("b_" ^ tar_rel ^ "_p", tar_vars),
                       [Rel(Pred("b_" ^ tar_rel, tar_vars));
                      ]);
                  ]
              end
          end
      end
 in

put_t_rp_base
;;

(* **************************************************************
  Generate put_t_rp_base
  example:
  +a_lost_t (X,Y,Z) :- t(X,Y,Z), not b_t_p(X,Y,Z), not a_lost_t (X,Y,Z).
  -a_lost_t (X,Y,Z) :- not t(X,Y,Z), a_lost_t (X,Y,Z).
  +a_gain_t(X,Y,Z) :- not t(X,Y,Z), b_t_p(X,Y,Z), not a_gain_t(X,Y,Z).
  -a_gain_t(X,Y,Z) :- t(X,Y,Z), a_gain_t(X,Y,Z).
  -a_gain_t(X,Y,Z) :- not b_t_p(X,Y,Z), a_gain_t(X,Y,Z).
************************************************************** *)
let generate_put_t_rp_auxt tar_pred =
  let tar_rel = get_rel_from_pred tar_pred in
  let tar_vars = get_varlst_from_pred tar_pred in

  let put_t_rp_auxt = [
    Rule(Deltainsert("a_lost_" ^ tar_rel, tar_vars),
         [Rel(Pred(tar_rel, tar_vars));
          Not(Pred("b_" ^ tar_rel ^ "_p", tar_vars));
          Not(Pred("a_lost_" ^ tar_rel, tar_vars));
        ]);

    Rule(Deltadelete("a_lost_" ^ tar_rel, tar_vars),
         [Not(Pred(tar_rel, tar_vars));
          Rel(Pred("a_lost_" ^ tar_rel, tar_vars));
        ]);

    Rule(Deltainsert("a_gain_" ^ tar_rel, tar_vars),
         [Not(Pred(tar_rel, tar_vars));
          Rel(Pred("b_" ^ tar_rel ^ "_p", tar_vars));
          Not(Pred("a_gain_" ^ tar_rel, tar_vars));
        ]);

    Rule(Deltadelete("a_gain_" ^ tar_rel, tar_vars),
         [Rel(Pred(tar_rel, tar_vars));
          Rel(Pred("a_gain_" ^ tar_rel, tar_vars));
        ]);

    Rule(Deltadelete("a_gain_" ^ tar_rel, tar_vars),
         [Not(Pred("b_" ^ tar_rel ^ "_p", tar_vars));
          Rel(Pred("a_gain_" ^ tar_rel, tar_vars));
        ]);

  ] in

put_t_rp_auxt
;;

(* **************************************************************
  Generate put_t_rp_auxs
  example:
    -a_lost_s1(X,Y,Z,W) :- ins_s1(X,Y,Z,W), a_lost_s1(X,Y,Z,W).
    -a_lost_s1(X,Y,Z,W) :- del_s1(X,Y,Z,W), a_lost_s1(X,Y,Z,W).
    -a_gain_s1(X,Y,Z,W) :- ins_s1(X,Y,Z,W), a_gain_s1(X,Y,Z,W).
    -a_gain_s1(X,Y,Z,W) :- del_s1(X,Y,Z,W), a_gain_s1(X,Y,Z,W).
************************************************************** *)
let generate_put_t_rp_auxs init_pred_lst back_ins_rels back_del_rels =

  let rec gen init_pred_lst = match init_pred_lst with
    | [] -> []
    | hd::rest -> (_1_gen hd) @ (gen rest)
    and _1_gen pred = match pred with
      | Pred(src_rel, src_vars) ->
          if (List.mem src_rel back_ins_rels) && (List.mem src_rel back_del_rels)
              then begin
                    [
                        Rule(Deltadelete("a_lost_" ^ src_rel, src_vars),
                           [Rel(Pred("ins_" ^ src_rel, src_vars));
                            Rel(Pred("a_lost_" ^ src_rel, src_vars));
                          ]);

                        Rule(Deltadelete("a_lost_" ^ src_rel, src_vars),
                           [Rel(Pred("del_" ^ src_rel, src_vars));
                            Rel(Pred("a_lost_" ^ src_rel, src_vars));
                          ]);

                        Rule(Deltadelete("a_gain_" ^ src_rel, src_vars),
                           [Rel(Pred("ins_" ^ src_rel, src_vars));
                            Rel(Pred("a_gain_" ^ src_rel, src_vars));
                          ]);

                        Rule(Deltadelete("a_gain_" ^ src_rel, src_vars),
                           [Rel(Pred("del_" ^ src_rel, src_vars));
                            Rel(Pred("a_gain_" ^ src_rel, src_vars));
                          ]);
                    ]
              end

              else begin
                if (List.mem src_rel back_ins_rels) && (not (List.mem src_rel back_del_rels))
                  then begin
                    [
                        Rule(Deltadelete("a_lost_" ^ src_rel, src_vars),
                           [Rel(Pred("ins_" ^ src_rel, src_vars));
                            Rel(Pred("a_lost_" ^ src_rel, src_vars));
                          ]);

                        Rule(Deltadelete("a_gain_" ^ src_rel, src_vars),
                           [Rel(Pred("ins_" ^ src_rel, src_vars));
                            Rel(Pred("a_gain_" ^ src_rel, src_vars));
                          ]);
                    ]

                  end
                  else begin
                    if (not (List.mem src_rel back_ins_rels)) && (List.mem src_rel back_del_rels)
                      then begin
                      [
                          Rule(Deltadelete("a_lost_" ^ src_rel, src_vars),
                             [Rel(Pred("del_" ^ src_rel, src_vars));
                              Rel(Pred("a_lost_" ^ src_rel, src_vars));
                            ]);

                          Rule(Deltadelete("a_gain_" ^ src_rel, src_vars),
                             [Rel(Pred("del_" ^ src_rel, src_vars));
                              Rel(Pred("a_gain_" ^ src_rel, src_vars));
                            ]);
                      ]


                      end
                      else begin
                        []
                      end
                  end
              end

      | _ -> []
  in

  let put_t_rp_auxs = gen init_pred_lst in

put_t_rp_auxs
;;

(* **************************************************************
 Generate ct
 (example)
 Input:
  _|_ :- s1(X,Y,Z,W), Y<=0.
  _|_ :- t(X,Y,Z), Y<=0.
 Output:
  _|_ :- t(X,Y,Z), Y<=0.
*************************************************************** *)
let generate_ct sttl_constraint_core target_rel =

  let rec gen sttl target_rel = match sttl with
    | [] -> []
    | hd::rest -> (_1_gen hd target_rel) @ (gen rest target_rel)

    and _1_gen hd target_rel = match hd with
      | Rule (get_empty_pred, body) ->
        let rel_lst_body = get_rels_body (Prog([hd])) in
        if List.mem target_rel rel_lst_body
          then [hd]
          else []
      | _-> []
  in

  let ct = gen sttl_constraint_core target_rel in

ct
;;


(* **************************************************************
 Generate ct_aux
 (example)
 Output:
  _|_ :- a_lost_t(X,Y,Z), a_gain_t(X,Y,Z).
  _|_ :- a_gain_t(X,Y,Z), not b_t(X,Y,Z).
*************************************************************** *)
let generate_ct_aux tar_pred =

  let tar_rel = get_rel_from_pred tar_pred in
  let tar_vars = get_varlst_from_pred tar_pred in

  let ct_aux =  [
    Rule(get_empty_pred,
      [
        Rel(Pred("a_lost_" ^ tar_rel, tar_vars));
        Rel(Pred("a_gain_" ^ tar_rel, tar_vars));
      ]  );

    Rule(get_empty_pred,
      [
        Rel(Pred("a_gain_" ^ tar_rel, tar_vars));
        Not(Pred("b_" ^ tar_rel, tar_vars));
      ]  );

  ] in

ct_aux
;;


(* **************************************************************
 Generate ct_pk
 (example)
 Input:
  ⊥() :- t(X,Y,Z), t(X,Y2,Z2), Y <> Y2.
  ⊥() :- t(X,Y,Z), t(X,Y2,Z2), Z <> Z2.
  ⊥() :- s1(X,Y,Z,W), s1(X,Y2,Z2,W2), Y <> Y2.
  ⊥() :- s1(X,Y,Z,W), s1(X,Y2,Z2,W2), Z <> Z2.
  ⊥() :- s1(X,Y,Z,W), s1(X,Y2,Z2,W2), W <> W2.
 Output:
  ⊥() :- t(X,Y,Z), t(X,Y2,Z2), Y <> Y2.
  ⊥() :- t(X,Y,Z), t(X,Y2,Z2), Z <> Z2.
*************************************************************** *)
let generate_ct_pk sttl_constraint_pk tar_pred  =

  let rec gen sttl tar_rel = match sttl with
    | [] -> []
    | hd::rest -> (_1_gen hd tar_rel) @ (gen rest tar_rel)

    and _1_gen hd tar_rel = match hd with
      | Rule (get_empty_pred, body) ->
          let rels_body = unique_element @@ get_rels_body_tml body in
          if List.mem tar_rel rels_body
            then [hd]
            else []
      | _ -> []
  in

  let tar_rel = get_rel_from_pred tar_pred in
  let ct_pk = gen sttl_constraint_pk tar_rel in

ct_pk
;;

(* ======================================================================================== *)
(* Algorithm 5.3 Deriving BX between Target-Side Database and View Instance of Target Schema *)
(* ======================================================================================== *)
(*
% --- schema ---------------------------------------------------
source b_t('X':string, 'Y':int).
source a_lost_s1('X':string, 'Y':int).
source a_gain_s1('X':string, 'Y':int).
source a_lost_t('X':string, 'Y':int).
source a_gain_t('X':string, 'Y':int).
view t('X':string, 'Y':int).

--- get --------------------------------------------
t(X,Y,Z) :- t_0(X,Y,Z).
  t_0(X,Y,Z) :- b_t(X,Y,Z), not a_t_del(X,Y,Z).
  t_0(X,Y,Z) :- a_t_ins(X,Y,Z).

--- put --------------------------------------------
% put_t_rs
s1(X,Y,Z,W) :- s1_0(X,Y,Z,W).
s1_0(X,Y,Z,W) :- s1_evo(X,Y,Z,W), not a_gain_s1(X,Y,Z,W).
s1_0(X,Y,Z,W) :- a_lost_s1(X,Y,Z,W).
s1_evo(X,Y,Z,W) :- b_t(X,Y,Z), a_c_s1(X,W).

% put_t_rdt
ins_t(X,Y,Z) :- t(X,Y,Z), not t_0(X,Y,Z).
del_t(X,Y,Z) :- not t(X,Y,Z), t_0(X,Y,Z).

% put_t_rds
ins_s1(X,Y,Z,W) :- ins_t(X,Y,Z), not s1(X,Y,Z,_), Y < 100, W=''.
del_s1(X,Y,Z,W) :- del_t(X,Y,Z), s1(X,Y,Z,W), Y < 100.

% put_t_ri
+b_t(X,Y,Z) :- ins_s1(X,Y,Z,W), ins_t(X,Y,Z), not b_t(X,Y,Z).
-b_t(X,Y,Z) :- del_s1(X,Y,Z,W), del_t(X,Y,Z), b_t(X,Y,Z).
+a_c_s1(X,W) :- ins_s1(X,Y,Z,W), not a_c_s1(X,W).
-a_c_s1(X,W) :- del_s1(X,Y,Z,W), not ins_s1(X,_,_,_), a_c_s1(X,W).

% put_t_rp_base
b_t_p(X,Y,Z) :- b_t(X,Y,Z), not -b_t(X,Y,Z).
b_t_p(X,Y,Z) :- +b_t(X,Y,Z).

% put_t_rp_base
+a_lost_t (X,Y,Z) :- t(X,Y,Z), not b_t_p(X,Y,Z), not a_lost_t (X,Y,Z).
-a_lost_t (X,Y,Z) :- not t(X,Y,Z), a_lost_t (X,Y,Z).
+a_gain_t(X,Y,Z) :- not t(X,Y,Z), b_t_p(X,Y,Z), not a_gain_t(X,Y,Z).
-a_gain_t(X,Y,Z) :- t(X,Y,Z), a_gain_t(X,Y,Z).
-a_gain_t(X,Y,Z) :- not b_t_p(X,Y,Z), a_gain_t(X,Y,Z).

% put_t_rp_auxs
-a_lost_s1(X,Y,Z,W) :- ins_s1(X,Y,Z,W), a_lost_s1(X,Y,Z,W).
-a_lost_s1(X,Y,Z,W) :- del_s1(X,Y,Z,W), a_lost_s1(X,Y,Z,W).
-a_gain_s1(X,Y,Z,W) :- ins_s1(X,Y,Z,W), a_gain_s1(X,Y,Z,W).
-a_gain_s1(X,Y,Z,W) :- del_s1(X,Y,Z,W), a_gain_s1(X,Y,Z,W).

% ct
_|_ :- t(X,Y,Z), Y<=0.

% ct_aux:
_|_ :- a_lost_t(X,Y,Z), a_gain_t(X,Y,Z).
_|_ :- a_gain_t(X,Y,Z), not b_t(X,Y,Z).

% ct_pk
⊥() :- t(X,Y,Z), t(X,Y2,Z2), Y <> Y2.
⊥() :- t(X,Y,Z), t(X,Y2,Z2), Z <> Z2.
*)
(* ======================================================================================== *)
let derivation_target_birds ast_schemas ast_constraint_core ast_constraint_pk init_pred_lst head_preds_target_1 target_pred_1 ast_schevo_1 ast_bwd_1 source_rels pk_lst_1 pk_lst_var var_stype log =


  let rec derive_all_bx_ts_trg
            ast_schemas
            ast_constraint_core
            ast_constraint_pk
            tar_pred_lst
            init_pred_lst
            init_rel_lst
            target_rel
            target_vars
            target_vartypes
            ast_schevo_1
            ast_bwd_ex_schevo
            pk_lst_1
            auxc_varlst
            auxc_keylst
            var_stype
            back_ins_rels
            back_del_rels
    = match tar_pred_lst with
    | [] -> []
    | hd::rest -> (derive_bx_ts_trg ast_schemas ast_constraint_core ast_constraint_pk hd init_pred_lst init_rel_lst target_rel target_vars target_vartypes ast_schevo_1 ast_bwd_ex_schevo pk_lst_1 auxc_varlst auxc_keylst var_stype back_ins_rels back_del_rels)
    @ (derive_all_bx_ts_trg ast_schemas ast_constraint_core ast_constraint_pk rest init_pred_lst init_rel_lst target_rel target_vars target_vartypes ast_schevo_1 ast_bwd_ex_schevo pk_lst_1 auxc_varlst auxc_keylst var_stype back_ins_rels back_del_rels)

    and derive_bx_ts_trg ast_schemas ast_constraint_core ast_constraint_pk tar_pred init_pred_lst init_rel_lst target_rel target_vars target_vartypes ast_schevo_1 ast_bwd_ex_schevo pk_lst_1 auxc_varlst auxc_keylst var_stype back_ins_rels back_del_rels =

      (* deriving schema definition *)
      let ts_schema = generate_ts_schema_tar ast_schemas tar_pred target_rel target_vartypes auxc_varlst var_stype in

      (* deriving rules of get *)
      let get_t_trg =  generate_get_t_trg tar_pred in
      let get_t_trg0 =  generate_get_t_trg0 tar_pred in

      (* deriving rules of put *)
      let put_t_rs =  (List.concat @@ List.map generate_get_t_src init_pred_lst ) @
                      (generate_get_t_src0 init_pred_lst target_rel target_vars auxc_varlst) in
      let put_t_rdt = generate_put_t_rdt tar_pred in
      let put_t_rback = (generate_put_t_rds ast_bwd_ex_schevo)
                        @ (generate_put_t_ri tar_pred init_pred_lst auxc_keylst auxc_varlst back_ins_rels back_del_rels) in

      let t_rback_ins_rel = get_ins_rels_head (Prog(put_t_rback)) in
      let t_rback_del_rel = get_del_rels_head (Prog(put_t_rback)) in

      let put_t_rp_base = generate_put_t_rp_base tar_pred t_rback_ins_rel t_rback_del_rel in
      let put_t_rp_auxt = generate_put_t_rp_auxt tar_pred in
      let put_t_rp_auxs = generate_put_t_rp_auxs init_pred_lst back_ins_rels back_del_rels in

      (* deriving constraints *)
      let ct = generate_ct (get_sttl ast_constraint_core) target_rel in
      let ct_aux = generate_ct_aux tar_pred in
      let ct_pk = generate_ct_pk (get_sttl ast_constraint_pk) tar_pred in

      let ast = Prog (ts_schema @
                      get_t_trg @ get_t_trg0 @
                      put_t_rs @ put_t_rdt @ put_t_rback @ put_t_rp_base @ put_t_rp_auxt @ put_t_rp_auxs @
                      ct @ ct_aux @ ct_pk
                      (* put_rt0 @ put_rt @ put_base @ put_auxc @ put_aux @ *)
                      (* cs @ cs_aux @ cs_pk *)
                     ) in
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
  let init_rel_lst = get_rels init_pred_lst in
  let target_rel = get_rel_from_pred target_pred_1 in
  let target_vars = get_varlst_from_pred target_pred_1 in
  let target_vartypes = get_vartypes_schema ast_schemas target_rel in
  let auxc_varlst = get_auxc_varlst pk_lst_var target_rel target_vars init_pred_lst in (* eg, (s1,[X]), (s2, [X,Y]) *)
  let auxc_keylst = get_auxc_keylst pk_lst_var target_rel target_vars init_pred_lst in (* eg, (s1,[X]), (s2, [X,Y]) *)
  let tar_pred_lst = [target_pred_1] in

  let back_ins_rels = get_ins_rels_head ast_bwd_1 in
  let back_del_rels = get_del_rels_head ast_bwd_1 in

  (* exclude rule of schem evolution from ast_bwd *)
  let ast_bwd_ex_schevo = exculde_schevo ast_bwd_1 target_rel in

  (*-- main ----------------------------------------------------------------------------*)
  let ast_lst = derive_all_bx_ts_trg
                ast_schemas
                ast_constraint_core
                ast_constraint_pk
                tar_pred_lst
                init_pred_lst
                init_rel_lst
                target_rel
                target_vars
                target_vartypes
                ast_schevo_1
                ast_bwd_ex_schevo
                pk_lst_1
                auxc_varlst
                auxc_keylst
                var_stype
                back_ins_rels
                back_del_rels
  in
ast_lst
;;
