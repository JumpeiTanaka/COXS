(* @author: Jumpei Tanaka *)

open Expr;;
open Utils;;
open Printf;;


(***********************************************************
 *  execution command
 *********************************************************)
(* by Jumpei Tanaka *)
let exe_command2 command =
  let status = Sys.command @@ command in
  status;;

(** get the statement of view schema  *)
let get_source_schemas e = match e with
  | Prog sttl ->
    let is_q = function
      | Source_schema _ -> true
      | _ -> false
    in
    let lq = List.filter is_q sttl in
    match lq with
    | []   -> raise (SemErr "The program has no source")
    | _    -> lq
;;


(***********************************************************
 *  Symtable
 *********************************************************)
(* by Jumpei Tanaka *)
let print_symtable2 (st:symtable) =
  let print_el s = Printf.printf "%s" (string_of_stt s) in
  let print_lst _ lst = List.iter print_el lst in
  Hashtbl.iter print_lst st

(* by Jumpei Tanaka *)
let print_symtable_file oc (st:symtable) =
  let print_el s = output_string oc (string_of_stt s) in
  let print_lst _ lst = List.iter print_el lst in
  Hashtbl.iter print_lst st

(* Receives a rule and generates its hash key for the  symtable *)
let symtkey_of_rule2 rt : symtkey = match rt with
  | Rule (h, b) -> symtkey_of_rterm h
  | Constraint (h, b) -> symtkey_of_rterm h
  | _ -> invalid_arg "function symtkey_of_rule called without a rule"

(* make a list of key from sttlst of rule *)
let rec keylst sttlst = match sttlst with
  | [] -> []
  | hd::rest -> [_keylst hd] @ (keylst rest)
  and _keylst hd = match hd with
       | Rule _ -> symtkey_of_rule hd
       | _ -> invalid_arg "error: keylst"

(* Add rules of symtable into AST *)
let add_rules ast rules = match ast with
  |  Prog stt_lst ->  let _add_rules key lst = (@) lst in
                      let rules_lst = Hashtbl.fold _add_rules rules [] in
                      Prog (stt_lst@rules_lst)
;;

(* make keys of source from AST *)
let rec get_keys_source prog = match prog with
  | Prog (sttl) -> List.map symtkey_of_rterm (_1_get_keys_source sttl)

  and _1_get_keys_source sttl = match sttl with
        | [] -> []
        | hd::rest -> (get_source_sch_rterml hd) @ (_1_get_keys_source rest)
;;

(* make keys of target from AST *)
let rec get_keys_target prog = match prog with
  | Prog (sttl) -> List.map symtkey_of_rterm (_1_get_keys_target sttl)

  and _1_get_keys_target sttl = match sttl with
        | [] -> []
        | hd::rest -> (get_target_sch_rterml hd) @ (_1_get_keys_target rest)
;;

(***********************************************************
 *  list operation
 *********************************************************)
(* delete dupulicated item in a list *)
let rec unique_element list =
  let rec _unique_element l s =  match l with
    | [] -> s
    | first :: rest ->
                        if List.exists (fun e -> e = first) s
                        then _unique_element rest s
                        else _unique_element rest (s @ [first])
  in _unique_element list []
;;

(* list1 ⊂ list2; list inclusiton check *)
(*  (example)                                                    *)
(*      ["a"; "b"; "abc"] ⊂ ["a"; "b"; "abc"; "efg"] -> true     *)
(*      ["a"; "b"; "abc"] ⊂ ["a"; "b"; "efg"] -> false           *)
let rec list_inclusion lst1 lst2 = match lst1 with
  | [] -> true
  | hd::rest -> (List.mem hd lst2) && (list_inclusion rest lst2)
;;

(* Check whether items in lst1 exist in lst2: yes->true, no->false *)
let rec comp_lst lst1 lst2 = match lst1 with
  | [] -> false
  | hd::rest -> (List.mem hd lst2) || (comp_lst rest lst2)
;;

(* list1 - list2 *)
let rec list_setminus lst1 lst2 = match lst2 with
  | [] -> lst1
  | hd::rest -> if (List.mem hd lst1)
                then
                  let lst11 = List.filter (fun x -> x <> hd) lst1 in
                  list_setminus lst11 rest
                else
                  list_setminus lst1 rest
;;

(* list1 ⋂ list2 *)
let rec list_conjunction lst1 lst2 = match lst2 with
  | [] -> []
  | hd::rest -> if (List.mem hd lst1)
                then
                  [hd] @ (list_conjunction lst1 rest)
                else
                  list_conjunction lst1 rest
;;



(* Check intersection of lists: if exists, return true *)
let rec check_intersec lst1 lst2 = match lst1 with
  | [] -> false
  | hd::rest -> (List.mem hd lst2) || (check_intersec rest lst2)


(* Making a pair list from list1 and list2 *)
let list_to_pair lst1 lst2 =
  let rec _1_to_pair lst1 lst2 = match lst1 with
    | [] -> []
    | hd1::rest1 -> _2_to_pair hd1 rest1 lst2
  and _2_to_pair hd1 rest1 lst2 = match lst2 with
        | [] -> []
        | hd2::rest2 -> [(hd1, hd2)] @ (_1_to_pair rest1 rest2)
  in

  if (List.length lst1 <> List.length lst2)
  then []
  else _1_to_pair lst1 lst2
;;

(* Delte equivalent pair from a list, e.g., deletion of ("A","A") *)
let rec delete_equiv_pair lst = match lst with
  | [] -> []
  | hd::rest -> (_1_delete_equiv_pair hd) @ (delete_equiv_pair rest)

  and _1_delete_equiv_pair hd =
    if (fst hd = snd hd)
    then []
    else [hd]
;;

(* replace pair list *)
(* lst = [1,2,3], rep = (2, 10), result = [1,10,3] *)
let rec list_rep rep lst = match lst with
  | [] -> []
  | hd::rest -> if hd = (fst rep)
                then [snd rep] @ (list_rep rep rest)
                else [hd] @ (list_rep rep rest)
;;



(***********************************************************
 *  string
 *********************************************************)

(* a function to check whether a needle is included in a haystack *)
(* very naive brute force algorith *)
let strstr haystack needle =
  assert (needle <> "");
  let hlen = String.length haystack in
  let nlen = String.length needle in
  (* [has_prefix hpos npos] checks
     haystack.[hpos-npos+i] = needle.[i] for 0 <= i <= npos
  *)
  let rec has_prefix hpos npos =
    if haystack.[hpos] <> needle.[npos] then false
    else if npos = 0 then true
    else has_prefix (hpos - 1) (npos - 1)
  in
  let npos_init = nlen - 1 in
  let hlen_nlen = hlen - nlen in
  (* check from 0 to hlen - nlen *)
  let rec loop hstart =
    if hstart > hlen_nlen then false
    else
      if has_prefix (hstart + npos_init) npos_init then true
      else loop (hstart + 1)
  in
  loop 0

(* very naive brute force algorith *)
let strstr2 ~haystack ~needle =
  assert (needle <> "");
  let hlen = String.length haystack in
  let nlen = String.length needle in
  (* [has_prefix hpos npos] checks
     haystack.[hpos-npos+i] = needle.[i] for 0 <= i <= npos
  *)
  let rec has_prefix hpos npos =
    if haystack.[hpos] <> needle.[npos] then false
    else if npos = 0 then true
    else has_prefix (hpos - 1) (npos - 1)
  in
  let npos_init = nlen - 1 in
  let hlen_nlen = hlen - nlen in
  (* check from 0 to hlen - nlen *)
  let rec loop hstart =
    if hstart > hlen_nlen then None
    else
      if has_prefix (hstart + npos_init) npos_init then Some hstart
      else loop (hstart + 1)
  in
  loop 0

(* Jumpei Tanaka *)
(* Prints colnamtab *)
let print_colnamtab (cnt:colnamtab) =
  let print_el s =
    Printf.printf "%s; " (s)
  in
  let print_lst key lst =
    Printf.printf "(%s, %d) => [" (fst key) (snd key);
    List.iter print_el lst;
    Printf. printf "]\n";
  in
  Hashtbl.iter print_lst cnt


(* split string (e.g.) v1#t -> [v1; t;] *)
(* this function can be deldeted *)
let string_separate2 (sep: char) (str : string)  =
  let rec s_separate sep str p =
    let next_separate sep str p =
      try
        (String.index_from str (p + 1) sep)
      with _ -> String.length str in
    let start = p in
    let next  = next_separate sep str p  in
    [String.sub str start (next - start)] @
      (if next < String.length str then s_separate sep str (next + 1)
       else []) in
  s_separate sep str 0
;;

(* split string (e.g.) v1#t -> (v1, t) *)
let string_separate (sep: char) (str : string)  =
  let len = String.length str in
  let pos = String.index str sep in
  ( (String.sub str 0 pos), (String.sub str (pos+1) (len - 1 - pos )) )
;;

(* return later of splitter (e.g.) v1#t -> t *)
(*
let str_later_of (sep: char) (str : string)  =
    let len = String.length str in
    let pos = String.index str sep in
    (* error handling to be added when pos is error *)
    String.sub str (pos+1) (len - 1 - pos )
;;
*)

(* replace obj string to templ string  *)
let replace_string obj templ s =
  Str.global_replace (Str.regexp obj) templ s
;;


(**********************************************************************
  AST operation
 ***********************************************************************)
(** get the statement of target schema  *)
let get_target_schemas e = match e with
  | Prog sttl ->
    let is_q = function
      | Target_schema _ -> true
      | _ -> false
    in
    let lq = List.filter is_q sttl in
    match lq with
    | []   -> raise (SemErr "The program has no target")
    | _    -> lq
;;

(** get a list of rel names of target schema *)
let get_target_schema_rels ast =

  let rec get ast = match ast with
    | Prog sttl -> _1_get sttl
    and _1_get sttl = match sttl with
      | [] -> []
      | hd::rest -> (_2_get hd) @ (_1_get rest)
    and _2_get stt = match stt with
      | Target_schema (_, rel, varlst) -> [rel]
      | _ -> []
    in

  let rels = get ast in
rels
;;


(** get the statement of source  as a list *)
let get_source e = match e with
  | Prog sttl -> let is_q = function
                    | Source _ -> true
                    | _ -> false
                 in
                 List.filter is_q sttl
;;


(* make var from string varlst *)
let make_var varlst =
  let rec gen varlst = match varlst with
   | [] -> []
   | hd::rest -> (_1_gen hd) @ (gen rest)
  and _1_gen hd =
    [NamedVar(hd)]
  in

  let result = gen varlst in
result
;;

(* **************************************************************
  get rel name of source and view from AST
  Input: source s1(A,B) and view t1(A,B) in ast
  Output: ["s1"; "t1"]
************************************************************** *)
let get_rels_schema ast =

  let rec get ast = match ast with
    | Prog sttl -> _1_get sttl
    and _1_get sttl = match sttl with
      | [] -> []
      | hd::rest -> (_2_get hd) @ (_1_get rest)
    and _2_get stt = match stt with
      | Source (rel, valrst) -> [rel]
      | View (rel, varlst) -> [rel]
      | _ -> []
  in

  let result = get ast in
result
;;


(* **************************************************************
  get var_types of source and view from AST
  Input: source s1('A':int, 'B':string) and view t1('A':int) in ast,
         s1
  Output: ['A':int; 'B':string]
************************************************************** *)
let get_vartypes_schema ast rel =

  let rec get ast = match ast with
    | Prog sttl -> _1_get sttl
    and _1_get sttl = match sttl with
      | [] -> []
      | hd::rest -> (_2_get hd) @ (_1_get rest)
    and _2_get stt = match stt with
      | Source (s_rel, s_varlst)
      | View (s_rel, s_varlst)
        ->  if s_rel = rel then s_varlst else []
      | Source_schema(sc, s_rel, s_varlst)
      | Target_schema(sc, s_rel, s_varlst)
        ->  if s_rel = rel then s_varlst else []
      | _ -> []
  in

  let result = get ast in
result
;;

(* **************************************************************
  get rel name of source from AST
  Input: source s1(A,B) and view t1(A,B) in ast
  Output: ["s1"; "t1"]
************************************************************** *)
let get_source_rels_schema ast =

  let rec get ast = match ast with
    | Prog sttl -> _1_get sttl
    and _1_get sttl = match sttl with
      | [] -> []
      | hd::rest -> (_2_get hd) @ (_1_get rest)
    and _2_get stt = match stt with
      | Source (rel, valrst) -> [rel]
      | _ -> []
  in

  let result = get ast in
result
;;

(*
(* **************************************************************
  filter nos_preds from pred list
************************************************************** *)
let rec get_nos_preds preds = match preds with
  | [] -> []
  | hd::rest -> (_1_get hd) @ (get_nos_preds rest)

  and _1_get rt = match rt with
    | Deltainsert_nos (rel, varlst) -> [rt]
    | Deltadelete_nos (rel, varlst) -> [rt]
    | _ -> []
;;
*)

(* retrive view name *)
let get_view_name prog =

  let rec get prog = match prog with
    | Prog sttl -> _1_get sttl
    and _1_get sttl = match sttl with
      | [] -> []
      | hd::rest -> (_2_get hd) @ (_1_get rest)
    and _2_get hd = match hd with
      | View (rel, varlst) -> [rel]
      | _ -> []
  in

  let view_lst = get prog in

  if List.length view_lst = 0
  then
    ""
  else
    List.hd view_lst
;;

(*********************************************
  retrieve relation name from a predicate
  In:  Pred(relname1, varlst1)
  Out: relname1
**********************************************)
let get_rel_from_pred pred = match pred with
  | Pred(relname, _)
  | Deltainsert(relname, _)
  | Deltadelete(relname, _)
  | Deltainsert_nos(relname, _)
  | Deltadelete_nos(relname, _) -> relname
  (* | _ -> invalid_arg "function get_rel_from_pred without Pred" *)
;;


(*********************************************
  retrieve relation name from a predicate
  In:  Pred(relname1, varlst1)
  Out: varlst1
**********************************************)
let get_varlst_from_pred pred = match pred with
  | Pred(_, varlst) -> varlst
  | _ -> invalid_arg "function get_rel_from_pred without Pred"
;;




(*********************************************
  retrieve relation name from a predicate list
  In:  [Pred(relname1, varlst1); Pred(relname2, varlst2); ...]
  Out: [relname1, relname2, ...]
**********************************************)
let rec get_rels pred_lst = match pred_lst with
  | [] -> []
  | hd::rest -> [get_rel_from_pred hd] @ (get_rels rest)
;;


(*********************************************
  In: Prog [Rule(Pred(name1, varlst1), bodylst1); ...]
  Out: [name, ...]
*********************************************)
let get_rels_body prog =

  let rec _0_get_rels_body prog rels = match prog with
    | Prog sttl -> _1_get_rels_body sttl rels

    and _1_get_rels_body sttl rels = match sttl with
      | [] -> []
      | hd::rest -> (_2_get_rels_body hd rels) @ (_1_get_rels_body rest rels)

    and _2_get_rels_body hd rels = match hd with
      | Rule (Pred(name, varlst), bodylst)          -> _3_get_rels_body bodylst rels
      | Rule (Deltainsert(name, varlst), bodylst)   -> _3_get_rels_body bodylst rels
      | Rule (Deltadelete(name, varlst), bodylst)   -> _3_get_rels_body bodylst rels
      | Rule (Deltainsert_nos(name, varlst), bodylst)   -> _3_get_rels_body bodylst rels
      | Rule (Deltadelete_nos(name, varlst), bodylst)   -> _3_get_rels_body bodylst rels
    | _ -> rels

    and _3_get_rels_body bodylst rels = match bodylst with
      | [] -> []
      | hd::rest -> (_4_get_rels_body hd rels) @ (_3_get_rels_body rest rels)

    and _4_get_rels_body hd rels = match hd with
      | Rel(Pred(name, _))
      | Not(Pred(name, _)) -> rels @ [name]
(*      | Rel(Deltainsert(name, _)) *)
(*      | Rel(Deltadelete(name, _)) *)
(*      | Not(Deltainsert(name, _)) *)
(*      | Not(Deltadelete(name, _)) *)
      | _ -> rels
  in

  let result = _0_get_rels_body prog [] in
result
;;


(*********************************************
  In: Prog [Rule(Pred(name1, varlst1), bodylst1); ...]
  Out: [name, ...] if predicate is not negated
*********************************************)
let get_rels_body_nonnegate prog =

  let rec _0_get_rels_body prog rels = match prog with
    | Prog sttl -> _1_get_rels_body sttl rels

    and _1_get_rels_body sttl rels = match sttl with
      | [] -> []
      | hd::rest -> (_2_get_rels_body hd rels) @ (_1_get_rels_body rest rels)

    and _2_get_rels_body hd rels = match hd with
      | Rule (Pred(name, varlst), bodylst)          -> _3_get_rels_body bodylst rels
      | Rule (Deltainsert(name, varlst), bodylst)   -> _3_get_rels_body bodylst rels
      | Rule (Deltadelete(name, varlst), bodylst)   -> _3_get_rels_body bodylst rels
      | Rule (Deltainsert_nos(name, varlst), bodylst)   -> _3_get_rels_body bodylst rels
      | Rule (Deltadelete_nos(name, varlst), bodylst)   -> _3_get_rels_body bodylst rels
    | _ -> rels

    and _3_get_rels_body bodylst rels = match bodylst with
      | [] -> []
      | hd::rest -> (_4_get_rels_body hd rels) @ (_3_get_rels_body rest rels)

    and _4_get_rels_body hd rels = match hd with
      | Rel(Pred(name, _)) -> rels @ [name]
      | _ -> rels
  in

  let result = _0_get_rels_body prog [] in
result
;;

(*********************************************
  In: Prog [Rule(Deltainsert(name1, varlst1), bodylst1); ...]
  Out: [name, ...]
*********************************************)
let get_delta_rels_body prog =

  let rec _0_get_rels_body prog rels = match prog with
    | Prog sttl -> _1_get_rels_body sttl rels

    and _1_get_rels_body sttl rels = match sttl with
      | [] -> []
      | hd::rest -> (_2_get_rels_body hd rels) @ (_1_get_rels_body rest rels)

    and _2_get_rels_body hd rels = match hd with
      | Rule (Pred(name, varlst), bodylst)          -> _3_get_rels_body bodylst rels
      | Rule (Deltainsert(name, varlst), bodylst)   -> _3_get_rels_body bodylst rels
      | Rule (Deltadelete(name, varlst), bodylst)   -> _3_get_rels_body bodylst rels
      | Rule (Deltainsert_nos(name, varlst), bodylst)   -> _3_get_rels_body bodylst rels
      | Rule (Deltadelete_nos(name, varlst), bodylst)   -> _3_get_rels_body bodylst rels
      | _ -> rels

    and _3_get_rels_body bodylst rels = match bodylst with
      | [] -> []
      | hd::rest -> (_4_get_rels_body hd rels) @ (_3_get_rels_body rest rels)

    and _4_get_rels_body hd rels = match hd with
      | Rel(Deltainsert(name, _))
      | Rel(Deltadelete(name, _)) -> rels @ [name]
(*    | Not(Deltainsert(name, _)) *)
(*    | Not(Deltadelete(name, _)) *)
      | _ -> rels
  in

  let result = _0_get_rels_body prog [] in
result
;;

(*********************************************
  In: [Rel(Pred(rel, varlst), ....]
  Out: [rel, ...]
*********************************************)
let get_rels_body_tml tml  =

  let rec get tml = match tml with
    | [] -> []
    | hd::rest -> (_1_get hd) @ (get rest)
  and _1_get tm = match tm with
      | Rel(Pred(rel, varlst))
      | Rel(Deltainsert(rel, varlst))
      | Rel(Deltadelete(rel, varlst))
      | Not(Pred(rel, varlst))
      | Not(Deltainsert(rel, varlst))
      | Not(Deltadelete(rel, varlst)) -> [rel]
      | _ -> []
  in

  let result = get tml in
result
;;

(*********************************************
  In: Prog [Rule(Pred(name1, varlst1), bodylst1); ...]
  Out: [Pred(name1), ...]
*********************************************)
let get_preds_head prog =

  let rec get sttl = match sttl with
    | [] -> []
    | hd::rest -> (_1_get hd) @ (get rest)

  and _1_get stt = match stt with
    | Rule (Pred (rel, varlst), _) -> [Pred (rel, varlst)]
    | Rule (Deltainsert (rel, varlst), _) -> [Deltainsert (rel, varlst)]
    | Rule (Deltadelete (rel, varlst), _) -> [Deltadelete (rel, varlst)]
    | Rule (Deltainsert_nos (rel, varlst), _) -> [Deltainsert_nos (rel, varlst)]
    | Rule (Deltadelete_nos (rel, varlst), _) -> [Deltadelete_nos (rel, varlst)]
    | _ -> []
  in

  let result = get (get_sttl prog) in
result
;;


(*********************************************
  In: Prog [Rule(Pred(name1, varlst1), bodylst1); ...]
  Out: [name1, ...]
*********************************************)
let get_rels_head prog =

  let rec _0_get sttl = match sttl with
    | [] -> []
    | hd::rest -> (_1_get hd) @ (_0_get rest)

  and _1_get stt = match stt with
    | Rule (Pred (rel, varlst), _) -> [rel]
    | Rule (Deltainsert (rel, varlst), _) -> [rel]
    | Rule (Deltadelete (rel, varlst), _) -> [rel]
    | _ -> []
  in

  let result = _0_get (get_sttl prog) in
result
;;

(*********************************************
  In: Prog [Rule(Deltainsert(name1, varlst1), bodylst1); ...]
  Out: [name1, ...]
*********************************************)
let get_ins_rels_head prog =

  let rec _0_get sttl = match sttl with
    | [] -> []
    | hd::rest -> (_1_get hd) @ (_0_get rest)

  and _1_get stt = match stt with
    | Rule (Deltainsert (rel, varlst), _) -> [rel]
    | _ -> []
  in

  let result = _0_get (get_sttl prog) in
result
;;

(*********************************************
  In: Prog [Rule(Deltadelete(name1, varlst1), bodylst1); ...]
  Out: [name1, ...]
*********************************************)
let get_del_rels_head prog =

  let rec _0_get sttl = match sttl with
    | [] -> []
    | hd::rest -> (_1_get hd) @ (_0_get rest)

  and _1_get stt = match stt with
    | Rule (Deltadelete (rel, varlst), _) -> [rel]
    | _ -> []
  in

  let result = _0_get (get_sttl prog) in
result
;;

(*********************************************
  In: Prog [Rule(Pred(name1, varlst1), bodylst1); ...]
      name1
  Out: [Rule(Pred(name1, varlst1), bodylst1); Rule(Pred(name3, varlst3), bodylst3);...]
*********************************************)
let get_rules_by_headname ast rel_lst =

  let rec get_rules ast rel_lst = match ast with
    | Prog sttl -> _1_get_rules sttl rel_lst

    and _1_get_rules sttl rel_lst = match sttl with
        | [] -> []
        | hd::rest -> (_2_get_rules hd rel_lst) @ (_1_get_rules rest rel_lst)

    and _2_get_rules hd rel_lst = match hd with
        | Rule (Pred(rel, varlst), bodylst) ->
                  if List.mem rel rel_lst
                  then [Rule (Pred(rel, varlst), bodylst)]
                  else []
        | Rule (Deltainsert(rel, varlst), bodylst) ->
                  if List.mem rel rel_lst
                  then [Rule (Deltainsert(rel, varlst), bodylst)]
                  else []
        | Rule (Deltadelete(rel, varlst), bodylst) ->
                if List.mem rel rel_lst
                then [Rule (Deltadelete(rel, varlst), bodylst)]
                else []

      | _ -> []
  in

  let result = Prog (get_rules ast rel_lst) in
result
;;

(* --------------------------------------------------------
   In: pred_lst = [Pred(rel1, varlst1); [Pred(rel1, varlst1); ...]
       rel_lst = [re1;]
   Out:pred_lst = [Pred(rel1, varlst1);]
--------------------------------------------------------*)
let filter_pred_rellst pred_lst rel_lst =

  let rec filter pred_lst rel_lst = match pred_lst with
    | [] -> []
    | hd::rest -> (_1_filter hd rel_lst) @ (filter rest rel_lst)

    and _1_filter hd rel_lst = match hd with
      | Pred(rel, varlst) ->
          if List.mem rel rel_lst
          then
            [hd]
          else
            []
      | _ -> invalid_arg "function filter_pred_rellstcalled without rterm of pred"
  in

  let result = filter pred_lst rel_lst in
result
;;

(* retrive rel list from body which is in rel_lst *)
let get_rels_inbody prog rel_lst =

    let rec get sttl rel_lst = match sttl with
      | [] -> []
      | hd::rest -> (_1_get hd rel_lst) @ (get rest rel_lst)
      and _1_get stt rel_lst = match stt with
        | Rule (Pred _, bodylst)
        | Rule (Deltainsert _, bodylst)
        | Rule (Deltadelete _, bodylst) -> _2_get bodylst rel_lst
        | _ -> []
      and _2_get bodylst rel_lst = match bodylst with
        | [] -> []
        | hd::rest -> (_3_get hd rel_lst) @ (_2_get rest rel_lst)
      and _3_get tm rel_lst = match tm with
        | Rel (Pred(rel, _))
        | Rel (Deltainsert(rel, _))
        | Rel (Deltadelete(rel, _))
        | Not (Pred(rel, _))
        | Not (Deltainsert(rel, _))
        | Not (Deltadelete(rel, _)) ->
            if List.mem rel rel_lst
              then [rel]
              else []
        | _ -> []
      in

  let result = get (get_sttl prog) rel_lst in
result
;;


(* --------------------------------------------------------
   filter rules by checking rels in body
   In:
     Prog ([
     Rule(Pred(re1, varlst), [Rel(Pred(re12,varlst); Not(Pred(re13,varlst)]));
     Rule(Pred(re1, varlst), [Rel(Pred(re12,varlst)]));
     ],
     rel_lst = [re1; re12;]
   Out:
      Rule(Pred(re1, varlst), [Rel(Pred(re12,varlst)]));
--------------------------------------------------------*)
let filter_rules_body ast rel_lst =

  let rec filter sttl rel_lst = match sttl with
    | [] -> []
    | hd::rest -> (_1_filter hd rel_lst) @ (filter rest rel_lst)

  and _1_filter stt rel_lst = match stt with
    | Rule (Pred(rel, varlst), bodylst)
    | Rule (Deltainsert(rel, varlst), bodylst)
    | Rule (Deltadelete(rel, varlst), bodylst)
    | Rule (Deltainsert_nos(rel, varlst), bodylst)
    | Rule (Deltadelete_nos(rel, varlst), bodylst) ->
      let check = _2_filter bodylst rel_lst in
      if List.length check = 0
        then [stt]
        else []
    | _ -> []

  and _2_filter bodylst rel_lst = match bodylst with
    | [] -> []
    | hd::rest -> (_3_filter hd rel_lst) @ (_2_filter rest rel_lst)

  and _3_filter tm rel_lst = match tm with
    | Rel(Pred(rel, varlst))
    | Rel(Deltainsert(rel, varlst))
    | Rel(Deltadelete(rel, varlst))
    | Not(Pred(rel, varlst))
    | Not(Deltainsert(rel, varlst))
    | Not(Deltadelete(rel, varlst)) ->
        if List.mem rel rel_lst
          then []
          else [tm]
    | _ -> []
  in

  let result = Prog (filter (get_sttl ast) rel_lst) in
result
;;


(*********************************************
  In: Prog [Rule(Pred(name1, varlst1), bodylst1);
             Rule(Pred(name_a, varlst_a), bodylst_a);
           ...; ],
       rel_name
  Out: [Rule(Pred(name1, varlst1), bodylst1);]
       where rterm Deletainsert of rel_name exist in bodylst1
*********************************************)
let get_rules_ins_in_body ast rel =

  let rec get sttl rel = match sttl with
    | [] -> []
    | hd::rest -> (_1_get hd rel) @ (get rest rel)

    and _1_get stt rel = match stt with
      | Rule(rt, tml) ->
          let rel_ins_lst = _2_get tml rel in
            (*
            printf "rel_ins_lst => [";
            let print_el s = printf "%s; " s in
            List.iter print_el rel_ins_lst;
            printf "]\n";
            *)
          if (List.length rel_ins_lst) >=1
            then
              let rel_ins = List.hd rel_ins_lst in
              if rel_ins = rel
                then [stt]
                else []
            else []
      | _ -> []

    and _2_get tml rel = match tml with
      | [] -> []
      | hd::rest -> (_3_get hd rel) @ (_2_get rest rel)

    and _3_get tm rel = match tm with
      | Rel(Deltainsert(rel, varlst)) -> [rel]
      | _ -> []

  in

  let result = Prog (get (get_sttl ast) rel) in
result
;;


(*********************************************
  In: Prog [Rule(Pred(name1, varlst1), bodylst1);
             Rule(Pred(name_a, varlst_a), bodylst_a);
           ...; ],
       rel_name
  Out: [Rule(Pred(name1, varlst1), bodylst1);]
       where rterm Deletadelete of rel_name exist in bodylst1
*********************************************)
let get_rules_del_in_body ast rel =

  let rec get sttl rel = match sttl with
    | [] -> []
    | hd::rest -> (_1_get hd rel) @ (get rest rel)

    and _1_get stt rel = match stt with
      | Rule(rt, tml) ->
        let rel_del_lst = _2_get tml rel in
            (*
            printf "rel_del_lst => [";
            let print_el s = printf "%s; " s in
            List.iter print_el rel_del_lst;
            printf "]\n";
            *)
        if (List.length rel_del_lst) >=1
          then
            let rel_del = List.hd rel_del_lst in
            if rel_del = rel
              then [stt]
            else []
        else []
      | _ -> []

    and _2_get tml rel = match tml with
      | [] -> []
      | hd::rest -> (_3_get hd rel) @ (_2_get rest rel)

    and _3_get tm rel = match tm with
      | Rel(Deltadelete(rel, varlst)) -> [rel]
      | _ -> []

  in

  let result = Prog (get (get_sttl ast) rel) in
result
;;



(*********************************************
  In: AST, predicate of IBD (Pred(name1, varlst1)
  Out: Prog [Rule(Pred(name1, varlst1), bodylst1);
             Rule(Pred(name_a, varlst_a), bodylst_a);
           ...; ]
*********************************************)
let get_one_query ast pred =

  let rec filter ast target_pred = match ast with
    | Prog sttl -> _1_filter sttl target_pred

    and _1_filter sttl target_pred = match sttl with
      | [] -> []
      | hd::rest -> (_2_filter hd target_pred) @ (_1_filter rest target_pred)

    and _2_filter hd target_pred = match hd with
      | Rule (Pred(rel, varlst), b) ->
          if Pred(rel, varlst) = target_pred
          then [Rule (Pred(rel, varlst), b)]
          else []
      | Rule (Deltainsert(rel, varlst), b) ->
          if Deltainsert(rel, varlst) = target_pred
          then [Rule (Deltainsert(rel, varlst), b)]
          else []
      | Rule (Deltadelete(rel, varlst), b) ->
          if Deltadelete(rel, varlst) = target_pred
          then [Rule (Deltadelete(rel, varlst), b)]
          else []
      | Rule (Deltainsert_nos(rel, varlst), b) ->
          if Deltainsert_nos(rel, varlst) = target_pred
          then [Rule (Deltainsert_nos(rel, varlst), b)]
          else []
      | Rule (Deltadelete_nos(rel, varlst), b) ->
          if Deltadelete_nos(rel, varlst) = target_pred
          then [Rule (Deltadelete_nos(rel, varlst), b)]
          else []
      | _ -> []
  in

  let rec get_new_rules ast rel_lst = match ast with
    | Prog sttl -> _1_get_new_rules sttl rel_lst

    and _1_get_new_rules sttl rel_lst = match sttl with
        | [] -> []
        | hd::rest -> (_2_get_new_rules hd rel_lst) @ (_1_get_new_rules rest rel_lst)

    and _2_get_new_rules hd rel_lst = match hd with
        | Rule (Pred(rel, varlst), bodylst) ->
                    (*
                    printf "rel_lst => [";
                    let e = printf "%s; " in
                    List.iter e rel_lst;
                    printf "]\n";

                    printf "Rule => %s\n" (string_of_stt hd);
                    *)
                  if List.mem rel rel_lst
                  then [Rule (Pred(rel, varlst), bodylst)]
                  else []
        | _ -> []
  in

  let rec query ast rules body_rels =
      let new_rules = get_new_rules ast body_rels in
          (*
          printf "new_rules => [";
          print_sttlst new_rules;
          printf "]\n";
          *)
      let new_body_rels = unique_element (get_rels_body (Prog (new_rules))) in
      let total_rules = Prog (unique_element ((Expr.get_sttl rules) @ new_rules)) in

      (*
        print_endline "new_rules : "; Expr.print_ast (Prog(new_rules)); printf "\n";

        printf "new_body_rels => [";
        let print_el s = printf "%s; " s in
        List.iter print_el new_body_rels;
        printf "]\n\n";

        print_endline "total_rules : "; Expr.print_ast total_rules; printf "\n";
      *)

      if List.length new_rules == 0
      then
        total_rules
      else
        query ast total_rules new_body_rels
  in

  let init_rules = Prog (filter ast pred) in
    (* print_endline "get_one_query.init_rules:"; Expr.print_ast init_rules; printf "\n"; *)
  let init_body_rels = get_rels_body init_rules in
    (* printf "get_one_query.init_body_rels => [";
    let print_el s = printf "%s; " s in
    List.iter print_el init_body_rels; printf "]\n"; *)
  let result = query ast init_rules init_body_rels in
result
;;


(* input: AST, rel_lst for rule head *)
let get_queries prog head_rel_lst =

  let rec get sttl prog rel_lst = match sttl with
    | [] -> []
    | hd::rest -> (_1_get hd prog rel_lst) @ (get rest prog rel_lst)

    and _1_get stt prog rel_lst = match stt with
      | Rule (Pred(rel, varlst), bodylst) ->
          if List.mem rel rel_lst
            then [get_one_query prog (Pred(rel, varlst))]
            else [Prog []]
      | Rule (Deltainsert(rel, varlst), bodylst) ->
          if List.mem rel rel_lst
            then [get_one_query prog (Deltainsert(rel, varlst))]
            else [Prog []]
      | Rule (Deltadelete(rel, varlst), bodylst) ->
          if List.mem rel rel_lst
            then [get_one_query prog (Deltadelete(rel, varlst))]
            else [Prog []]
      | _ -> [Prog []]
  in

  let ast_rules = get (get_sttl prog) prog head_rel_lst in
  let ast_rules_sttl = List.map get_sttl ast_rules in
  let result = Prog (unique_element (List.fold_left List.append [] ast_rules_sttl) ) in

result
;;




(* get relname list of insertion delta relations in rules of backward propgation *)
let rec get_bwd_ins_lst prog =

  let rec _0_get_bwd_ins_lst prog = match prog with
      | Prog sttl -> _1_get_bwd_ins_lst sttl
      and _1_get_bwd_ins_lst sttl = match sttl with
        | [] -> []
        | hd::rest -> (_2_get_bwd_ins_lst hd) @ (_1_get_bwd_ins_lst rest)
      and _2_get_bwd_ins_lst hd = match hd with
        | Rule (Pred(rel, varlst), bodylst) -> _3_get_bwd_ins_lst bodylst
        | Rule (Deltainsert(rel, varlst), bodylst) -> [rel] @ (_3_get_bwd_ins_lst bodylst)
        | _ -> []
      and _3_get_bwd_ins_lst bodylst = match bodylst with
        | [] -> []
        | hd::rest -> (_4_get_bwd_ins_lst hd) @ (_3_get_bwd_ins_lst rest)
      and _4_get_bwd_ins_lst hd = match hd with
        | Rel(Deltainsert(rel,_)) -> [rel]
        | Not(Deltainsert(rel,_)) -> [rel]
        | _ -> []
    in

  let result = _0_get_bwd_ins_lst prog in
result
;;

(* get relname list of deletion delta relations in rules of backward propgation *)
let rec get_bwd_del_lst prog =

  let rec _0_get_bwd_del_lst prog = match prog with
      | Prog sttl -> _1_get_bwd_del_lst sttl
      and _1_get_bwd_del_lst sttl = match sttl with
        | [] -> []
        | hd::rest -> (_2_get_bwd_del_lst hd) @ (_1_get_bwd_del_lst rest)
      and _2_get_bwd_del_lst hd = match hd with
        | Rule (Pred(rel, varlst), bodylst) -> _3_get_bwd_del_lst bodylst
        | Rule (Deltadelete(rel, varlst), bodylst) -> [rel] @ (_3_get_bwd_del_lst bodylst)
        | _ -> []
      and _3_get_bwd_del_lst bodylst = match bodylst with
        | [] -> []
        | hd::rest -> (_4_get_bwd_del_lst hd) @ (_3_get_bwd_del_lst rest)
      and _4_get_bwd_del_lst hd = match hd with
        | Rel(Deltadelete(rel,_)) -> [rel]
        | Not(Deltadelete(rel,_)) -> [rel]
        | _ -> []
    in

  let result = _0_get_bwd_del_lst prog in
result
;;

(* get relname list of insertion delta relations in rules of constraint *)
let rec get_const_ins_lst prog =

  let rec _0_get_const_ins_lst prog = match prog with
      | Prog sttl -> _1_get_const_ins_lst sttl
      and _1_get_const_ins_lst sttl = match sttl with
        | [] -> []
        | hd::rest -> (_2_get_const_ins_lst hd) @ (_1_get_const_ins_lst rest)
      and _2_get_const_ins_lst hd = match hd with
        | Rule (Pred(rel, varlst), bodylst) -> _3_get_const_ins_lst bodylst
        | _ -> []
      and _3_get_const_ins_lst bodylst = match bodylst with
        | [] -> []
        | hd::rest -> (_4_get_const_ins_lst hd) @ (_3_get_const_ins_lst rest)
      and _4_get_const_ins_lst hd = match hd with
        | Rel(Deltainsert(rel,_)) -> [rel]
        | Not(Deltainsert(rel,_)) -> [rel]
        | _ -> []
    in

  let result = _0_get_const_ins_lst prog in
result
;;

(* get relname list of deletion delta relations in rules of constraint *)
let rec get_const_del_lst prog =

  let rec _0_get_const_del_lst prog = match prog with
      | Prog sttl -> _1_get_const_del_lst sttl
      and _1_get_const_del_lst sttl = match sttl with
        | [] -> []
        | hd::rest -> (_2_get_const_del_lst hd) @ (_1_get_const_del_lst rest)
      and _2_get_const_del_lst hd = match hd with
        | Rule (Pred(rel, varlst), bodylst) -> _3_get_const_del_lst bodylst
        | _ -> []
      and _3_get_const_del_lst bodylst = match bodylst with
        | [] -> []
        | hd::rest -> (_4_get_const_del_lst hd) @ (_3_get_const_del_lst rest)
      and _4_get_const_del_lst hd = match hd with
        | Rel(Deltadelete(rel,_)) -> [rel]
        | Not(Deltadelete(rel,_)) -> [rel]
        | _ -> []
    in

  let result = _0_get_const_del_lst prog in
result
;;


(* filter backward rules corresponding to one schema evolution *)
let filter_bwd ast_bwd target_pred =

  let rec bwd_rules ast_bwd target_rel = match ast_bwd with
    | Prog sttl -> _1_bwd_rules sttl target_rel
    and _1_bwd_rules sttl target_rel = match sttl with
      | [] -> []
      | hd::rest -> (_2_bwd_rules hd target_rel) @ (_1_bwd_rules rest target_rel )
    and _2_bwd_rules stt target_rel = match stt with
      | Rule (Deltainsert(rel, varlst), bodylst ) ->
          let flg_lst = _3_bwd_rules bodylst target_rel in
          if List.length flg_lst != 0
              then [Deltainsert(rel, varlst)]
              else []
      | Rule (Deltadelete(rel_del, varlst_del), bodylst_del ) ->
          let flg_lst = _3_bwd_rules bodylst_del target_rel in
          if List.length flg_lst != 0
              then [Deltadelete(rel_del, varlst_del)]
              else []
      | _ -> []
    and _3_bwd_rules bodylst target_rel = match bodylst with
      | [] -> []
      | hd::rest -> (_4_bwd_rules hd target_rel) @ (_3_bwd_rules rest target_rel)
    and _4_bwd_rules tm target_rel = match tm with
      | Rel(Deltainsert(rel, varlst))
      | Rel(Deltadelete(rel, varlst))
      | Not(Deltainsert(rel, varlst))
      | Not(Deltadelete(rel, varlst))
          -> if rel = target_rel
              then [rel]
              else []
      | _ -> []
  in

  let rec query_bwd ast_bwd bwd_rule_lst = match bwd_rule_lst with
    | [] -> []
    | hd::rest -> (_1_query_bwd ast_bwd hd) @ (query_bwd ast_bwd rest)
    and _1_query_bwd ast_bwd stt =
      [get_one_query ast_bwd stt]
  in

  let target_rel = get_rel_from_pred target_pred in
  let bwd_head_lst = bwd_rules ast_bwd target_rel in
  let bwd_query_lst = query_bwd ast_bwd bwd_head_lst in
  let result_tmp = List.fold_left merge_ast (Prog []) bwd_query_lst in
  let result = Prog (unique_element (get_sttl result_tmp)) in

result
;;


(*********************************************
  In: Prog [Source_schema (sch, rel, valst); Target_schema(sch, rel, varlst); ... ]
  In: Prog [Source(rel, valst); View(sch, rel, varlst); ... ]
*********************************************)
let schema2schema ast_schema =

  let rec map ast_schema = match ast_schema with
  | Prog sttl -> _1_map sttl
  and _1_map sttl = match sttl with
    | [] -> []
    | hd::rest -> (_2_map hd) @ (_1_map rest)
  and _2_map st = match st with
    | Source_schema (_, rel, varlst) -> [Source(rel, varlst)]
    | Target_schema (_, rel, varlst) -> [View(rel, varlst)]
    | _ -> []
  in

  let schema_birds = Prog (map ast_schema) in
schema_birds
;;


(* filter pk_lst by rel *)
let rec filter_pk ast_constraint_pk rel =

  let rec filter sttl rel = match sttl with
    | [] -> []
    | hd::rest -> (_1_filter hd rel) @ (filter rest rel)

    and _1_filter stt rel = match stt with
      | Rule(get_empty_pred, bodylst) ->
        let body_rel = List.hd (_2_filter @@ List.hd bodylst) in
        if body_rel = rel
          then [stt]
          else []
      | _ -> []

    and _2_filter tm = match tm with
      | Rel(Pred(rel, var)) -> [rel]
      | _ -> [""]

  in

  let result = Prog( filter (get_sttl ast_constraint_pk) rel) in
result
;;

(* --- transfrom non-shared ast to shared ast ----------------------- *)
let nos2s ast =

  let rec transform sttl = match sttl with
    | [] -> []
    | hd::rest -> (_1_transform hd) @ (transform rest)

    and _1_transform stt = match stt with
      | Rule (Deltainsert_nos(rel, varlst), tml) ->
          [Rule (Deltainsert(rel, varlst), tml)]
      | Rule (Deltadelete_nos(rel, varlst), tml) ->
          [Rule (Deltadelete(rel, varlst), tml)]
      | _ -> [stt]
  in

  let ast_shared = Prog (transform (get_sttl ast)) in
ast_shared
;;

(***********************************************************
 *  SQL
 *********************************************************)
(* string of (schema, rel) mapping *)
let rec string_of_mpg lst = match lst with
 | [] -> ""
 | hd::rest -> "(" ^ (fst hd) ^ "," ^ (snd hd) ^ "); " ^ (string_of_mpg rest)
;;

let rec schema_mpg_lst dbschema lst = match lst with
| [] -> []
| hd::rest -> [ ( !dbschema ^ "." ^ (snd hd),  (fst hd) ^ "." ^ (snd hd) )
              ]  @ (schema_mpg_lst dbschema rest)
;;

let rec rep_schemas sql_str obj_tmpl_lst = match obj_tmpl_lst with
  | [] -> sql_str
  | hd::rest ->
        let obj = fst hd in
        let templ = snd hd in
        let sql_str_new = replace_string obj templ sql_str in
        rep_schemas sql_str_new rest
;;


(* --- apply schema mapping (schema version, rel_name) ---*)
let rewrite_sql_schemas log dbschema schema_mpg sql_file=
    (* read sql *)
    let ch = open_in sql_file in
    let sql_str = really_input_string ch (in_channel_length ch) in
    close_in ch;

    (* make schema mapping list *)
    let obj_tmpl_lst = schema_mpg_lst dbschema schema_mpg in
      (*
      printf "[%s" (string_of_mpg obj_tmpl_lst);
      printf "]\n";
      *)

    (* replace schemas in sql file *)
    let sql_str_schemas = rep_schemas sql_str obj_tmpl_lst in

    (* output to a file *)
    let oc = open_out sql_file in
    output_string oc sql_str_schemas;
    close_out oc;
;;

(* Execute birds and generate SQL file for each init relations *)
let execute_birds ast_lst log dbschema verification =

  let rec execute ast_lst dbschema = match ast_lst with
    | [] -> []
    | hd::rest -> (_1_execute hd dbschema) @ (execute rest dbschema)

    and _1_execute ast dbschema =
      let view = get_view_name ast in
      let dl_file = view ^ ".dl" in
      let sql_file = view ^ ".sql" in
      let ast_str = string_of_prog ast in

      (* output to Datalog prograom into a file *)
      let oc = open_out dl_file in
      output_string oc ast_str;
      close_out oc;

      (* execute BIRDS *)
      let cmd =
        if verification
          then "birds" ^ " -s " ^ !dbschema ^ " -f " ^ dl_file ^ " -o " ^ sql_file ^ " -v"
          else "birds" ^ " -s " ^ !dbschema ^ " -f " ^ dl_file ^ " -o " ^ sql_file
      in

      let status = exe_command2 cmd in

      if (status != 0)
        then begin
            print_endline "BIRDS validation: failed";
            let uni = Sys.command ("rm " ^ sql_file) in
            [(status, "")]
        end
        else begin
            printf "BIRDS validation: success";
            [(status, sql_file)]
        end

  in

(* (Sys.file_exists sql_file) *)
  let result = execute ast_lst dbschema in
result
;;
