(* @author: Jumpei Tanaka *)
(* ************************************************ *)
(* Checking disjointness                            *)
(* ************************************************ *)

open Expr;;
open Utils;;
open Tools;;
open Printf;;
open Satisfiability;;

let check_disjoint prep_disjoint_lst log timeout =

  let rec check prep_disjoint_lst log timeout = match prep_disjoint_lst with
    | [] -> []
    | hd::rest -> (_1_check hd log timeout) @ (check rest log timeout)

    and _1_check sttl log timeout =
      let ins_target = List.hd (get_view sttl) in

      (* generate lean code to check disjointness *)
      let disdelta_thm = lean_simp_theorem_of_disjoint_delta log (Prog(sttl)) in
      printf "disdelta_thm => \n%s\n" disdelta_thm;

      let is_disjoint, msg = Utils.verify_fo_lean !log !timeout disdelta_thm in
          (* is_consistency = 0 means satisfying consistency , 1 is not *)
          if !log then begin printf "disjointness = %d\n" is_disjoint; end
          else ();

      if is_disjoint != 0
      then begin
        let result = "Disjointness is not satisfied for rules of: " ^ ins_target in
        [result]
      end
      else
        []

  and get_view sttl = match sttl with
    | [] -> []
    | hd::rest -> (_1_get_view hd) @ (get_view rest)
    and _1_get_view stt = match stt with
      | View (rel, varlst) -> [rel]
      | _ -> []
in

  let result = check prep_disjoint_lst log timeout in

result
;;

(*
  let disdelta_thm = lean_simp_theorem_of_disjoint_delta (debug) prog in
*)
