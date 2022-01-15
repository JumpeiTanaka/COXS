(* @author: Jumpei Tanaka *)

(* open Lib;; *)
open Printf;;
open Expr;;
open Utils;;
open Tools;;
open Preperation;;
open Disjoint;;
open Consistency;;

let check ast0 log timeout dbschema physical tar =
  (* ************************************************ *)
  (* Step 0: Check # of rels in taregt schema         *)
  (* ************************************************ *)

  let target_rels = unique_element @@ get_rels @@ Utils.get_target_rterms ast0 in

  if List.length target_rels >= 3
  then begin
    print_endline "Error: A strategy defines more than three relations in target schema.";
    exit 0
    end
  else if List.length target_rels = 2
    then begin
      print_endline "target_rels = 2";
      Framework2.steps ast0 log timeout dbschema physical
    end
    else begin
      print_endline "target_rels = 1";
      if !tar
        then  Framework_tar.steps ast0 log timeout dbschema physical
        else  Framework1.steps ast0 log timeout dbschema physical
    end
;;
