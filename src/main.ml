(* @author: Jumpei Tanaka *)

(* open Lib;; *)
open Lexer;;
open Printf;;
open Utils;;
open Expr;;
open Framework;;
open Filename;;


(** check for options of command line*)
(*default values*)
let print_version = ref false;;
let physical = ref "phy";;
let inputf = ref "";;
let outputf = ref "";;
let log = ref false;;

(* Not given as option *)
let timeout = ref 180;;
let dbschema = ref "public";;


(* Handle commad line arguments *)
let usage = "usage: " ^ Sys.argv.(0) ^ " [OPTIONS]"
let speclist = [
  ("-s", Arg.String (fun s -> physical := s),             "Input schema name for base and aux tables, if not chosen, phy");
  ("-f", Arg.String (fun s -> inputf := s),                  "<file> Input program file, if not chosen, read from stdin");
  ("-o", Arg.String (fun s -> outputf := s),                 "<file> Output result file for cm mode, if not chosen, print to stdout");
  ("-log", Arg.Unit (fun () -> log := true),                 " Print running inofrmation");
  ("-version", Arg.Unit (fun () -> print_version := true),   " Print version");
];;

let () =
  (* Read the arguments *)
  Arg.parse
    (Arg.align speclist)
    (fun x ->
       raise (Arg.Bad ("Bad argument : " ^ x))
    )
    usage;
;;


(* ============================================================================================= *)
(* main function *)
let main () =
  (* show program version *)
  if (!print_version) then (
                            print_endline "COXS version 0.2.2";
                            exit 0);

  (* read from a file and put into AST *)
  let chan = if !inputf = "" then stdin else open_in !inputf in (* close_in?*)
  let lexbuf = Lexing.from_channel chan in

  (* while true do *)
  try

    (* create AST from a input file *)
    let ast0 = Parser.main Lexer.token lexbuf in

    (* Overall derivation framework *)
    Framework.steps ast0 log timeout dbschema physical;

    exit 0;

  with
    SemErr exp -> print_endline ("Semantic error: "^exp)
  | ChkErr exp -> print_endline ("Invalidity: "^exp)
  | Parsing.Parse_error ->  print_endline "Syntax error"
  | LexErr msg -> print_endline (msg^":\nError: Illegal characters")
  | ParseErr msg -> print_endline (msg^":\nError: Syntax error")

;;

let _ = main();;
;;
