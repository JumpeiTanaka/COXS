(* @author: Jumpei Tanaka *)

(* open Lib;; *)
open Printf;;
open Expr;;
open Utils;;
open Tools;;

type calc =
  | Frule of formula
and formula =
  | Atom of term
  | Nnot of formula
  | And of formula list
  | Or  of formula list
;;

(**************************************************************************
  DNF (Disjunction Normal Form)

  DNF = (L11 ∧ L12 ∧ ...) ∨ (L21 ∧ L22 ∧ ...) ∨ ....
         --
         literal
         ----------------
         clause
         (literal disjunction)

  (Example)
    Do([
       Da([Dneg("L11"); Dpos("L12")]);
       Da([Dpos("L21"); Dneg("L22"); Dpos("L23")])
      ])
 **************************************************************************)
type dcalc =
  | Drule of dnf
and dnf =
  | Do of dclause list
and dclause =
  | Da of dliteral list
and dliteral =
  | Dpos of term (* literal is Pos("P"), Atom is Atom("p") *)
  | Dneg of term (* literal is Neg("P"), Atom is Nnot(Atom("p")) *)
;;


(**************************************************************************
 Functions
 **************************************************************************)

(* -----------------------------------------------------------------------
  Transform to NNF (Negation Normal Form)
  ¬(¬A) ≡ A
  ¬(A ∧ B) ≡ (¬A) ∨ (¬B)
  ¬(A ∨ B) ≡ (¬A) ∧ (¬B)
 ------------------------------------------------------------------------*)

let rec to_nnf (r : calc) : calc = match r with
  | Frule (fr) -> Frule (_1_to_nnf fr)

  and _1_to_nnf fr = match fr with
        | Atom(_)             -> fr (* Already NNF *)
        | Nnot (Atom(_))      -> fr (* Already NNF *)
        | Nnot (Nnot (fr2))   -> _1_to_nnf fr2 (* ¬(¬A)≡A *)
        | Nnot (And(flst))    -> Or(_2_to_nnf flst) (* ¬(A∧B)≡(¬A)∨(¬B) *)
        | Nnot (Or(flst))     -> And(_2_to_nnf flst) (* ¬(A∨B)≡(¬A)∧(¬B) *)
        | And(flst)           -> And(_3_to_nnf flst)
        | Or(flst)            -> Or(_3_to_nnf flst)

  and _2_to_nnf flst = match flst with
        | [] -> []
        | hd::rest -> [_1_to_nnf (Nnot (hd))] @ _2_to_nnf rest

  and _3_to_nnf flst = match flst with
        | [] -> []
        | hd::rest -> [_1_to_nnf hd] @ _3_to_nnf rest
;;


(* -----------------------------------------------------------------------
  Transform NNF (Negation Normal Form) to DNF (Disjunctive Normal Form)
   Distribution law
   (A ∨ B) ∧ C ≡ (A ∧ C) ∨ (B ∧ C)
   (A ∨ B) ∧ (C ∨ D) ≡ (A ∧ C) ∨ (B ∧ C) ∨ (A ∧ D) ∨ (B ∧ D)
   (A1 ∨ A2 ∨ ... ∨ Am ) ∧ (B1 ∨ B2 ∨ ... ∨ Bm) ≡ ∨(1≤i≤m),(1≤j≤n) (Ai ∧ Bj)
 ------------------------------------------------------------------------*)

let rec distribution2 dla1 dla2 = match dla1 with
  | [] -> []
  | d1::rest -> (_distribution2 d1 dla2) @ (distribution2 rest dla2)
  and _distribution2 d1 dla2 = match d1 with
          | Da(l_lst1) -> __distribution2 l_lst1 dla2
  and __distribution2 l_lst1 dla2 = match dla2 with
        | [] -> []
        | d2::rest -> (___distribution2 l_lst1 d2) @ (__distribution2 l_lst1 rest)
  and ___distribution2 l_lst1 d2 = match d2 with
        | Da(l_lst2) -> [Da( l_lst1@l_lst2 )]
;;

let rec to_dnf (r : calc) : dcalc = match r with
  | Frule (fr) -> Drule (_1_to_dnf fr)

  and _1_to_dnf fr = match fr with
      | Atom(p)        -> Do ([ Da[Dpos(p)] ])
      | Nnot (Atom(p)) -> Do ([ Da[Dneg(p)] ])
      | Or(flst)       -> Do (_3_to_dnf @@ _2_to_dnf flst)
      | And(flst)      -> distribution flst
      | _ -> failwith "This case cannot happen" (* Return error if input is not NNF *)

  and _2_to_dnf flst = match flst with
        | [] -> []
        | hd::rest -> [_1_to_dnf hd] @ _2_to_dnf rest

  and _3_to_dnf do_lst = match do_lst with
      | [] -> []
      | hd::rest -> (_4_to_dnf hd) @ (_3_to_dnf rest)

  and _4_to_dnf hd = match hd with
      | Do(dlst) -> dlst

  and distribution flst = match flst with
    | hd::rest -> let dnf1 = _1_to_dnf hd in
                  _distribution dnf1 rest
    | _-> failwith "This case cannot happen" (* Return error if input is not NNF *)

  and _distribution dnf1 rest = match rest with
    | [] -> dnf1
    | hd2::rest2 -> let dnf2 = _1_to_dnf hd2 in
                    begin match (dnf1, dnf2) with
                       | (Do(dl1), Do(dl2)) -> _distribution (Do(distribution2 dl1 dl2)) rest2
                    end
;;
