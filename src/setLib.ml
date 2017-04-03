open Decl_kinds
open Pp
open Term
open Loc
open Names
open Tacmach
open Entries
open Declarations
open Declare
open Libnames
open Util
open Constrintern
open Topconstr
open Constrexpr
open Constrexpr_ops
open Ppconstr
open Context
open GenericLib

let set_singleton (c : coq_expr) : coq_expr = gApp (gInject "set1") [c]

let set_bigcup (x : string) (p : coq_expr) (c : var -> coq_expr) : coq_expr =
  gApp (gInject "bigcup") [p; gFun [x] (fun [x] -> c x)]

let set_suchThat (x : string) (t : coq_expr) (p : var -> coq_expr) : coq_expr =
  gFunTyped [("x", t)] (fun [x] -> p x)

let set_eq c1 c2 = gApp (gInject "set_eq") [c1;c2]

let set_incl c1 c2 = gApp (gInject "set_incl") [c1;c2]

let set_union c1 c2 = gApp (gInject "setU") [c1;c2]

let rec set_unions = function
  | [] -> failwith "empty set unions"
  | [x] -> x
  | x::xs -> set_union x (set_unions xs)

let set_eq_refl x =
  gApp (gInject "set_eq_refl") [x]

let set_incl_refl =
  gApp ~explicit:true (gInject "subset_refl") [hole; hole]

let incl_subset l1 l2 p =
  gApp (gInject "incl_subset") [l1; l2; p]

let incl_refl =
  gApp (gInject "incl_refl") [hole]

let incl_hd_same p =
  gApp ~explicit:true (gInject "incl_hd_same") [hole; hole; hole; hole; p]

let incl_tl p =
  gApp (gInject "incl_tl") [hole; p]

let setU_set_eq_compat x1 x2 =
  gApp (gInject "setU_set_eq_compat") [x1; x2]

let setU_set0_r x1 x2 =
  gApp (gInject "setU_set0_r") [x1; x2]

let set_eq_trans x1 x2 =
  gApp (gInject "set_eq_trans") [x1; x2]

let setU_set0_l x1 x2 =
  gApp (gInject "setU_set0_l") [x1; x2]

let setU_set0_neut_eq x1 x2 =
  gApp (gInject "setU_set0_neut_eq") [x1; x2]

let eq_bigcupl x1 x2 p = gApp (gInject "eq_bigcupl") [x1; x2; p]

let cons_set_eq x l = gApp (gInject "cons_set_eq") [x; l]

let singl_set_eq a x = gApp ~explicit:true (gInject "singl_set_eq") [a; x]

let bigcup_setU_l x1 x2 x3 = gApp (gInject "bigcup_setU_l") [x1; x2; x3]

let bigcup_set1 x1 x2 = gApp (gInject "bigcup_set1") [x1 ; x2]

let subset_respects_set_eq_l p1 p2 =
  gApp (gInject "subset_respects_set_eq_l") [p1; p2]

let subset_respects_set_eq_r p1 p2 =
  gApp (gInject "subset_respects_set_eq_r") [p1; p2]

(* maybe add a new lemma? *)
let subset_set_eq_compat p1 p2 p3 =
  gApp (gInject "subset_respects_set_eq") [p1; p2; p3]

let incl_bigcupl p =
  gApp (gInject "incl_bigcupl") [p]

let incl_bigcup_compat p1 p2 =
  gApp (gInject "incl_bigcup_compat") [p1; p2]

let incl_subset l1 l2 p =
  gApp ~explicit:true (gInject "incl_subset") [hole; l1; l2; p]

let setU_set_subset_compat p1 p2 =
  gApp (gInject "setU_set_subset_compat") [p1; p2]
