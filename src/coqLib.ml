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

let gExIntro_impl (witness : coq_expr) (proof : coq_expr) : coq_expr =
  gApp (gInject "ex_intro") [hole; witness; proof]

let gExIntro (x : string) (pred : var -> coq_expr) (witness : coq_expr) (proof : coq_expr) : coq_expr =
  gApp (gInject "ex_intro") [(gFun [x] (fun [x] -> pred x)); witness; proof]

let gEx (x : string) (pred : var -> coq_expr) : coq_expr =
  gApp (gInject "ex") [(gFun [x] (fun [x] -> pred x))]

let gConjIntro p1 p2 =
  gApp (gInject "conj") [p1; p2]

let gEqType e1 e2 =
  gApp (gInject "eq") [e1; e2]

let gConj p1 p2 =
  gApp (gInject "and") [p1; p2]

let gImpl p1 p2 =
  gApp (gInject "Basics.impl") [p1; p2]

let gForall typ f =
  gApp (gInject "all") [typ; f]

let gProd e1 e2 =
  gApp (gInject "prod") [e1; e2]

let gLeq e1 e2 =
  gApp (gInject "leq") [e1; e2]

let gIsTrueLeq e1 e2 =
  gApp
    (gInject "is_true")
    [gApp (gInject "leq") [e1; e2]]

let gOrIntroL p =
  gApp (gInject "or_introl") [p]

let gOrIntroR p =
  gApp (gInject "or_intror") [p]

let gEqRefl p =
  gApp (gInject "Logic.eq_refl") [p]

let gI = gInject "I"

let gT = gInject "True"

let gIff p1 p2 =
  gApp (gInject "iff") [p1; p2]

let gIsTrueTrue =
  gApp (gInject "is_true") [gInject "true"]

let false_ind x1 x2 =
  gApp (gInject "False_ind") [x1; x2]

let gfalse = gInject "False"

(* TODO extend gMatch to write the return type? *)
let discriminate h =
  false_ind hole
    (gMatch h [(injectCtr "erefl", [], fun [] -> gI)])

let lt0_False hlt =
  gApp (gInject "lt0_False") [hlt]

let nat_ind ret_type base_case ind_case =
  gApp (gInject "nat_ind") [ret_type; base_case; ind_case]

let appn fn n arg =
  gApp (gInject "appn") [fn; n; arg]
