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
open Feedback
open GenericLib

(* Gen combinators *)
let gGen c = gApp (gInject "G") [c]

let returnGen c = gApp (gInject "returnGen") [c]
let bindGen cg xn cf = 
  gApp (gInject "bindGen") [cg; gFun [xn] (fun [x] -> cf x)]

let bindGenOpt cg xn cf = 
  gApp (gInject "bindGenOpt") [cg; gFun [xn] (fun [x] -> cf x)]

let oneof l =
  match l with
  | [] -> failwith "oneof used with empty list"
  | [c] -> c
  | c::cs -> gApp (gInject "oneof") [c; gList l]
       
let frequency l =
  match l with
  | [] -> failwith "frequency used with empty list"
  | [(_,c)] -> c
  | (_,c)::cs -> gApp (gInject "frequency") [c; gList (List.map gPair l)]

let backtracking l = gApp (gInject "backtrack") [gList (List.map gPair l)]
let uniform_backtracking l = backtracking (List.combine (List.map (fun _ -> gInt 1) l) l)
