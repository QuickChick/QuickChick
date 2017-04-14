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


let semGenSize gen size =
  gApp (gInject "semGenSize") [gen; size]

let arbitrarySize size =
  gApp (gInject "arbitrarySize") [size]

let oneOf_freq p1 p2 p3 =
  gApp (gInject "oneOf_freq") [p1; p2; p3]

let semFreqSize g gs size =
  gApp (gInject "semFreqSize") [g; gs; size]

let semBindSize g f size =
  gApp (gInject "semBindSize") [g; f; size]

let backtrackSizeMonotonic lst proof =
  gApp (gInject "backtrackSizeMonotonic") [lst; proof]

let returnGenSizeMonotonic x =
  gApp (gInject "returnGenSizeMonotonic") [x]

let bindMonotonic p s fp =
  gApp ~explicit:true
    (gInject "bindMonotonic") [hole; hole; hole; hole; p; gFun [s] (fun [x] -> fp x)]

let bindOptMonotonic p s fp =
  gApp ~explicit:true
    (gInject "bindOptMonotonic") [hole; hole; hole; hole; p; gFun [s] (fun [x] -> fp x)]

let suchThatMaybeMonotonic p pred =
  gApp ~explicit:true
    (gInject "suchThatMaybeMonotonic") [hole; hole; pred; p]

let suchThatMaybeOptMonotonic p pred =
  gApp ~explicit:true
    (gInject "suchThatMaybeOptMonotonic") [hole; hole; pred; p]
