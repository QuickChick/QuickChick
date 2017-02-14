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
