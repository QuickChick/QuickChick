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

let semGen gen =
  gApp (gInject "semGen") [gen]

let semReturn x =
  gApp (gInject "semReturn") [x]


let arbitrarySize size =
  gApp (gInject "arbitrarySize") [size]

let oneOf_freq p1 p2 p3 =
  gApp (gInject "oneOf_freq") [p1; p2; p3]

let semFreqSize g gs size =
  gApp (gInject "semFreqSize") [g; gs; size]

let semBindSize g f size =
  gApp (gInject "semBindSize") [g; f; size]

let semBindSizeMon g f gMon fMon =
  gApp
    ~explicit:true
    (gInject "semBindSizeMonotonic")
    [hole; hole; g; f; gMon; fMon]


let backtrackSizeMonotonic lst proof =
  gApp (gInject "backtrackSizeMonotonic") [lst; proof]

let backtrackSizeMonotonicOpt lst proof =
  gApp (gInject "backtrackSizeMonotonicOpt") [lst; proof]


let semBacktrack g =
  gApp (gInject "semBacktrack") [hole; g]

let returnGenSizeMonotonic x =
  gApp (gInject "returnGenSizeMonotonic") [x]

let returnGenSizeMonotonicOpt x =
  gApp (gInject "returnGenSizeMonotonicOpt") [x]

let bindMonotonic p s fp =
  gApp ~explicit:true
    (gInject "bindMonotonic") [hole; hole; hole; hole; p; gFun [s] (fun [x] -> fp x)]

let bindMonotonicOpt p s fp =
  gApp ~explicit:true
    (gInject "bindMonotonicOpt") [hole; hole; hole; hole; p; gFun [s] (fun [x] -> fp x)]

let bindOptMonotonic p s fp =
  gApp ~explicit:true
    (gInject "bindOptMonotonic") [hole; hole; hole; hole; p; gFun [s] (fun [x] -> fp x)]

let bindOptMonotonicOpt p s fp =
  gApp ~explicit:true
    (gInject "bindOptMonotonicOpt") [hole; hole; hole; hole; p; gFun [s] (fun [x] -> fp x)]

let suchThatMaybeMonotonic p pred =
  gApp ~explicit:true
    (gInject "suchThatMaybeMonotonic") [hole; hole; pred; p]

let suchThatMaybeOptMonotonic p pred =
  gApp ~explicit:true
    (gInject "suchThatMaybeOptMonotonic") [hole; hole; pred; p]

let suchThatMaybeMonotonicOpt p pred =
  gApp ~explicit:true
    (gInject "suchThatMaybeMonotonicOpt") [hole; hole; pred; p]

let suchThatMaybeOptMonotonicOpt p pred =
  gApp ~explicit:true
    (gInject "suchThatMaybeOptMonotonicOpt") [hole; hole; pred; p]

let semBindOptSizeMonotonicIncl_r g f s sf hg hf =
  gApp ~explicit:true (gInject "semBindOptSizeMonotonicIncl_r")
    [hole; hole; g; f; s; sf; hg; hf]

let semBindSizeMonotonicIncl_r g f s sf hg hf =
  gApp ~explicit:true (gInject "semBindSizeMonotonicIncl_r")
    [hole; hole; g; f; s; sf; hg; hf]

let semBindOptSizeMonotonicIncl_l g f s sf mon monf hg hf =
  gApp ~explicit:true (gInject "semBindOptSizeMonotonicIncl_l")
    [hole; hole; g; f; s; sf; mon; monf; hg; hf]

let semBindSizeMonotonicIncl_l g f s sf mon monf hg hf =
  gApp ~explicit:true (gInject "semBindSizeMonotonicIncl_l")
    [hole; hole; g; f; s; sf; mon; monf; hg; hf]

let semSuchThatMaybe_complete g f s h =
  gApp ~explicit:true (gInject "semSuchThatMaybe_complete") [hole; g; f; s; h]

let semSuchThatMaybeOpt_complete g f s h =
  gApp ~explicit:true (gInject "semSuchThatMaybeOpt_complete") [hole; g; f; s; h]

let semSuchThatMaybe_sound g f s h =
  gApp ~explicit:true (gInject "semSuchThatMaybe_sound") [hole; g; f; s; h]

let semSuchThatMaybeOpt_sound g f s h =
  gApp ~explicit:true (gInject "semSuchThatMaybeOpt_sound") [hole; g; f; s; h]
