open Util
open GenericLib

(* Gen combinators *)
let gGen c = gApp (gInject "G") [c]

let returnGen c = gApp (gInject "returnGen") [c]
let bindGen cg xn cf = 
  gApp (gInject "bindGen") [cg; gFun [xn] (fun [x] -> cf x)]

let bindGenOpt cg xn cf = 
  gApp (gInject "bindOpt") [cg; gFun [xn] (fun [x] -> cf x)]

(* Gen combinators *)
let gEnum c = gApp (gInject "E") [c]

let returnEnum c = gApp (gInject "returnEnum") [c]
let bindEnum cg xn cf = 
  gApp (gInject "bindEnum") [cg; gFun [xn] (fun [x] -> cf x)]
let failEnum c =
  gApp ~explicit:true (gInject "failEnum") [c]

  
let bindEnumOpt cg xn cf = 
  gApp (gInject "bindOpt") [cg; gFun [xn] (fun [x] -> cf x)]

let enumChecker cg xn cf sz = 
  gApp (gInject "enumerating") [cg; gFun [xn] (fun [x] -> cf x); sz]

let enumCheckerOpt cg xn cf sz = 
  gApp (gInject "enumeratingOpt") [cg; gFun [xn] (fun [x] -> cf x); sz]

  
let oneof l =
  match l with
  | [] -> failwith "oneof used with empty list"
  | [c] -> c
  | c::cs -> gApp (gInject "oneOf_") [c; gList l]

(* oneOfT_ {A : Type} (def: unit -> G A) (gs : list (unit -> G A)) : G A *)
let oneofT l =
  match l with
  | [] -> failwith "oneofT used with empty list"
  | [c] -> gApp c [gTT] 
  | c::cs -> gApp (gInject "oneOfT_") [c; gList l]

           
let frequency l =
  match l with
  | [] -> failwith "frequency used with empty list"
  | [(_,c)] -> c
  | (_,c)::cs -> gApp (gInject "freq_") [c; gList (List.map gPair l)]

(* TODO: frequencyT i.e. frequency thunked *)

let frequencyT l =
  match l with 
  | [] -> failwith "frequencyT used with empty list"
  | [(_, c)] -> gApp c [gTT]
  | (_,c)::cs -> gApp (gInject "freqT_") [c; gList (List.map gPair l)]

let enumerating l =
  gApp (gInject "enumerate") [gList l]

               
let backtracking l = gApp (gInject "backtrack") [gList (List.map gPair l)]
let uniform_backtracking l = backtracking (List.combine (List.map (fun _ -> gInt 1) l) l)

let checker_backtracking l = gApp (gInject "checker_backtrack") [gList (List.map (fun opt -> gFun ["_unit"] (fun _ -> opt)) l)]
                           
(* Map from inductives to maps of constructor weights *)
module TyCtrMap = Map.Make(Ord_ty_ctr)
module CtrMap   = Map.Make(Ord_ctr)

(* let weight_map : int CtrMap.t TyCtrMap.t = ref *)
