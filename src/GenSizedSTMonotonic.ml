open Pp
open Loc
open Names
open Extract_env
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
open Decl_kinds
open GenericLib
open SetLib
open CoqLib
open GenLib
open SemLib
open Feedback

let genSizedSTMon_body class_name full_gtyp full_pred inputs base_gen ind_gen =

  let base_case =
    gFunWithArgs
      inputs
      (fun inputs ->
         backtrackSizeMonotonic base_gen hole)
  in

  let ind_case =
    gFun ["size"; "IHs"]
      (fun [size; ihs] ->
         gFunWithArgs
           inputs
           (fun inputs ->
              backtrackSizeMonotonic ind_gen hole))
  in

  let ret_type =
    gFun ["s"]
      (fun [s] -> 
         gProdWithArgs
           inputs
           (fun inputs ->
              gApp class_name
                [gApp ~explicit:true (gInject "arbitrarySizeST")
                   [full_gtyp; full_pred (List.map gVar inputs); hole; gVar s]]))
  in 

  let mon_proof =
    gApp (gInject "nat_ind") [ret_type; base_case; ind_case]
  in

  msg_debug (str "mon term");
  debug_coq_expr mon_proof;
  gRecord [("monotonic", mon_proof)]
