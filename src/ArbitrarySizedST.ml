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
open Feedback
open Unify

(* Advanced Generators *)
let arbitrarySizedST gen_ctr dep_type gen_type ctrs input_names inputs n register_arbitrary =
  let input_names = List.map fresh_name input_names in

  (*  List.iter (fun x -> ignore (handle_branch x)) ctrs;  *)

  let aux_arb rec_name size vars =
    (* arguments to handle_branch *)
    let fail_exp = returnGen gNone in
    let ret_exp (c : coq_expr) = returnGen (gSome c) in
    let class_method = (gInject "arbitrary") in
    let class_methodST (pred : coq_expr) (size : coq_expr) = 
      gApp ~explicit:true (gInject "arbitrarySizeST")
        [ hole (* Implicit argument - type A *)
        ; pred
        ; hole (* Implicit instance *)
        ; size ]
    in
    let rec_method (l : coq_expr list) =
      gApp (gVar rec_name) l
    in
    let bind (opt : bool) (m : coq_expr) (x : string) (f : var -> coq_expr) =
      (if opt then bindGenOpt else bindGen) m x f
    in
    let stMaybe (opt : bool) (g : coq_expr) (bool_pred : coq_expr) =
      (gApp (gInject (if opt then "suchThatMaybeOpt" else "suchThatMaybe"))
         [ g (* Use the generator provided for base generator *)
         ; bool_pred
         ])
    in
    (* partially applied handle_branch *)
    let handle_branch' size =
      handle_branch n dep_type input_names size fail_exp ret_exp
        class_method class_methodST rec_method bind stMaybe gen_ctr register_arbitrary
    in

    gMatch (gVar size)
      [ (injectCtr "O", [], 
              fun _ -> (* Base cases *) 
                let base_branches =
                  List.map
                    fst
                    (List.filter (fun (_, b) -> b) (List.map (handle_branch' size) ctrs)) in
              uniform_backtracking base_branches
             )
           ; (injectCtr "S", ["size'"], 
              fun [size'] -> 
              let all_branches = List.map (fun x -> fst (handle_branch' size' x)) ctrs in
              uniform_backtracking all_branches
             )
           ] in

  let generator_body : coq_expr =
    gRecFunInWithArgs
      ~assumType:(gen_type)
      "aux_arb" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
      (fun (rec_name, size::vars) -> aux_arb rec_name size vars)
      (fun rec_name -> gFun ["size"] 
          (fun [size] -> gApp (gVar rec_name) 
              (gVar size :: List.map gVar input_names)
          ))
  in

  msg_debug (fnl () ++ fnl () ++ str "`Final body produced:" ++ fnl ());
  debug_coq_expr generator_body;
  msg_debug (fnl ());
  gRecord [("arbitrarySizeST", generator_body)]
