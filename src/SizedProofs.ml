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

(* arguments to handle_branch *)
let fail_exp = set_empty

let ret_exp (c : coq_expr) =
  set_singleton c

let ret_type (s : var) (match_expr : var -> coq_expr -> coq_expr -> coq_expr) = hole

let class_method = set_full

let class_methodST (pred : coq_expr) =
  pred

let rec_method (rec_name : coq_expr) (size : coq_expr) (l : coq_expr list) =
  gApp rec_name (size :: l)

let bind (opt : bool) (m : coq_expr) (x : string) (f : var -> coq_expr) =
  set_bigcup x m f

let stMaybe (opt : bool) (g : coq_expr) (bool_pred : coq_expr) =
  set_bigcup "x" g (fun x -> gEqType (gApp bool_pred [gVar x]) (gInject "true"))

let sizedEqProofs_body
      (class_name : string)
      (gen_ctr : ty_ctr)
      (ty_params : ty_param list)
      (ctrs : dep_ctr list)
      (dep_type : dep_type)
      (input_names : string list)
      (inputs : arg list)
      (n : int)
      (register_arbitrary : dep_type -> unit) =

  (* type constructor *)
  let coqTyCtr = gTyCtr gen_ctr in

  (* parameters of the type constructor *)
  let coqTyParams = List.map gTyParam ty_params in

  (* Fully applied type constructor *)
  let full_dt = gApp ~explicit:true coqTyCtr coqTyParams in

  (* The type we are generating for -- not the predicate! *)
  let full_gtyp = (gType ty_params (nthType n dep_type)) in

  (* The type of the dependent generator *)
  let gen_type = gGen (gOption full_gtyp) in

  (* Fully applied predicate (parameters and constructors) *)
  let full_pred inputs =
    gFun ["_forGen"] (fun [fg] -> gApp (full_dt) (list_insert_nth (gVar fg) inputs (n-1)))
  in
  (* gen_ctr dep_type gen_type ctrs input_names inputs n register_arbitrary *)
  (* class_name full_gtyp full_pred inputs base_gen ind_gen = *)

  let input_vars = List.map fresh_name input_names in
  
  let zero_set inputs =
    let handle_branch'  =
      handle_branch n dep_type inputs
        fail_exp ret_exp ret_type class_method class_methodST
        (rec_method (gVar (make_up_name ())) (gVar (make_up_name ()))) bind stMaybe gen_ctr (fun _ -> ())
    in
    (List.fold_right
       (fun c exp ->
          let (p, b) = handle_branch' c in
          if b then
            set_union p exp
          else exp
       )
       ctrs (set_empty))
  in

  let succ_set rec_name size inputs =
    let handle_branch'  =
      handle_branch n dep_type inputs
        fail_exp ret_exp ret_type class_method class_methodST
        (rec_method (gVar rec_name) (gVar size)) bind stMaybe gen_ctr (fun _ -> ())
    in
    (List.fold_right
       (fun c exp ->
          let (p, b) = handle_branch' c in
          set_union p exp
       ) ctrs (set_empty))
  in

    let aux_iter rec_name size vars =
    gMatch (gVar size)
      [ (injectCtr "O", [],
         fun _ -> zero_set vars)
      ; (injectCtr "S", ["size'"],
         fun [size'] -> succ_set rec_name size' vars)
      ]
  in

  let iter_body : coq_expr =
    gRecFunInWithArgs
      "aux_iter" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
      (fun (rec_name, size::vars) -> aux_iter rec_name size vars)
      (fun rec_name -> gFun ["size"] 
          (fun [size] -> gApp (gVar rec_name) 
              (gVar size :: List.map gVar input_vars)
          ))
  in

  (* let full_prop gtyp inputs = *)
  (*   gApp (full_dt) (list_insert_nth gtyp inputs (n-1)) *)
  (* in *)

  (* let left_ret_type x = *)
  (*   gFun ["n"] *)
  (*     (fun [n] -> *)
  (*        gProdWithArgs *)
  (*          inputs *)
  (*          (fun inputs -> *)
  (*             gImpl *)
  (*               (gApp (appn succ_set n zero_set) [x]) *)
  (*               (full_prop (gVar x) (List.map gVar inputs)) *)
  (*          ) *)
  (*     ) *)
  (* in *)

  (* let rec elim_base_cases hin ih ctrs n = *)
  (*   let hr = Printf.sprintf "Hl%d" n in *)
  (*   let hl = Printf.sprintf "Hr%d" n in *)
  (*   match ctrs with *)
  (*   | [] -> false_ind hole h *)
  (*   | c :: ctrs' -> *)
  (*     let (p, b) = handle_branch' inputs c in *)
  (*     if b then *)
  (*       gMatch hin *)
  (*         [(injectCtr "or_introl", [hl], *)
  (*           fun [hl] -> p); *)
  (*          (injectCtr "or_intror", [hr], *)
  (*           fun [hr] -> elim_cases (gVar hr) ih ctrs' (n+1))] *)
  (*     else elim_cases hin ih ctrs' (n+1) *)
  (* in *)

  (* let left_base_case = *)
  (*   gFun (input_names @ ["hin"]) *)
  (*     (fun inputs_hin -> *)
  (*        let (inputs, hin) = last inputs_hin in *)
  (*        elim_cases hin hole ctrs 0  *)
  (*     ) *)
  (* in *)

  (* let left_ind_case = *)
  (*   gFun ("s" :: "":: (input_names @ "hin")) *)
  (*     (fun (s :: ihs :: inputs_hin) -> *)
  (*        let (inputs, hin) = last inputs_hin in *)
         
  (*     ) *)
  (* in *)

  (* let leftp (x : var) : coq_expr = *)
  (*   (\* Hin : \bigcup(n : nat) (succ ^ n zero) x *\) *)
  (*   gFun ["Hin"] *)
  (*     (fun [hin] -> *)
  (*        gMatch hin *)
  (*          [(injectCtr "ex_intro", ["s"; "Hc"], *)
  (*            fun [s; hc] -> *)
  (*              gMatch hc *)
  (*                [(injectCtr "conj", ["Hl"; "Hin"], *)
  (*                  fun [hl; hin] -> *)
  (*                    gApp *)
  (*                      (nat_ind (ret_type x) left_base_case left_ind_case) *)
  (*                      x (List.map gVar input_vars) hin *)
  (*                 )] *)
  (*           )]) *)
  (* in *)

  (* let rightp (x : var) : coq_exp = *)
    
  (* in *)

  (* let spec = *)
  (*   gFun ["x"] *)
  (*     (fun [x] -> gConjIntro leftp rightp) *)

  (* msg_debug (str "zero"); *)
  (* debug_coq_expr zero_set; *)
  msg_debug (str "iter");
  debug_coq_expr iter_body;
  gRecord [("iter", iter_body)]
