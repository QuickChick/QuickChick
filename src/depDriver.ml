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
open ArbitrarySizedST
open GenSizedSTMonotonic
open Error
open Unify
open SizedProofs

(** Derivable classes *)
type derivable =
    ArbitrarySizedSuchThat
  | GenSizedSuchThatMonotonic
  | GenSizedSuchThatSizeMonotonic
  | GenSizedSuchThatCorrect
  | SizedProofEqs

let print_der = function
  | ArbitrarySizedSuchThat -> "ArbitrarySizedSuchThat"
  | GenSizedSuchThatMonotonic -> "SizeMonotonic"
  | SizedProofEqs -> "SizedProofEqs"
  | GenSizedSuchThatSizeMonotonic
  | GenSizedSuchThatCorrect -> ""


let class_name cn =
  match cn with
  | ArbitrarySizedSuchThat -> "GenSizedSuchThat"
  | GenSizedSuchThatMonotonic -> "SizeMonotonic"
  | SizedProofEqs -> "SizedProofEqs"
  | GenSizedSuchThatSizeMonotonic
  | GenSizedSuchThatCorrect -> ""

(** Name of the instance to be generated *)
let mk_instance_name der tn =
  let prefix = match der with
    | ArbitrarySizedSuchThat -> "arbSizedST"
    | GenSizedSuchThatMonotonic -> "SizeMonotonic"
    | SizedProofEqs -> "SizedProofEqs"
    | _ -> failwith "Not implemented"
  in var_to_string (fresh_name (prefix ^ tn))

(** Generic derivation function *)
let deriveDependent (cn : derivable) (c : constr_expr) (n : int) (instance_name : string) =

  let (ty_ctr, ty_params, ctrs, dep_type) : (ty_ctr * (ty_param list) * (dep_ctr list) * dep_type) =
    match coerce_reference_to_dep_dt c with
    | Some dt -> msg_debug (str (dep_dt_to_string dt) ++ fnl()); dt 
    | None -> failwith "Not supported type" in

  msg_debug (str (string_of_int n) ++ fnl ());
  debug_coq_expr (gType ty_params dep_type);

  let (input_types : dep_type list) =
    let rec aux acc i = function
      | DArrow (dt1, dt2) 
      | DProd ((_,dt1), dt2) ->
        if i == n then (* i == n means this is what we generate for - ignore *) 
          aux acc (i+1) dt2
        else (* otherwise this needs to be an input argument *)
          aux (dt1 :: acc) (i+1) dt2
      | DTyParam tp -> acc
      | DTyCtr (c,dts) -> acc
      | DTyVar _ -> acc
    in List.rev (aux [] 1 dep_type) (* 1 because of using 1-indexed counting for the arguments *)       
  in

  (* type constructor *)
  let coqTyCtr = gTyCtr ty_ctr in
  (* parameters of the type constructor *)
  let coqTyParams = List.map gTyParam ty_params in

  (* Fully applied type constructor *)
  let full_dt = gApp ~explicit:true coqTyCtr coqTyParams in

  (* Name for type indices *)
  let input_names = List.mapi (fun i _ -> Printf.sprintf "input%d_" i) input_types in
  
  let forGen = "_forGen" in


  let params = List.map (fun tp -> gArg ~assumName:(gTyParam tp) ()) ty_params in
  
  let inputs =
    List.map (fun (n,t) -> gArg ~assumName:(gVar (fresh_name n)) ~assumType:(gType ty_params t) ())
      (List.combine input_names input_types)
  in
  
  (* TODO: These should be generated through some writer monad *)
  (* XXX Put dec_needed in ArbitrarySizedSuchThat *)
  let gen_needed = [] in
  let dec_needed = [] in

  let self_dec = [] in 
  (*     (* Maybe somethign about type paramters here *)
     if !need_dec then [gArg ~assumType:(gApp (gInject (Printf.sprintf "DepDec%n" (dep_type_len dep_type))) [gTyCtr ty_ctr]) 
                            ~assumGeneralized:true ()] 
     else [] in*)

  let arbitraries = ref ArbSet.empty in

  (* this is passed as an arg to arbitrarySizedST. Yikes! *)
  let register_arbitrary dt =
    arbitraries := ArbSet.add dt !arbitraries
  in

  (* The type we are generating for -- not the predicate! *)
  let full_gtyp = (gType ty_params (nthType n dep_type)) in

  (* The type of the dependent generator *)
  let gen_type = gGen (gOption full_gtyp) in

  (* Fully applied predicate (parameters and constructors) *)
  let full_pred inputs =
    gFun [forGen] (fun [fg] -> gApp (full_dt) (list_insert_nth (gVar fg) inputs (n-1)))
  in

  (* The dependent generator  *)
  let gen =
    arbitrarySizedST
      ty_ctr ty_params ctrs dep_type input_names inputs n register_arbitrary
  in

  (* Generate arbitrary parameters *)
  let arb_needed = 
    ArbSet.fold
      (fun dt acc ->
        (gArg ~assumType:(gApp (gInject "Arbitrary") [gType ty_params dt]) ~assumGeneralized:true ()) :: acc
      ) (!arbitraries) []
  in

  (* Generate typeclass constraints. For each type parameter "A" we need `{_ : <Class Name> A} *)
  let instance_arguments = match cn with
    | ArbitrarySizedSuchThat ->
      params
      @ gen_needed
      @ dec_needed
      @ self_dec
      @ arb_needed
      @ inputs
    | GenSizedSuchThatMonotonic -> []
    | SizedProofEqs -> params @ inputs
    | _ -> []
  in

  (* The instance type *)
  let instance_type iargs = match cn with
    | ArbitrarySizedSuchThat ->
      gApp (gInject (class_name cn))
        [gType ty_params (nthType n dep_type);
         full_pred (List.map (fun n -> gVar (fresh_name n)) input_names)]
    | GenSizedSuchThatMonotonic ->
      gProdWithArgs
        ((gArg ~assumType:(gInject "nat") ~assumName:(gInject "size") ()) :: inputs)
        (fun (size :: inputs) ->
           gApp (gInject (class_name cn))
             [gApp ~explicit:true (gInject "arbitrarySizeST")
                [full_gtyp; full_pred (List.map gVar inputs); hole; gVar size]])
    | SizedProofEqs -> gApp (gInject (class_name cn)) [full_pred (List.map (fun n -> gVar (fresh_name n)) input_names)] 
    | _ -> failwith "Unimplemented"
  in

  let instance_record iargs =
    match cn with
    | ArbitrarySizedSuchThat -> gen
    | GenSizedSuchThatMonotonic ->
      msg_debug (str "mon type");
      debug_coq_expr (instance_type []);
      genSizedSTMon_body (class_name cn) ty_ctr ty_params ctrs dep_type input_names inputs n register_arbitrary
    | SizedProofEqs ->
      sizedEqProofs_body (class_name cn) ty_ctr ty_params ctrs dep_type input_names inputs n register_arbitrary
    | _ -> failwith "Unimplemented"
  in

  msg_debug (str "Instance Type: " ++ fnl ());
  debug_coq_expr (instance_type [gInject "input0"; gInject "input1"]);

  declare_class_instance instance_arguments instance_name instance_type instance_record
;;

(*
VERNAC COMMAND EXTEND DeriveArbitrarySizedSuchThat
  | ["DeriveArbitrarySizedSuchThat" constr(c) "for" constr(n) "as" string(s1)] -> [deriveDependent ArbitrarySizedSuchThat c n s1]
END;;
  *)
