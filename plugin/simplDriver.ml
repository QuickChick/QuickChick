(* Derivation of the simple classes: Show, Shrink, Sized, Fuzzy and Mutate.
   Generators and enumerators for plain types go through PublicDerive. *)
open Constrexpr
open GenericLib
open Sized
open ArbitrarySized

type derivable =
    Shrink
  | Show
  | Fuzzy
  | Mutate
  | Sized

let derivable_to_string = function
  | Shrink -> "Shrink"
  | Show   -> "Show"
  | Fuzzy -> "Fuzzy"
  | Mutate -> "Mutate"
  | Sized -> "Sized"

let mk_instance_name der tn =
  let prefix = derivable_to_string der in
  let strip_last s = List.hd (List.rev (String.split_on_char '.' s)) in
  var_to_string (fresh_name (prefix ^ strip_last tn))

let repeat_instance_name der tn =
  let prefix = derivable_to_string der in
  let strip_last s = List.hd (List.rev (String.split_on_char '.' s)) in
  (prefix ^ strip_last tn)

(* Generic derivation function *)
let derive (cn : derivable) (c : constr_expr) =
  let dt = match coerce_reference_to_dt_rep c with
    | Some dt -> dt
    | None -> failwith "Not supported type"  in

  let coqTyCtr = List.map (fun (ty_ctr, _, _) -> gTyCtr ty_ctr) dt in
  let coqTyParams = List.map (fun (_, ty_params, _) -> List.map gTyParam ty_params) dt in

  let full_dt = List.map2
    (fun coqTyCtr coqTyParams -> gApp ~explicit:true coqTyCtr coqTyParams)
    coqTyCtr coqTyParams in

  let class_name = derivable_to_string cn in

  let param_class_names = match cn with
    | Sized -> ["Sized"]
    | Shrink -> ["Shrink"]
    | Show -> ["Show"]
    | Fuzzy -> ["Gen"; "Fuzzy"]
    | Mutate -> ["Gen"; "Sized"; "Mutate"]
  in

  (* Generate typeclass constraints. For each type parameter "A" we need `{_ : <Class Name> A} *)
  let instance_arguments : (arg list) list = List.map (fun coqTyParams ->
    List.concat @@
      List.map (fun tp -> (gArg ~assumName:tp ~assumImplicit:true ()) ::
        (List.map (fun name -> gArg ~assumType:(gApp (gInject name) [tp]) ~assumGeneralized:true ()) param_class_names)
      ) coqTyParams) coqTyParams
  in

  (* The instance type *)
  let instance_type full_dt _iargs = gApp (gInject class_name) [full_dt]
  in

  (* Create the instance record. Only need to extend this for extra instances *)
  let (instance_record, functions_to_mutually_define) :
      (ty_ctr -> var list -> coq_expr)
      * (var * arg list * var * coq_expr * coq_expr) list =
    (* Copying code for Arbitrary, Sized from derive.ml *)
    match cn with
    | Show -> show_decl dt
    | Shrink -> shrink_decl dt
    | Sized -> sized_decl dt
    | Fuzzy | Mutate ->
        let legacy_decl = match cn with Fuzzy -> fuzzy_decl | _ -> mutate_decl in
        (match dt with
         | [(ty_ctr, _, ctrs)] ->
             ((fun _ iargs -> legacy_decl ty_ctr ctrs iargs), [])
         | _ -> failwith "Fuzzy and Mutate derivation do not support mutually inductive types")
  in

  if functions_to_mutually_define <> [] then define_new_fixpoint @@ List.map (fun ((function_name, arguments, arg, return_type, body), instance_arguments) ->
    let arguments = instance_arguments @ arguments in

    (function_name, arguments, arg, return_type, body))
    (List.combine functions_to_mutually_define instance_arguments);

  let rec iter3 f l1 l2 l3 =
    match (l1, l2, l3) with
    | x1 :: l1, x2 :: l2, x3 :: l3 ->
        f x1 x2 x3;
        iter3 f l1 l2 l3
    | [], [], [] -> ()
    | _ -> raise (Invalid_argument "iter3")
  in

  iter3
    (fun instance_arguments (ty_ctr, _, _) full_dt ->
      let ind_name = ty_ctr_to_string ty_ctr in
      let instance_name = mk_instance_name cn ind_name in

      declare_class_instance instance_arguments instance_name
        (instance_type full_dt) (instance_record ty_ctr))
    instance_arguments dt full_dt
