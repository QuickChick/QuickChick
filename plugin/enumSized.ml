open Util
open GenericLib
open GenLib

let enumSized_decl (types : (ty_ctr * ty_param list * ctr_rep list) list) : (ty_ctr -> var list -> coq_expr) * ((var * arg list * var * coq_expr * coq_expr) list) =
  let impl_function_names : (ty_ctr * var) list =
    List.map (fun (ty, _, _) -> 
      let type_name = ty_ctr_to_string ty in
      let function_name = fresh_name ("enumSized_impl_" ^ type_name) in

      (ty, function_name)
    ) types in

  let generate_enumSized_function ((ty, ty_params, ctors) : (ty_ctr * ty_param list * ctr_rep list)) : var * arg list * var * coq_expr * coq_expr =
    let function_name = List.assoc ty impl_function_names in

    let coqTyParams = List.map gTyParam ty_params in
    let full_type = gApp ~explicit:true (gTyCtr ty) coqTyParams in

    let arg = fresh_name "size" in
    let arg_type = (gInject "Coq.Init.Datatypes.nat") in

    (* E ty *)
    let return_type = gApp (gInject "QuickChick.Enumerators.E") [full_type] in

    let find_ty_ctr = function
    | TyCtr (ty_ctr', _) -> List.assoc_opt ty_ctr' impl_function_names
    | _ -> None in

    (* a base branch is a constructor that doesn't require our ty_ctr to be used *)
    let is_base_branch ty =
      fold_ty' (fun b ty' -> b && (None = (find_ty_ctr ty'))) true ty in
    let base_branches =
      List.filter (fun (_, ty) -> is_base_branch ty) ctors in

    let create_for_branch size (ctr, ty) =
      let rec aux i acc ty : coq_expr =
        match ty with
        | Arrow (ty1, ty2) ->
            bindEnum
              (match find_ty_ctr ty1 with
                | Some name -> gApp (gVar name) [gVar size]
                | None -> gInject "enum")
              (Printf.sprintf "p%d" i)
              (fun pi -> aux (i+1) ((gVar pi) :: acc) ty2)
        | _ -> returnEnum (gApp ~explicit:true (gCtr ctr) (coqTyParams @ List.rev acc))
      in aux 0 [] ty in
    let body = gMatch (gVar arg) [
      (
        injectCtr "O", [],
        fun _ -> oneof (List.map (create_for_branch arg) base_branches)
      );
      (
        injectCtr "S", ["size'"],
        fun [size'] -> oneof (List.map (create_for_branch size') ctors)
      )
    ] in
    debug_coq_expr body;

    (function_name, [gArg ~assumName:(gVar arg) ~assumType:arg_type ()], arg, return_type, body) in

  let functions = List.map generate_enumSized_function types in

  (* returns {| enumSized := enumSized_impl_... |} *)
  let instance_record ty_ctr ivars : coq_expr =
    let impl_function_name = List.assoc ty_ctr impl_function_names in
    let implicit_arguments = List.map gVar ivars in

    gRecord [
      ("enumSized",
        gApp ~explicit:true (gVar impl_function_name) implicit_arguments)
    ] in
  
  (instance_record, functions)
