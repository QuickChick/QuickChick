open Util
open GenericLib
open GenLib
open Error

let enumSized_decl (types : (ty_ctr * ctr_rep list) list) : (ty_ctr -> var list -> coq_expr) * ((var * (var * coq_expr) list * var * coq_expr * coq_expr) list) =
  let impl_function_names : (ty_ctr * var) list =
    List.map (fun (ty, _) -> 
      let type_name = ty_ctr_to_string ty in
      let function_name = fresh_name ("enumSized_impl_" ^ type_name) in

      (ty, function_name)
    ) types in

  let generate_enumSized_function ((ty, ctors) : (ty_ctr * ctr_rep list)) : var * (var * coq_expr) list * var * coq_expr * coq_expr =
    let function_name = List.assoc ty impl_function_names in

    let arg = fresh_name "size" in
    let arg_type = (gInject "Coq.Init.Datatypes.nat") in

    (* E ty *)
    let return_type = gApp (gInject "QuickChick.Enumerators.E") [gTyCtr ty] in

    let find_ty_ctr = function
    | TyCtr (ty_ctr', _) -> List.assoc_opt ty_ctr' impl_function_names
    | _ -> None in

    (* a base branch is a constructor that doesn't require our ty_ctr to be used *)
    let is_base_branch ty =
      fold_ty' (fun b ty' -> b && (None = (find_ty_ctr ty'))) true ty in
    let base_branches =
      List.filter (fun (_, ty) -> is_base_branch ty) ctors in

    (* TODO: implement this back *)
    (* let tyParams = [List.map gVar (list_drop_every 2 iargs)] in *)
    let tyParams = [] in

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
        | _ -> returnEnum (gApp ~explicit:true (gCtr ctr) (tyParams @ List.rev acc))
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

    (function_name, [(arg, arg_type)], arg, return_type, body) in

  let functions = List.map generate_enumSized_function types in

  (* returns {| enumSized := enumSized_impl_... |} *)
  let instance_record ty_ctr ivars : coq_expr =
    if List.length ivars > 0 then
      (* This might be a regression compared to the version without support for mutual induction. *)
      qcfail "Not implemented";

    let impl_function_name = List.assoc ty_ctr impl_function_names in
    gRecord [("enumSized", gVar impl_function_name)] in
  
  (instance_record, functions)
