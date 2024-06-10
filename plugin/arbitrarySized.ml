open Util
open GenericLib
open GenLib
open Error

let arbitrarySized_decl (types : (ty_ctr * ctr_rep list) list) : (ty_ctr -> var list -> coq_expr) * ((var * (var * coq_expr) list * var * coq_expr * coq_expr) list) =
  let impl_function_names : (ty_ctr * var) list =
    List.map (fun (ty, _) -> 
      let type_name = ty_ctr_to_string ty in
      let function_name = fresh_name ("arbitrarySized_impl_" ^ type_name) in

      (ty, function_name)
    ) types in

  let generate_arbitrarySized_function ((ty, ctors) : (ty_ctr * ctr_rep list)) : var * (var * coq_expr) list * var * coq_expr * coq_expr =
    let function_name = List.assoc ty impl_function_names in

    let arg = fresh_name "size" in
    let arg_type = (gInject "Coq.Init.Datatypes.nat") in

    (* G ty *)
    let return_type = gApp (gInject "QuickChick.Generators.G") [gTyCtr ty] in

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
            bindGen
              (match find_ty_ctr ty1 with
                | Some name -> gApp (gVar name) [gVar size]
                | None -> gInject "arbitrary")
              (Printf.sprintf "p%d" i)
              (fun pi -> aux (i+1) ((gVar pi) :: acc) ty2)
        | _ -> returnGen (gApp ~explicit:true (gCtr ctr) (tyParams @ List.rev acc))
      in aux 0 [] ty in
    let body = gMatch (gVar arg) [
      (
        injectCtr "O", [],
        fun _ -> oneofThunked (List.map (create_for_branch arg) base_branches)
      );
      (
        injectCtr "S", ["size'"],
        fun [size'] ->
          frequencyThunked (List.map (fun (ctr, ty') ->
            (Weightmap.lookup_weight (is_base_branch ty') ctr size', create_for_branch size' (ctr, ty'))
          ) ctors)
      )
    ] in
    debug_coq_expr body;

    (function_name, [(arg, arg_type)], arg, return_type, body) in

  let functions = List.map generate_arbitrarySized_function types in

  (* returns {| arbitrarySized := arbitrarySized_impl_... |} *)
  let instance_record ty_ctr ivars : coq_expr =
    if List.length ivars > 0 then
      (* This might be a regression compared to the version without support for mutual induction. *)
      qcfail "Not implemented";

    let impl_function_name = List.assoc ty_ctr impl_function_names in
    gRecord [("arbitrarySized", gVar impl_function_name)] in
  
  (instance_record, functions)

let rec replace v x = function
  | [] -> []
  | y::ys -> if y = v
      then x::ys
      else y::(replace v x ys)

let shrink_decl (types : (ty_ctr * ctr_rep list) list) : (ty_ctr -> var list -> coq_expr) * ((var * (var * coq_expr) list * var * coq_expr * coq_expr) list) =
  let impl_function_names : (ty_ctr * var) list =
    List.map (fun (ty, _) -> 
      let type_name = ty_ctr_to_string ty in
      let function_name = fresh_name ("shrink_impl_" ^ type_name) in

      (ty, function_name)
    ) types in

  let generate_show_function ((ty, ctors) : (ty_ctr * ctr_rep list)) : var * (var * coq_expr) list * var * coq_expr * coq_expr =
    let function_name = List.assoc ty impl_function_names in

    let arg = fresh_name "x" in
    let arg_type = gTyCtr ty in

    (* ty list *)
    let return_type = gApp (gInject "Coq.Init.Datatypes.list") [gTyCtr ty] in

    let is_current_ty_crt = function
    | TyCtr (ty_ctr', _) -> ty = ty_ctr'
    | _ -> false in

    let find_ty_ctr = function
    | TyCtr (ty_ctr', _) -> List.assoc_opt ty_ctr' impl_function_names
    | _ -> None in

    (* TODO: implement this back *)
    (* let tyParams = [List.map gVar (list_drop_every 2 iargs)] in *)
    let tyParams = [] in

    let create_branch (ctr, ty) = (
      ctr,
      generate_names_from_type "p" ty,
      fold_ty_vars
        (fun allParams v ty' ->
          let liftNth =
            gFun ["shrunk"]
            (fun [shrunk] ->
              gApp ~explicit:true (gCtr ctr) (tyParams @ (replace (gVar v) (gVar shrunk) (List.map gVar allParams))))
          in

          lst_appends (match find_ty_ctr ty' with
          | Some name ->
              if is_current_ty_crt ty'
                (* [[v], List.map liftNth (name v)] *)
                then [ gList [gVar v] ; gApp (gInject "List.map") [liftNth; gApp (gVar name) [gVar v]] ]
                (* [List.map liftNth (name v)] *)
                else [ gApp (gInject "List.map") [liftNth; gApp (gVar name) [gVar v]] ]
            (* [List.map liftNth (shrink v)] *)
            | None -> [ gApp (gInject "List.map") [liftNth; gApp (gInject "shrink") [gVar v]] ]))
        lst_append
        list_nil ty
    ) in
    let body = gMatch (gVar arg) (List.map create_branch ctors) in
    debug_coq_expr body;

    (function_name, [(arg, arg_type)], arg, return_type, body) in

  let functions = List.map generate_show_function types in

  (* returns {| shrink := show_impl_... |} *)
  let instance_record ty_ctr ivars : coq_expr =
    if List.length ivars > 0 then
      (* This might be a regression compared to the version without support for mutual induction. *)
      qcfail "Not implemented";

    let impl_function_name = List.assoc ty_ctr impl_function_names in
    gRecord [("shrink", gVar impl_function_name)] in
  
  (instance_record, functions)

let show_decl (types : (ty_ctr * ctr_rep list) list) : (ty_ctr -> var list -> coq_expr) * ((var * (var * coq_expr) list * var * coq_expr * coq_expr) list) =
  let impl_function_names : (ty_ctr * var) list =
    List.map (fun (ty, _) -> 
      let type_name = ty_ctr_to_string ty in
      let function_name = fresh_name ("show_impl_" ^ type_name) in

      (ty, function_name)
    ) types in

  let generate_show_function ((ty, ctors) : (ty_ctr * ctr_rep list)) : var * (var * coq_expr) list * var * coq_expr * coq_expr =
    let function_name = List.assoc ty impl_function_names in

    let arg = fresh_name "x" in
    let arg_type = gTyCtr ty in

    let return_type = gInject "Coq.Strings.String.string" in

    let find_ty_ctr = function
    | TyCtr (ty_ctr', _) -> List.assoc_opt ty_ctr' impl_function_names
    | _ -> None in

    let branch (ctr, ty) = (
        ctr,
        generate_names_from_type "p" ty,
        fun vs -> match vs with
          | [] -> gStr (constructor_to_string ctr)
          | _ -> str_append
                  (gStr (constructor_to_string ctr ^ " "))
                  (fold_ty_vars
                    (fun _ v ty' ->
                      smart_paren @@
                      gApp (match find_ty_ctr ty' with
                        | Some name -> gVar name
                        | _ -> gInject "show"
                      ) [gVar v])
                    (fun s1 s2 ->
                      if s2 = emptyString then s1
                      else str_appends [s1; gStr " "; s2])
                    emptyString ty vs)
      ) in
    (* match x with | Ctr p0 p1 ... pn -> "Ctr " ++ (...) ++ " " ++ (...) *)
    let body = gMatch (gVar arg) (List.map branch ctors) in

    (function_name, [(arg, arg_type)], arg, return_type, body) in

  let functions = List.map generate_show_function types in

  (* returns {| show := show_impl_... |} *)
  let instance_record ty_ctr _ivars : coq_expr =
    let impl_function_name = List.assoc ty_ctr impl_function_names in
    gRecord [("show", gVar impl_function_name)] in
  
  (instance_record, functions)