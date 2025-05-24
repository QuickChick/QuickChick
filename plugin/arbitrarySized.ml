open Util
open GenericLib
open GenLib

let arbitrarySized_decl (types : (ty_ctr * ty_param list * ctr_rep list) list) : (ty_ctr -> var list -> coq_expr) * ((var * arg list * var * coq_expr * coq_expr) list) =
  let impl_function_names : (ty_ctr * var) list =
    List.map (fun (ty, _, _) ->
      let type_name = ty_ctr_to_string ty in
      let function_name = fresh_name ("arbitrarySized_impl_" ^ type_name) in

      (ty, function_name)
    ) types in

  let generate_arbitrarySized_function ((ty, ty_params, ctors) : (ty_ctr * ty_param list * ctr_rep list)) : var * arg list * var * coq_expr * coq_expr =
    let function_name = List.assoc ty impl_function_names in

    let coqTyParams = List.map gTyParam ty_params in
    let full_type = gApp ~explicit:true (gTyCtr ty) coqTyParams in

    let arg = fresh_name "size" in
    let arg_type = (gInject "Coq.Init.Datatypes.nat") in

    (* G ty *)
    let return_type = gApp (gInject "QuickChick.Generators.G") [full_type] in

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
            bindGen
              (match find_ty_ctr ty1 with
                | Some name -> gApp (gVar name) [gVar size]
                | None -> gInject "arbitrary")
              (Printf.sprintf "p%d" i)
              (fun pi -> aux (i+1) ((gVar pi) :: acc) ty2)
        | _ -> returnGen (gApp ~explicit:true (gCtr ctr) (coqTyParams @ List.rev acc))
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

    (function_name, [gArg ~assumName:(gVar arg) ~assumType:arg_type ()], arg, return_type, body) in

  let functions = List.map generate_arbitrarySized_function types in

  (* returns {| arbitrarySized := @arbitrarySized_impl_... |} *)
  let instance_record ty_ctr ivars : coq_expr =
    let impl_function_name = List.assoc ty_ctr impl_function_names in
    let implicit_arguments = List.map gVar ivars in

    gRecord [
      ("arbitrarySized",
        gApp ~explicit:true (gVar impl_function_name) implicit_arguments)
    ] in
  
  (instance_record, functions)

let rec replace v x = function
  | [] -> []
  | y::ys -> if y = v
      then x::ys
      else y::(replace v x ys)

let shrink_decl (types : (ty_ctr * ty_param list * ctr_rep list) list) : (ty_ctr -> var list -> coq_expr) * ((var * arg list * var * coq_expr * coq_expr) list) =
  let impl_function_names : (ty_ctr * var) list =
    List.map (fun (ty, _, _) -> 
      let type_name = ty_ctr_to_string ty in
      let function_name = fresh_name ("shrink_impl_" ^ type_name) in

      (ty, function_name)
    ) types in

  let generate_shrink_function ((ty, ty_params, ctors) : (ty_ctr * ty_param list * ctr_rep list)) : var * arg list * var * coq_expr * coq_expr =
    let function_name = List.assoc ty impl_function_names in

    let coqTyParams = List.map gTyParam ty_params in
    let full_type = gApp ~explicit:true (gTyCtr ty) coqTyParams in

    let arg = fresh_name "x" in
    let arg_type = full_type in

    (* full_type list *)
    let return_type = gApp (gInject "Coq.Init.Datatypes.list") [full_type] in

    let is_current_ty_crt = function
    | TyCtr (ty_ctr', _) -> ty = ty_ctr'
    | _ -> false in

    let find_ty_ctr = function
    | TyCtr (ty_ctr', _) -> List.assoc_opt ty_ctr' impl_function_names
    | _ -> None in

    let create_branch (ctr, ty) = (
      ctr,
      generate_names_from_type "p" ty,
      fold_ty_vars
        (fun allParams v ty' ->
          let liftNth =
            gFun ["shrunk"]
            (fun [shrunk] ->
              gApp ~explicit:true (gCtr ctr) (coqTyParams @ (replace (gVar v) (gVar shrunk) (List.map gVar allParams))))
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

    (function_name, [gArg ~assumName:(gVar arg) ~assumType:arg_type ()], arg, return_type, body) in

  let functions = List.map generate_shrink_function types in

  (* returns {| shrink := @show_impl_... |} *)
  let instance_record ty_ctr ivars : coq_expr =
    let impl_function_name = List.assoc ty_ctr impl_function_names in
    let implicit_arguments = List.map gVar ivars in

    gRecord [
      ("shrink",
        gApp ~explicit:true (gVar impl_function_name) implicit_arguments)
    ] in
  
  (instance_record, functions)

let show_decl (types : (ty_ctr * ty_param list * ctr_rep list) list) : (ty_ctr -> var list -> coq_expr) * ((var * arg list * var * coq_expr * coq_expr) list) =
  let impl_function_names : (ty_ctr * var) list =
    List.map (fun (ty, _, _) -> 
      let type_name = ty_ctr_to_string ty in
      let function_name = fresh_name ("show_impl_" ^ type_name) in

      (ty, function_name)
    ) types in

  let generate_show_function ((ty, ty_params, ctors) : (ty_ctr * ty_param list * ctr_rep list)) : var * arg list * var * coq_expr * coq_expr =
    let function_name = List.assoc ty impl_function_names in

    let coqTyParams = List.map gTyParam ty_params in
    let full_type = gApp ~explicit:true (gTyCtr ty) coqTyParams in

    let arg = fresh_name "x" in
    let arg_type = full_type in

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

    (function_name, [gArg ~assumName:(gVar arg) ~assumType:arg_type ()], arg, return_type, body) in

  let functions = List.map generate_show_function types in

  (* returns {| show := show_impl_... |} *)
  let instance_record ty_ctr _ivars : coq_expr =
    let impl_function_name = List.assoc ty_ctr impl_function_names in
    gRecord [("show", gVar impl_function_name)] in
  
  (instance_record, functions)
exception ConversionError
  
let fuzzy_decl ty_ctr ctrs iargs =

  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  (* Keep just the type parameters, not the typeclass constraints. *)
  let tyParams = List.map gVar (list_keep_every 3 iargs) in

  let fuzzy_fun = 
    let fuzzy_body x =

        (* Trying to convert an instance of ctr to ctr'.
           Takes as argument vs (the values of ctr's parameters)
           and converts to ctr' on the fly, producing values for types
           as needed. 
           UP   : ctr  subseq ctr'
           DOWN : ctr' subseq ctr
           INV: length vs = length ty
           Keep a bool on up to track differences to avoid recomputing 
           if similar sigs.
         *)
        
        let rec convert_up b i ctr ty ctr' ty' vs vs_so_far =
          match (ty, ty', vs) with
          | (Arrow (ty1, ty2), Arrow (ty1', ty2'), v::vs) ->
             if ty1 = ty1' then
               (* Same type, just keep the var *)
               convert_up b (i+1) ctr ty2 ctr' ty2' vs (v :: vs_so_far)
             else
               (* Different type, produce arbitrary and recurse *)
               bindGen (gInject "arbitrary") ("param" ^ string_of_int i) (fun v' ->
                   convert_up false (i+1) ctr (Arrow (ty1, ty2)) ctr' ty2' vs (v' :: vs_so_far))
          | (TyCtr _, Arrow (ty1', ty2'), []) ->
             (* Different vars allowed at the end, arbitrary them. *)
             bindGen (gInject "arbitrary") ("param" ^ string_of_int i) (fun v' ->
                 convert_up false (i+1) ctr ty ctr' ty2' [] (v' :: vs_so_far))
          | (TyCtr _, TyCtr _, []) ->
             (* Finished, just produce the new type constructor. *)
             if not b then 
               returnGen (gApp ~explicit:true (gCtr ctr') (tyParams @ (List.map gVar (List.rev vs_so_far))))
             else
             (* Identical sigs, will be handled by convert_down. Raise error. *)
             raise ConversionError
          | _ ->
             (* Something went wrong. Can't convert *)
             raise ConversionError
        in 

        let rec convert_down i ctr ty ctr' ty' vs vs_so_far =
          match (ty, ty', vs) with
          | (Arrow (ty1, ty2), Arrow (ty1', ty2'), v::vs) ->
             if ty1 = ty1' then
               (* Same type, just keep the var *)
               convert_down (i+1) ctr ty2 ctr' ty2' vs (v :: vs_so_far)
             else
               (* Different type, throw away v and recurse *)
               convert_down (i+1) ctr ty2 ctr' (Arrow (ty1', ty2')) vs vs_so_far
          | (Arrow (ty1, ty2), TyCtr _, v :: vs) ->
             (* Different vars allowed at the end for ctr, throw them away. *)
             convert_down (i+1) ctr ty2 ctr' ty' vs vs_so_far
          | (TyCtr _, TyCtr _, []) ->
             (* Finished, just produce the new type constructor. *)
             returnGen (gApp ~explicit:true (gCtr ctr') (tyParams @ (List.map gVar (List.rev vs_so_far))))
          | _ ->
             (* Something went wrong. Can't convert *)
             raise ConversionError
        in 

        (* This should be moved to some util func *)
        let rec catMaybes = function
          | [] -> []
          | Some x :: t -> x :: catMaybes t
          | None :: t -> catMaybes t in
        
        let rec convert_ctr ((ctr, ty)) ctrs vs =
          match ctrs with
          | ((ctr', ty')) :: ctrs' ->
             if ctr == ctr' then convert_ctr ((ctr, ty)) ctrs' vs
             else begin
                 let up   = try Some (convert_up true 0 ctr ty ctr' ty' vs [])
                            with ConversionError -> None in
                 let down = try Some (convert_down    0 ctr ty ctr' ty' vs [])
                            with ConversionError -> None in
                 catMaybes [up ; down] @ convert_ctr ((ctr,ty)) ctrs' vs
               end 
          | [] -> []
        in

      let create_branch aux_fuzz (ctr, ty) =
        (ctr, generate_names_from_type "p" ty,
         fun all_vars ->
         (* Fuzz options based on the different constructors *)
         let opts_base = convert_ctr (ctr, ty) ctrs all_vars in

         let rec aux opts ty acc_vars : coq_expr =
           match ty, acc_vars with
           | Arrow (ty1, ty2), v :: vs ->
              (* lift a generator for ty1 to a generator for the whole thing *)
              let liftNth g =
                bindGen g "fuzzed" (fun fuzzed ->
                    returnGen (gApp ~explicit:true (gCtr ctr)
                                               (tyParams @ (replace (gVar v) (gVar fuzzed) (List.map gVar all_vars))))) in
              let fuzz_options = 
                if isCurrentTyCtr ty1 then
                  (* Recursive argument. Fuzz with aux, or keep *)
                  [ liftNth (gApp (gVar aux_fuzz) [gVar v])
                  ; returnGen (gVar v)
                  ]
                else
                  [ liftNth (gApp (gInject "fuzz") [gVar v]) ]
              in 

              aux (fuzz_options @ opts) ty2  vs
           (* Finalize, pick one of the options, using oneof' for now. *)
           | _ ->
              (* If no options are available (i.e, you're fuzzing a nullary constructor,
                 just generate an arbitrary thing *)
              begin match opts with
              | [] -> gInject "arbitrary"
              | _  -> oneofT (List.map (fun x -> (gFunTyped [("_tt", gUnit)] (fun _ -> x))) opts)
              end
         in aux opts_base ty all_vars)
      in

      let aux_fuzz_body rec_fun x' = gMatch (gVar x') (List.map (create_branch rec_fun) ctrs) in

      gRecFunIn "aux_fuzz" ["x'"]
        (fun (aux_fuzz, [x']) -> aux_fuzz_body aux_fuzz x')
        (fun aux_fuzz -> gApp (gVar aux_fuzz) [gVar x])
    in
    (* Create the function body by recursing on the structure of x *)
    gFun ["x"] (fun [x] -> fuzzy_body x)
  in
  debug_coq_expr fuzzy_fun;
  gRecord [("fuzz", fuzzy_fun)]

(* Mutator derivation *)
let mutate_decl ty_ctr (ctrs : ctr_rep list) (iargs : var list) = 
  
  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  (* Keep just the type parameters, not the typeclass constraints *)
  (* the number is the number of type class constraints included in `param_class_names` in simpleDriver *)
  let tyParams = List.map gVar (list_keep_every 4 iargs) in

  let unfold_coq_type : coq_type -> coq_type list * coq_type =
    let rec aux prm_typs (typ : coq_type) =
      match typ with 
      | Arrow (typ1, typ2) -> aux (typ1 :: prm_typs) typ2
      | _ -> (List.rev prm_typs, typ)
    in
    aux []
  in

  let map2_opt f opt_a opt_b = 
    Option.bind opt_a (fun a ->
    Option.bind opt_b (fun b ->
      Some (f a b)))
  in

  let rel_under_opt r def opt_a opt_b =
    match map2_opt r opt_a opt_b with 
    | Some res -> res 
    | None -> def
  in

  let coq_expr_to_thunk (e : coq_expr) : coq_expr = gFun ["_tt"] (fun [_] -> e) in
  (* let coq_expr_of_thunk (e : coq_expr) : coq_expr = gApp e [gTT] in *) (* TODO: unnecessary *)
  
  let mutate_fun =
  
    let mutate_body x =

      (*
      mutation options:
        - regenerate:
          - weight is constant
        - recombine:
          - weight is constant (TODO: more inputs?)
          - choose a new constructor
          - for each argument required by the new constructor, try (i.e. check
            if it has a compatible type) to use a given argument or the entire 
            input. This will yield a tree of branching choices. Givens can be
            used non-linearly.
          - if no givens were used, then backtrack. (TODO: or not?)
          - return the new constructor applied to the new arguments.  
        - recurse:
          - weight is a function of child size
          - choose a given argument to mutate
          - if the argument is of the same type then use aux else use arbitrary
          - return input except with result of mutation
      *)

      let weight_reg : coq_expr = 
        gInt 1
      in 
      let weight_rcm (n_preserved : int) : coq_expr = 
        gApp (gInject "Nat.pow") [gInt 2; gInt n_preserved] 
      in
      let weight_rec_ind (e_size : coq_expr) : coq_expr = 
        gApp (gInject "Nat.pow") [gInt 2; e_size] in
      let weight_rec_nonind : coq_expr = 
        gInt 1 
      in

      let create_branch 
            (x' : coq_expr) (aux_mutate : var) 
            ((ctr, ty) : constructor * coq_type) : 
            constructor * pp_tag list * (var list -> coq_expr) =
        (ctr, generate_names_from_type "p" ty,
         fun (all_vars : var list) : coq_expr ->
            let ctr_arg_typs : coq_type list = fst (unfold_coq_type ty) in
            let ctr_args : coq_expr list = List.map gVar all_vars in
            let ctr_env : (int option * coq_expr * (coq_type -> bool)) list =  
              (None, x', isCurrentTyCtr) ::
              List.map_i 
                (fun i ty -> (Some i, List.nth ctr_args i, fun ty' -> ty == ty')) 
                0 ctr_arg_typs
            in

            (* regenerate *)
            let regs : (coq_expr * coq_expr) list = 
              [(weight_reg, coq_expr_to_thunk @@ gInject "arbitrary")] 
            in

            (* recombines *)
            (* LEO: Maybe, filter the "noop" mutation that comes out *)
            let rcms : (coq_expr * coq_expr) list =
              (* all recombine options under nested freq *)
              (fun x -> [(gInt 1, coq_expr_to_thunk x)]) @@
              frequencyT @@
              List.map (fun (n_preserved, e) -> (weight_rcm n_preserved, coq_expr_to_thunk e)) @@
              List.map_append
                (fun (ctr', ctr'_typ) ->
                  let ctr'_prm_typs : coq_type list = 
                    fst (unfold_coq_type ctr'_typ) 
                  in
                  (* convert lists of lists of (optional) arguments into
                     applications, complete with any arguments that were None
                     and so need to be arbitrarily generated. *)
                  List.map_append
                    (fun opt_args ->
                      (* references :( *)
                      let n_preserved_ref = ref 0 in
                      let diff = ref false in
                      let rec f 
                          (opt_args' : (int option * coq_expr) option list) 
                          (args : coq_expr list) n_preserved i : 
                          coq_expr =
                        match opt_args' with
                        | [] ->
                          n_preserved_ref := n_preserved;
                          returnGen @@
                            gApp ~explicit:true (gCtr ctr') (List.rev args)
                        | Some (opt_i', arg) :: opt_args'' ->
                          (* counts as diff if the constructor is different, or
                             the constructor is the same but the source index is
                             different *)
                          if ((ctr != ctr') ||
                              (ctr == ctr') && rel_under_opt (!=) true opt_i' (Some i)) &&
                            not !diff then
                            diff := true;
                          f opt_args'' (arg :: args) (n_preserved + 1) (i + 1)
                        | None :: opt_args'' ->
                          if not !diff then diff := true;
                          bindGen (gInject "arbitrary") 
                            ("recombineArg_" ^ string_of_int i)
                            (fun x -> f opt_args'' (gVar x :: args) n_preserved (i + 1))
                      in
                      let res = f opt_args [] 0 0 in
                      (* discard argument arrangements that are not diff i.e.
                         output would be the same as input *)
                      if !diff then [(!n_preserved_ref, res)] else []
                    )
                  @@
                  (* compute all valid arrangements of arguments, including
                     using arbitrary (via None) *)
                  List.fold_right 
                    (fun ctr'_prm_ty argss ->
                      let opt_args : (int option * coq_expr) option list =
                        None ::
                        List.filter_map
                          (fun (opt_i, arg, is_ty) -> 
                            if is_ty ctr'_prm_ty
                              then Some (Some (opt_i, arg))
                              else None)
                          ctr_env 
                      in
                      List.map_append
                        (fun opt_arg -> 
                          List.map (fun args -> opt_arg :: args) argss)
                          opt_args
                    )
                    ctr'_prm_typs
                    [[]]
                ) 
                ctrs
            in

            (* recursions *)
            let recs : (coq_expr * coq_expr) list =
              List.map_i
                (fun i arg_typ -> 
                  let ctr_arg = List.nth ctr_args i in
                  if isCurrentTyCtr arg_typ then
                    (* TODO: weight by function of size *)
                    (* mutate child *)
                    (* return input where child is replaced *)
                    (* TODO: choose weighting function of size for inductive children *)
                    ( weight_rec_ind (gApp (gInject "size") [ctr_arg]),
                      coq_expr_to_thunk @@
                      bindGen (gApp (gVar aux_mutate) [ctr_arg]) 
                        (var_to_string (List.nth all_vars i) ^ "'") (fun child' -> 
                      returnGen (gApp ~explicit:true (gCtr ctr) 
                        (tyParams @ List.assign ctr_args i (gVar child')))))
                  else
                    (* TODO: choose reasonable weight for non-inductive children *)
                    ( weight_rec_nonind,
                      coq_expr_to_thunk @@
                      bindGen (gApp (gInject "mutate") [ctr_arg])
                        (var_to_string (List.nth all_vars i) ^ "'") (fun child' ->
                      returnGen (gApp ~explicit:true (gCtr ctr)
                        (tyParams @ List.assign ctr_args i (gVar child')))))
                )
                0 ctr_arg_typs
            in
            (* TODO: should actually use freq, and so need to choose weights *)
            (* TODO: used thunked version *)
            frequencyT @@
            regs @ rcms @ recs
        )
      in
  
      let aux_mutate_body rec_fun x' : coq_expr = 
        gMatch (gVar x') (List.map (create_branch (gVar x') rec_fun) ctrs) 
      in
  
      gRecFunIn "aux_mutate" ["x'"]
        (fun (aux_mutate, [x']) -> aux_mutate_body aux_mutate x')
        (fun aux_mutate -> gApp (gVar aux_mutate) [gVar x])
    
    in

    gFun ["x"] (fun [x] -> mutate_body x)
  
  in
  debug_coq_expr mutate_fun;
  gRecord [("mutate", mutate_fun)]

(** Shrinking Derivation *)
