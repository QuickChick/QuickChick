open Pp
open Util
open GenericLib
open GenLib
open Error

(* Derivation of ArbitrarySized. Contains mostly code from derive.ml *)

let rec replace v x = function
  | [] -> []
  | y::ys -> if y = v then x::ys else y::(replace v x ys)

let arbitrarySized_body (ty_ctr : ty_ctr) (ctrs : ctr_rep list) iargs = 
  
  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in
  let isBaseBranch ty = fold_ty' (fun b ty' -> b && not (isCurrentTyCtr ty')) true ty in

  let tyParams = List.map gVar (list_drop_every 2 iargs) in

  (* Need reverse fold for this *)
  let create_for_branch tyParams rec_name size (ctr, ty) =
    let rec aux i acc ty : coq_expr =
      match ty with
      | Arrow (ty1, ty2) ->
         bindGen (if isCurrentTyCtr ty1 then
                     gApp (gVar rec_name) [gVar size]
                  else gInject "arbitrary")
           (Printf.sprintf "p%d" i)
           (fun pi -> aux (i+1) ((gVar pi) :: acc) ty2)
      | _ -> returnGen (gApp ~explicit:true (gCtr ctr) (tyParams @ List.rev acc))
    in aux 0 [] ty in
  
  let bases = List.filter (fun (_, ty) -> isBaseBranch ty) ctrs in

  gRecFunInWithArgs
    "arb_aux" [gArg ~assumName:(gInject "size") ()]
    (fun (aux_arb, [size]) ->
      gMatch (gVar size)
        [(injectCtr "O", [],
          fun _ -> oneof (List.map (create_for_branch tyParams aux_arb size) bases))
        ;(injectCtr "S", ["size'"],
          fun [size'] -> frequency (List.map (fun (ctr,ty') ->
                                        (Weightmap.lookup_weight ctr size',
                                         create_for_branch tyParams aux_arb size' (ctr,ty'))) ctrs))
    ])
    (fun x -> gVar x)
  
let arbitrarySized_decl ty_ctr ctrs iargs =

  let arb_body = arbitrarySized_body ty_ctr ctrs iargs in
  let arbitrary_decl = gFun ["s"] (fun [s] -> gApp arb_body [gVar s]) in

  gRecord [("arbitrarySized", arbitrary_decl)]

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
                  [ liftNth (gApp (gVar aux_fuzz) [gVar v; gTT])
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
        (fun aux_fuzz -> gApp (gVar aux_fuzz) [gVar x; gTT])
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

  let to_thunk (e : coq_expr) : coq_expr = gFun ["_tt"] (fun [_] -> e) in
  (* let from_thunk (e : coq_expr) : coq_expr = gApp e [gTT] in *) (* TODO: unnecessary *)
  
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

      let weight_reg : coq_expr = gInt 1 in 
      let weight_rcm : coq_expr = gInt 1 in
      let weight_rec_ind (size : coq_expr) : coq_expr = gApp (gInject "Nat.pow") [size; gInt 2] in
      let weight_rec_nonind : coq_expr = gInt 1 in
      
  
      let create_branch 
            (x' : coq_expr) (aux_mutate : var) 
            ((ctr, ty) : constructor * coq_type) : 
            constructor * pp_tag list * (var list -> coq_expr) =
        (ctr, generate_names_from_type "p" ty,
         fun (all_vars : var list) : coq_expr ->
            let ctr_arg_typs : coq_type list = fst (unfold_coq_type ty) in
            let ctr_args : coq_expr list = List.map gVar all_vars in

            (* regenerate *)
            let regs : (coq_expr * coq_expr) list = 
              (* TODO: choose weighting for regenerate *)
              [(weight_reg, to_thunk @@ gInject "arbitrary")] 
            in
            
            (* recombines *)
            let rcms : (coq_expr * coq_expr) list =
              (* TODO: choose weighting for recombines *)
              List.map (fun e -> (weight_rcm, to_thunk @@ returnGen e)) @@
              List.flatten @@ 
              List.map
                (fun (ctr', ctr'_typ) -> 
                  let ctr'_prm_typs : coq_type list = 
                    fst (unfold_coq_type ctr'_typ) 
                  in
                  List.map (gApp ~explicit:true (gCtr ctr')) @@
                  List.fold_right
                    (fun ctr'_prm_typ argss ->
                      (* for each ctr_arg *)
                      List.flatten @@
                        List.map_i
                          (fun i typ ->
                            (* try ctr_arg as arg *)
                            if typ == ctr'_prm_typ then begin
                              (* types match, so apply *)
                              List.map (fun args -> List.nth ctr_args i :: args) argss
                            end else 
                              (* types don't match, so skip *)
                              []
                          )
                          0 ctr_arg_typs
                        @
                        (* also try input x' as arg *)
                        [if isCurrentTyCtr ctr'_prm_typ then
                          List.map (fun args -> (x' :: args)) argss
                        else 
                          []]
                    )
                    ctr'_prm_typs
                    []
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
                      to_thunk @@
                      bindGen (gApp (gVar aux_mutate) [ctr_arg]) 
                        (var_to_string (List.nth all_vars i) ^ "'") (fun child' -> 
                      returnGen (gApp ~explicit:true (gCtr ctr) 
                        (tyParams @ List.assign ctr_args i (gVar child')))))
                  else
                    (* TODO: choose reasonable weight for non-inductive children *)
                    ( weight_rec_nonind,
                      to_thunk @@
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
let shrink_decl ty_ctr ctrs iargs =

  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  let tyParams = List.map gVar (list_drop_every 2 iargs) in

  let shrink_fun = 
    let shrink_body x =
      let create_branch aux_shrink (ctr, ty) =
        (ctr, generate_names_from_type "p" ty,
         fold_ty_vars (fun allParams v ty' ->
             let liftNth = gFun ["shrunk"]
                 (fun [shrunk] -> gApp ~explicit:true (gCtr ctr)
                     (tyParams @ (replace (gVar v) (gVar shrunk) (List.map gVar allParams)))) in
             lst_appends (if isCurrentTyCtr ty' then
                            [ gList [gVar v] ; gApp (gInject "List.map") [liftNth; gApp (gVar aux_shrink) [gVar v]]]
                          else
                            [ gApp (gInject "List.map") [liftNth; gApp (gInject "shrink") [gVar v]]]))
           lst_append list_nil ty) in

      let aux_shrink_body rec_fun x' = gMatch (gVar x') (List.map (create_branch rec_fun) ctrs) in

      gRecFunIn "aux_shrink" ["x'"]
        (fun (aux_shrink, [x']) -> aux_shrink_body aux_shrink x')
        (fun aux_shrink -> gApp (gVar aux_shrink) [gVar x])
    in
    (* Create the function body by recursing on the structure of x *)
    gFun ["x"] (fun [x] -> shrink_body x)
  in
  debug_coq_expr shrink_fun;
  gRecord [("shrink", shrink_fun)]

let show_decl ty_ctr ctrs _iargs =
  msg_debug (str "Deriving Show Information:" ++ fnl ());
  msg_debug (str ("Type constructor is: " ^ ty_ctr_to_string ty_ctr) ++ fnl ());
  msg_debug (str (str_lst_to_string "\n" (List.map ctr_rep_to_string ctrs)) ++ fnl());

  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  (* Create the function body by recursing on the structure of x *)
  let show_body x =
    
    let branch aux (ctr,ty) =
      
      (ctr, generate_names_from_type "p" ty,
       fun vs -> match vs with 
                 | [] -> gStr (constructor_to_string ctr) 
                 |_ -> str_append (gStr (constructor_to_string ctr ^ " "))
                                  (fold_ty_vars (fun _ v ty' -> smart_paren (gApp (if isCurrentTyCtr ty' then gVar aux else gInject "show") [gVar v]))
                                                (fun s1 s2 -> if s2 = emptyString then s1 else str_appends [s1; gStr " "; s2]) emptyString ty vs))
    in
    
    gRecFunIn "aux" ["x'"]
              (fun (aux, [x']) -> gMatch (gVar x') (List.map (branch aux) ctrs))
              (fun aux -> gApp (gVar aux) [gVar x])
  in
  
  let show_fun = gFun ["x"] (fun [x] -> show_body x) in
  gRecord [("show", show_fun)]
          
