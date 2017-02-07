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
type derivable = Show | Arbitrary | Size

let list_last l = List.nth l (List.length l - 1)
let list_init l = List.rev (List.tl (List.rev l))
let list_drop_every n l =
  let rec aux i = function
    | [] -> []
    | x::xs -> if i == n then aux 1 xs else x::aux (i+1) xs
  in aux 1 l

let print_der = function
  | Show -> "Show"
  | Arbitrary -> "Arbitrary"
  | Size -> "Size"

let debug_environ () =
  let env = Global.env () in
  let preEnv = Environ.pre_env env in
  let minds = preEnv.env_globals.env_inductives in
  Mindmap_env.iter (fun k _ -> msgerr (str (MutInd.debug_to_string k) ++ fnl())) minds

let rec replace v x = function
  | [] -> []
  | y::ys -> if y = v then x::ys else y::(replace v x ys)

(* Generic derivation function *)
let debugDerive (c : constr_expr) =
  match coerce_reference_to_dt_rep c with
  | Some dt -> msgerr (str (dt_rep_to_string dt) ++ fnl ())
  | None -> failwith "Not supported type"  

(* Generic derivation function *)
let derive (cn : derivable) (c : constr_expr) (instance_name : string) (extra_name : string) =

  let (ty_ctr, ty_params, ctrs) =
    match coerce_reference_to_dt_rep c with
    | Some dt -> dt
    | None -> failwith "Not supported type"  in

  let coqTyCtr = gTyCtr ty_ctr in
  let coqTyParams = List.map gTyParam ty_params in

  let full_dt = gApp coqTyCtr coqTyParams in

  let class_name = match cn with
    | Show -> "QuickChick.Show.Show"
    | Size -> "QuickChick.GenLow.GenLow.CanonicalSize"
    | Arbitrary -> "QuickChick.Arbitrary.Arbitrary" in

  (* Generate typeclass constraints. For each type parameter "A" we need `{_ : <Class Name> A} *)
  let instance_arguments =
    List.concat (List.map (fun tp ->
                           [ gArg ~assumName:tp ~assumImplicit:true ();
                             gArg ~assumType:(gApp (gInject class_name) [tp]) ~assumGeneralized:true ()]
                          ) coqTyParams) in

  (* The instance type *)
  let instance_type iargs = gApp (gInject class_name) [full_dt] in

  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  let isBaseBranch ty = fold_ty' (fun b ty' -> b && not (isCurrentTyCtr ty')) true ty in

  (* Create the instance record. Only need to extend this for extra instances *)
  let instance_record iargs =

    match cn with
    | Show ->

       (* Create the function body by recursing on the structure of x *)
       let show_body x =

         let branch aux (ctr,ty) =

           (ctr, generate_names_from_type "p" ty,
            fun vs -> str_append (gStr (constructor_to_string ctr ^ "  "))
                                 (fold_ty_vars (fun _ v ty' -> str_appends [ gStr "( "
                                                                           ; gApp (if isCurrentTyCtr ty' then gVar aux else gInject "show") [gVar v]
                                                                           ; gStr " )"
                                                                           ])
                                               (fun s1 s2 -> str_appends [s1; gStr " "; s2]) emptyString ty vs))
         in

         gRecFunIn "aux" ["x'"]
                   (fun (aux, [x']) -> gMatch (gVar x') (List.map (branch aux) ctrs))
                   (fun aux -> gApp (gVar aux) [gVar x])
       in

       let show_fun = gFun ["x"] (fun [x] -> show_body x) in
       gRecord [("show", show_fun)]

    | Arbitrary ->
       msgerr (str "Here" ++ fnl ());
       (* Create the function body by recursing on the structure of x *)
       let arbitrary_decl =

         (* Need reverse fold for this *)
         let create_for_branch tyParams ps rec_name size (ctr, ty) =
           let rec aux i acc ty : coq_expr =
             match ty with
             | Arrow (ty1, ty2) ->
                bindGen (if isCurrentTyCtr ty1 then gApp (gVar rec_name) (gVar size :: List.map gVar ps) else gInject "arbitrary")
                        (Printf.sprintf "p%d" i)
                        (fun pi -> aux (i+1) ((gVar pi) :: acc) ty2)
             | _ -> returnGen (gApp ~explicit:true (gCtr ctr) (tyParams @ List.rev acc))
           in aux 0 [] ty in

         let bases = List.filter (fun (_, ty) -> isBaseBranch ty) ctrs in
         let aux_arb =
             let explicitly_typed_arguments =
               List.concat (List.map (fun tp ->
                           [ gArg ~assumName:tp ();
                             gArg ~assumName:(gVar (make_up_name())) ~assumType:(gApp (gInject class_name) [tp]) ()]
                          ) coqTyParams) in

             gRecFunInWithArgs
               "aux_arb" (gArg ~assumName:(gInject "size") () :: explicitly_typed_arguments)
               (fun (aux_arb, size::ps) ->
                let tyParams = List.map gVar (list_drop_every 2 ps) in
                gMatch (gVar size)
                       [(injectCtr "O", [],
                         fun _ -> oneof (List.map (create_for_branch tyParams ps aux_arb size) bases))
                       ;(injectCtr "S", ["size'"],
                         fun [size'] -> frequency (List.map (fun (ctr,ty') ->
                                                             ((if isBaseBranch ty' then gInt 1 else gVar size),
                                                              create_for_branch tyParams ps aux_arb size' (ctr,ty'))) ctrs))
                       ])
               (fun x -> gVar x) in

         let fn = defineConstant extra_name aux_arb in
         msgerr (str "Defined" ++ fnl ());

         gApp (gInject "sized") [gFun ["s"] (fun [s] -> gApp (gVar fn) ((gVar s) :: List.map gVar iargs))]
       in

       (* Shrinking function *)
       let shrink_body x =
         let create_branch aux_shrink (ctr, ty) =
           (ctr, generate_names_from_type "p" ty,
            fold_ty_vars (fun allParams v ty' ->
                          let liftNth = gFun ["shrunk"]
                                             (fun [shrunk] -> gApp ~explicit:true (gCtr ctr)
                                                                   (coqTyParams @ (replace (gVar v) (gVar shrunk) (List.map gVar allParams)))) in
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

       let shrink_decl = gFun ["x"] (fun [x] -> shrink_body x) in

       gRecord [("arbitrary", arbitrary_decl); ("shrink", shrink_decl)]
    | Size ->
       let sizeOf_body x =
         let create_branch rec_name (ctr, ty) =
           (ctr, generate_names_from_type "p" ty,
            if isBaseBranch ty then fun _ -> gInt 0
            else fun vs ->
                 let opts = fold_ty_vars (fun _ v ty' ->
                                          if isCurrentTyCtr ty' then [(gApp (gVar rec_name) [gVar v])]
                                          else []) (fun l1 l2 -> l1 @ l2) [] ty vs in
                 gApp (gInject "S") [maximum opts]) in

         gRecFunIn "aux_size" ["x'"]
                   (fun (aux_size, [x']) -> gMatch (gVar x') (List.map (create_branch aux_size) ctrs))
                   (fun aux_size -> gApp (gVar aux_size) [gVar x]) in
       let sizeOf_decl = gFun ["x"] (fun [x] -> sizeOf_body x) in
       gRecord [("sizeOf", sizeOf_decl)]
  in

  declare_class_instance instance_arguments instance_name instance_type instance_record

(* Set library generics *)
let sizeEqType (ty_ctr, ty_params, ctrs) =

  (* Common helpers, refactor? *)
  let coqTyCtr = gTyCtr ty_ctr in
  let coqTyParams = List.map gTyParam ty_params in
  let full_dt = gApp coqTyCtr coqTyParams in

  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in
  let isBaseBranch ty = fold_ty' (fun b ty' -> b && not (isCurrentTyCtr ty')) true ty in

  let bases = List.filter (fun (_, ty) -> isBaseBranch ty) ctrs in

  (* Second reverse fold necessary *)
  let create_branch ltf size tps (ctr,ty) =
    let non_class_tps = List.map gVar (list_drop_every 2 tps) in
    let rec aux i acc ty : coq_expr =
      match ty with
      | Arrow (ty1, ty2) ->
         let fi = Printf.sprintf "f%d" i in
         set_bigcup fi (if isCurrentTyCtr ty1 then gFun [fi] (fun [f] -> ltf (gApp (gInject "sizeOf") [gVar f]) size)
                        else gFun [fi] (fun _ -> gInject "True"))
                    (fun f -> aux (i+1) (f::acc) ty2)
      | _ -> set_singleton (gApp ~explicit:true (gCtr ctr) (non_class_tps @ (List.map gVar (List.rev acc)))) in
    aux 0 [] ty in

  let tp_args =
    List.concat (List.map (fun tp ->
                           [ gArg ~assumName:tp ~assumImplicit:true ();
                             gArg (* ~assumName:(gVar (make_up_name())) *)
                                  ~assumType:(gApp (gInject "QuickChick.GenLow.GenLow.CanonicalSize") [tp]) ~assumGeneralized:true ()]
                          ) coqTyParams) in

  let size_zero =
    match tp_args with
    | [] -> set_eq (set_unions (List.map (create_branch glt hole []) bases))
                   (set_suchThat "x" full_dt (fun x -> gle (gApp (gInject "sizeOf") [gVar x]) (gInt 0))) 
    | _ -> 
       gFunWithArgs tp_args
                    (fun tps -> set_eq (set_unions (List.map (create_branch glt hole tps) bases))
                                       (set_suchThat "x" full_dt (fun x -> gle (gApp (gInject "sizeOf") [gVar x]) (gInt 0))))
  in

  let lhs size tps = set_unions (List.map (create_branch glt (gVar size) tps) ctrs) in
  let rhs size = set_suchThat "x" full_dt (fun x -> gle (gApp (gInject "sizeOf") [gVar x]) (gVar size)) in

  let size_eq =
    gFunWithArgs (gArg ~assumName:(gInject "size") () :: tp_args)
                 (fun (size::tps) -> set_eq (lhs size tps) (rhs size)) in
  
  let size_succ =
    gFunWithArgs (gArg ~assumName:(gInject "size") () :: tp_args)
         (fun (size::tps) ->
          set_eq (set_unions (List.map (create_branch gle (gVar size) tps) ctrs))
                 (set_suchThat "x" full_dt (fun x -> gle (gApp (gInject "sizeOf") [gVar x]) (gSucc (gVar size))))
         ) in

  (size_eq, size_zero, size_succ, lhs, rhs)

let deriveSizeEqs c s =
  let dt = match coerce_reference_to_dt_rep c with
    | Some dt -> dt
    | None -> failwith "Not supported type"  in
  let (eq, zero, succ, _, _) = sizeEqType dt in
  ignore (defineConstant (s ^ "_eqT") eq); 
  ignore (defineConstant (s ^ "_zeroT") zero);
  ignore (defineConstant (s ^ "_succT") succ)


let deriveEqProof (ty_ctr, ty_params, ctrs) (lhs : var -> var list -> coq_expr)
    (rhs : var -> coq_expr) (ind_scheme : coq_expr) =
  (* copy paste from above -- refactor! *)
  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  let isBaseBranch ty = fold_ty' (fun b ty' -> b && not (isCurrentTyCtr ty')) true ty in
  (* copy paste ends *)

  (* TODO apply sizeOf to params (?) *)

  let deriveBaseCase inj (ctr, ty) (size : var) (params : var list) =
    let non_class_tps = List.map gVar (list_drop_every 2 params) in
    (* partially applied constructor *)
    let ctr_params = gApp ~explicit:true ctr non_class_tps in
    let c_left = fun l -> gApp (gInject "leq0n") [gVar size] in
    let rec c_right cty (args : var list) (fargs : var list) (cargs : var list) (n : int)
      : coq_expr * (var list -> coq_expr) =
      match cty with
      | Arrow (ty1, ty2) ->
        (match args with
         | [] -> failwith "Internal: Wrong number of arguments"
         | arg :: args ->
           let x = Printf.sprintf "y%d" n in
           let (term, typ) = c_right ty2 args fargs (arg :: cargs) (n+1) in
           let typ' = fun i -> gConj gT (typ (i :: cargs)) in
           (gExIntro_impl (gVar arg) (gConjIntro gI term),
            fun l -> gEx x (fun i -> gConj gI (typ (i :: l)))))
      | _ ->
        (gEqRefl (gApp ctr_params (List.map gVar fargs)),
         fun l -> gEqType (gApp ctr_params (List.rev (List.map gVar l)))
             (gApp ctr_params (List.map gVar fargs)))
    in
    let rec gen_args cty n =
      match cty with
      | Arrow (ty1, ty2) ->
        let x = Printf.sprintf "x%d" n in
        x :: (gen_args ty2 (n+1))
      | _ -> []
    in
    let args = gen_args ty 0 in
    let lhs_type l = gApp (lhs size params) [gApp ctr_params (List.map gVar l)] in
    let rhs_type l = gApp (rhs size) [gApp ctr_params (List.map gVar l)] in
    (gFun args
       (fun l ->
          gConjIntro
            (gFunTyped [("z", lhs_type l)]
               (fun [x1] -> gAnnot (c_left (l @ [x1])) (rhs_type l)))
            (gFunTyped [("z", rhs_type l)]
               (fun [x1] -> gAnnot (inj (fst (c_right ty l l [] 0))) (lhs_type l)))))
  in
  let deriveIndCase inj (ctr, ty) (size : var) (params : var list) =
    let non_class_tps = List.map gVar (list_drop_every 2 params) in
    (* partially applied constructor *)
    let ctr_params = gApp ~explicit:true (gCtr ctr) non_class_tps in
    let c_left h_un =
      let discriminate (h : var) : coq_expr =
        (* non-dependent pattern matching here, Coq should be able to infer
           the return type. TODO : change it to dep. pattern matching *)
        gMatch (gVar h) [(injectCtr "erefl", [], fun [] -> gI)]
      in
      let rec proof (h : var) ty leq flag n : coq_expr =
        match ty with
        | Arrow (ty1, ty2) ->
          let w' = Printf.sprintf "w%d" n in
          let hw' = Printf.sprintf "Hw%d" n in
          let hc1 = Printf.sprintf "Hc1_%d" n in
          let hc2 = Printf.sprintf "Hc2_%d" n in
          gMatch (gVar h)
            [(injectCtr "ex_intro", [w'; hw'],
              fun [w'; hw'] ->
                gMatch (gVar hw')
                  [(injectCtr "conj", [hc1; hc2],
                    fun [hc1; hc2] ->
                      let leq' =
                        if isCurrentTyCtr ty1 then
                          (gVar hc1) :: leq
                        else leq
                      in
                      proof hc2 ty2 leq' flag (n+1) 
                   )]
             )]
        | _ ->
          if flag then 
            let rec leq_proof = function
              | [h] -> h
              | h :: hs ->
                gApp (gInject "max_lub_ssr") [hole; hole; hole; h; leq_proof hs]
            in
            gMatch (gVar h) [(injectCtr "erefl", [], fun [] -> leq_proof (List.rev leq))]
          else discriminate h
      in
      let rec elim_union (ctrs : ctr_rep list) (h : var) n : coq_expr =
        match ctrs with
        (* type with no constructors, isomorphic to False *)
        | [] -> gMatch (gVar h) []
        (* Last contructor, no further case analysis *)
        | [(ctr', ty)] ->  proof h ty [] (ctr = ctr') 0
        | (ctr', ty) :: ctrs' ->
          let h' = Printf.sprintf "H%d" n in
          gMatch (gVar h)
            [(injectCtr "or_introl", [h'],
              fun [h'] -> proof h' ty [] (ctr = ctr') 0);
             (injectCtr "or_intror", [h'],
              fun [h'] -> elim_union ctrs' h' (n+1))
            ]
      in elim_union ctrs h_un 0
    in
    let rec c_right cty (args : var list) (fargs : var list) (cargs : var list) (iargs : var list)
        (leq : coq_expr) (n : int)
      : coq_expr * (var list -> coq_expr) =
      match cty with
      | Arrow (ty1, ty2) ->
        (match args with
         | [] -> failwith "Internal: Wrong number of arguments"
         | arg :: args ->
           let x = Printf.sprintf "y%d" n in
           let (leq_l, leq_r, iargs') =
             if isCurrentTyCtr ty1
             then
               (match iargs with
                | [arg] ->
                  (leq, leq, [])
                | arg :: args ->
                  (gApp (gInject "max_lub_l_ssr") [hole; hole; hole; leq],
                   gApp (gInject "max_lub_r_ssr") [hole; hole; hole; leq],
                   args))
             else (gI, leq, iargs)
           in
           let (term, typ) = c_right ty2 args fargs (arg :: cargs) iargs' leq_r (n+1) in
           let typ' = fun i -> gConj hole (typ (i :: cargs)) in
           (gExIntro_impl (gVar arg) (gConjIntro leq_l term),
            fun l -> gEx x (fun i -> gConj hole (typ (i :: l)))))
      | _ ->
        (gEqRefl (gApp ctr_params (List.map gVar fargs)),
         fun l -> gEqType (gApp ctr_params (List.rev (List.map gVar l)))
             (gApp ctr_params (List.map gVar fargs)))
    in
    let rec gen_args cty n =
      match cty with
      | Arrow (ty1, ty2) ->
        if isCurrentTyCtr ty1
        then
          let x  = Printf.sprintf "x%d" n in
          let ih = Printf.sprintf "IHx%d" n in
          x :: ih :: (gen_args ty2 (n+1))
        else
          let x  = Printf.sprintf "x%d" n in
          x :: (gen_args ty2 (n+1))
      | _ -> []
    in
    let rec disposeIH cty l =
      match cty with
      | Arrow (ty1, ty2) ->
        (if isCurrentTyCtr ty1
         then
           match l with
           | x :: ihx :: l ->
             let (l', iargs) = disposeIH ty2 l in 
             (x :: l', (x :: iargs))
           | _ -> failwith "Internal: Wrong number of arguments" 
         else
           match l with
           | x :: l ->
             let (l', iargs) = disposeIH ty2 l in 
             (x :: l', iargs)
           | _ -> failwith "Internal: Wrong number of arguments")
      | _ -> ([], [])
    in
    let args = gen_args ty 0 in
    let lhs_type l = gApp (lhs size params) [gApp ctr_params (List.map gVar l)] in
    let rhs_type l = gApp (rhs size) [gApp ctr_params (List.map gVar l)] in
    (gFun args
       (fun l ->
          let (l', iargs) = disposeIH ty l in
          gConjIntro
            (gFunTyped [("Hun", lhs_type l')]
               (fun [x1] -> gAnnot (c_left x1) (rhs_type l')))
            (gFunTyped [("Hleq", rhs_type l')]
               (fun [x1] -> gAnnot (inj (fst (c_right ty l' l' [] iargs (gVar x1) 0))) (lhs_type l')))))
  in
  let rec deriveCases (inj : coq_expr -> coq_expr) size params : ctr_rep list -> coq_expr list = function
    (* consider last constructor separately so we do not generate left injection *)
    | [(ctr, ty)] ->
      [if isBaseBranch ty then deriveBaseCase inj (gCtr ctr, ty) size params
       else deriveIndCase inj (ctr, ty) size params]
    | (ctr, ty) :: ctrs ->
      let inj_l (e : coq_expr) : coq_expr = inj (gOrIntroL e) in
      let inj_r (e : coq_expr) : coq_expr = inj (gOrIntroR e) in
      (if isBaseBranch ty then deriveBaseCase inj_l (gCtr ctr, ty) size params
       else  deriveIndCase inj_l (ctr, ty) size params) :: (deriveCases inj_r size params ctrs)
  in
  let expr_lst size params = deriveCases (fun x -> x) size params ctrs in
  let typ size params =
    gFun ["f"] (fun [f] -> gIff (gApp (lhs size params) [gVar f]) (gApp (rhs size) [gVar f]))
  in

  let coqTyParams = List.map gTyParam ty_params in
  let tp_args =
    List.concat (List.map (fun tp ->
                           [ gArg ~assumName:tp ~assumImplicit:true ();
                             gArg (* ~assumName:(gVar (make_up_name())) *)
                                  ~assumType:(gApp (gInject "QuickChick.GenLow.GenLow.CanonicalSize") [tp]) ~assumGeneralized:true ()]
                          ) coqTyParams) in
  gFunWithArgs tp_args
    (fun tps ->
     gFun ["size"]
          (fun [size] ->
               let non_class_tps = List.map gVar (list_drop_every 2 tps) in
               gApp ind_scheme ~explicit:true (non_class_tps @ ((typ size tps) :: (expr_lst size tps)))))

let deriveEqProofZero (ty_ctr, ty_params, ctrs) (zero_eq_typ : coq_expr)
    (eq_proof : coq_expr) : coq_expr =
  (* copy paste from above -- refactor! *)
  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  let isBaseBranch ty = fold_ty' (fun b ty' -> b && not (isCurrentTyCtr ty')) true ty in
  (* copy paste ends *)

  (* Proof that (set for inductive case) <--> set0*)
  let rec elim_ind_case ty : coq_expr =
    match ty with
    | Arrow (t1, t2) ->
      if isCurrentTyCtr t1 then
        gApp (gInject "bigcup_set0_l_eq")
          [hole; gFun ["f"] (fun [f] -> gConjIntro (gFun ["H"] (fun [h] -> false_ind hole (gApp (gInject "lt0_False") [gVar h])))
                                              (gFun ["H"] (fun [h]-> false_ind hole (gVar h))))]
      else
        gApp (gInject "bigcup_set0_r")
          [hole; gFun ["f"] (fun [f] -> elim_ind_case t2)]
    | _ -> failwith "Internal error: The inductive case must have at least an application of the type "
  in
  let rec deriveCases base_ctrs ctrs : coq_expr =
    match base_ctrs with
    | [] ->
      (match ctrs with
       | [(ctr', ty')] -> elim_ind_case ty'
       | (ctr', ty') :: ctrs' ->
         setU_set0_l (elim_ind_case ty') (deriveCases base_ctrs ctrs'))
    | [(ctr, ty)] ->
      (match ctrs with
       | [(ctr', ty')] ->
         if ctr = ctr'
         then
           set_eq_refl hole
         else
           failwith "Internal error"
       | (ctr', ty') :: ctrs' ->
         if ctr = ctr'
         then
           setU_set0_neut_eq hole (deriveCases [] ctrs')
         else
           setU_set0_r (elim_ind_case ty') (deriveCases base_ctrs ctrs'))
    | (ctr, ty) :: base_ctrs' ->
      (match ctrs with
       | [(ctr', ty')] ->
         if ctr = ctr'
         then
           set_eq_refl hole
         else
           failwith "Internal error"
       | (ctr', ty') :: ctrs' ->
         if ctr = ctr'
         then
           setU_set_eq_compat (set_eq_refl hole) (deriveCases base_ctrs' ctrs')
         else
           setU_set0_r (elim_ind_case ty') (deriveCases base_ctrs ctrs'))
  in
  let (base_ctrs : ctr_rep list) = List.filter (fun x -> isBaseBranch (snd x)) ctrs in 
  let coqTyParams = List.map gTyParam ty_params in
  let tp_args =
    List.concat (List.map (fun tp ->
                           [ gArg ~assumName:tp ~assumImplicit:true ();
                             gArg ~assumName:(gVar (make_up_name()))
                                  ~assumType:(gApp (gInject "QuickChick.GenLow.GenLow.CanonicalSize") [tp]) ~assumGeneralized:true ()]
                          ) coqTyParams) in
  let term =
    gFunWithArgs tp_args
      (fun tps ->
         gAnnot (set_eq_trans (deriveCases base_ctrs ctrs) (gApp eq_proof ((List.map gVar tps) @ [gInject "O"])))
                (gApp zero_eq_typ (List.map gVar tps)))
  in term

let deriveEqProofSucc (ty_ctr, ty_params, ctrs) (succ_eq_typ : coq_expr)
    (eq_proof : coq_expr) : coq_expr =
  (* copy paste from above -- refactor! *)
  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  let isBaseBranch ty = fold_ty' (fun b ty' -> b && not (isCurrentTyCtr ty')) true ty in
  (* copy paste ends *)

  let rec elim_case ty : coq_expr =
    let same_index ty : coq_expr =
      if isCurrentTyCtr ty then
        gConjIntro (gFun ["H"] (fun [h] -> gApp (gInject "leq_ltS") [gVar h]))
          (gFun ["H"] (fun [h] -> gApp (gInject "ltS_leq") [gVar h]))
      else
        gConjIntro (gFun ["H"] (fun [h] -> gVar h))
          (gFun ["H"] (fun [h]-> gVar h))
    in
    match ty with
    (* no big union, just singleton *)
    | TyCtr _ | TyParam _ -> set_eq_refl hole
    (* The last big union *)
    | Arrow (t1, TyCtr _) | Arrow (t1, TyParam _) ->
      gApp (gInject "eq_bigcupl")
        [hole; hole;
         gFun ["f"] (fun [f] -> same_index t1)]
    | Arrow (t1, t2) ->
        gApp (gInject "eq_bigcup'")
          [gFun ["f"] (fun [f] -> same_index t1); gFun ["x"] (fun x -> elim_case t2)]
  in
  let rec deriveCases ctrs : coq_expr =
    match ctrs with
    | [(ctr, ty)] -> elim_case ty
    | (ctr, ty) :: ctrs' ->
      setU_set_eq_compat (elim_case ty) (deriveCases ctrs')
  in
  let coqTyParams = List.map gTyParam ty_params in
  let tp_args =
    List.concat (List.map (fun tp ->
                           [ gArg ~assumName:tp ~assumImplicit:true ();
                             gArg ~assumName:(gVar (make_up_name()))
                                  ~assumType:(gApp (gInject "QuickChick.GenLow.GenLow.CanonicalSize") [tp]) ~assumGeneralized:true ()]
                          ) coqTyParams) in
  let term =
    gFunWithArgs tp_args
      (fun tps ->
         gFun ["size"]
           (fun [size] ->
              gAnnot (set_eq_trans (deriveCases ctrs) (gApp eq_proof ((List.map gVar tps) @ [gSucc (gVar size)])))
                (gApp succ_eq_typ ((gVar size) :: (List.map gVar tps)))))
  in term

let deriveSizeEqProof c s =
  let dt = match coerce_reference_to_dt_rep c with
    | Some dt -> dt
    | None -> failwith "Not supported type"  in
  let (_, zero_typ, succ_typ, lhs, rhs) = sizeEqType dt in
  let (ty_ctr, _, _) = dt in
  let ind = gInject ((ty_ctr_to_string ty_ctr) ^ "_rect") in
  let eqproof = deriveEqProof dt lhs rhs ind in
  let zeroproof = deriveEqProofZero dt zero_typ eqproof in
  let succproof = deriveEqProofSucc dt succ_typ eqproof in
  ignore (defineConstant (s ^ "_eq_proof") eqproof);
  (* debug_coq_expr eqproof; *)
  ignore (defineConstant (s ^ "_eq_proof_O") zeroproof);
  ignore (defineConstant (s ^ "_eq_proof_S") succproof)
  (* debug_coq_expr succproof; *)

VERNAC COMMAND EXTEND DeriveShow
  | ["DeriveShow" constr(c) "as" string(s)] -> [derive Show c s ""]
END;;

VERNAC COMMAND EXTEND DeriveArbitrary
  | ["DeriveArbitrary" constr(c) "as" string(s1) string(s2)] -> [derive Arbitrary c s1 s2]
END;;

VERNAC COMMAND EXTEND DeriveSize
  | ["DeriveSize" constr(c) "as" string(s)] -> [derive Size c s ""]
END;;

VERNAC COMMAND EXTEND DeriveSizeEqs
  | ["DeriveSizeEqs" constr(c) "as" string(s)] -> [deriveSizeEqs c s]
END;;

VERNAC COMMAND EXTEND DebugDerive
  | ["DebugDerive" constr(c)] -> [debugDerive c]
END;;

VERNAC COMMAND EXTEND DeriveSizeEqsProof
  | ["DeriveSizeEqsProof" constr(c) "as" string(s)] -> [deriveSizeEqProof c s]
END;;

(* Advanced Generators *)

type name_provider = { next_name : unit -> string }

let mk_name_provider s = 
  let cnt = ref 0 in
  { next_name = fun () -> 
      let res = s ^ string_of_int !cnt in
      incr cnt;
      res 
  }

(* Ranges are undefined, unknowns or constructors applied to ranges *)
type unknown = string

type range = Ctr of constructor * range list | Unknown of unknown | Undef | FixedInput

module UM = Map.Make(String)

type umap = range UM.t

let lookup k m = try Some (UM.find k m) with Not_found -> None

(* For equality handling: require ordered (String, String) *)
module OrdTSS = struct 
  type t = unknown * unknown
  let compare x y = compare x y
end

module EqSet = Set.Make(OrdTSS)

let eq_set_add u1 u2 eqs = 
  let (u1', u2') = if u1 < u2 then (u1, u2) else (u2, u1) in
  EqSet.add (u1', u2') eqs

type matcher_pat = 
  | MatchCtr of constructor * matcher_pat list
  | MatchU of unknown

type matcher = unknown * matcher_pat

let unk_provider = mk_name_provider "unkn"

(* Match a constructor/ranges list to a fixed input *)
(* Range list is toplevel, so it's mostly unifications.
   If any of the unknowns in rs is "FixedInput", then 
   we need to create a fresh unknown, bind it to the other unknown and 
   raise an equality check *)
let rec raiseMatch (k : umap) (c : constructor) (rs : range list) (eqs: EqSet.t) 
        : (umap * matcher_pat * EqSet.t) option = 
  foldM (fun (k, l, eqs) r ->
         match r with 
         | Ctr (c', rs') ->
            raiseMatch k c' rs' eqs >>= fun (k', m, eqs') ->
            Some (k', m::l, eqs')
         | Unknown u ->
            lookup u k >>= fun r' ->
            begin match r' with 
            | Undef -> (* The unknown should now be fixed *)
               Some (UM.add u FixedInput k, (MatchU u)::l, eqs)
            | FixedInput -> (* The unknown is already fixed, raise an eq check *)
               let u' = unk_provider.next_name () in
               Some (UM.add u' (Unknown u) k, (MatchU u')::l, eq_set_add u' u eqs)
            | _ -> failwith "Not supported yet"
            end
        ) (Some (k, [], eqs)) rs >>= fun (k', l, eqs') ->
  Some (k', MatchCtr (c, List.rev l), eqs')

(* Invariants: 
   -- Everything has a binding, even if just Undef 
   -- r1, r2 are never FixedInput, Undef (handled inline)
   -- TopLevel ranges can be unknowns or constructors applied to toplevel ranges
   -- Constructor bindings in umaps are also toplevel. 
   -- Only unknowns can be bound to Undef/FixedInput
 *) 
let rec unify (k : umap) (r1 : range) (r2 : range) (eqs : EqSet.t)
        : (umap * range * EqSet.t * matcher list) option =
  match r1, r2 with
  | Unknown u1, Unknown u2 ->
     if u1 == u2 then Some (k, Unknown u1, eqs, []) else
     lookup u1 k >>= fun r1 -> 
     lookup u2 k >>= fun r2 ->
     begin match r1, r2 with 
     (* "Hard" case: both are fixed. Need to raise an equality check on the inputs *)
     | FixedInput, FixedInput -> 
        let (u1', u2') = if u1 < u2 then (u1, u2) else (u2, u1) in
        (* Need to insert an equality between u1 and u2 *)
        let eqs' = EqSet.add (u1, u2) eqs in 
        (* Unify them in k *)
        Some (UM.add u1' (Unknown u2') k, Unknown u1', eqs', [])

     (* Easy cases: When at least one is undefined, it binds to the other *)
     (* Can probably replace fixed input with _ *)
     | Undef, Undef ->
        let (u1', u2') = if u1 < u2 then (u1, u2) else (u2, u1) in
        Some (UM.add u1' (Unknown u2') k, Unknown u1', eqs, [])
     | _, Undef ->
        Some (UM.add u2 (Unknown u1) k, Unknown u2, eqs, [])
     | Undef, _ ->
        Some (UM.add u1 (Unknown u2) k, Unknown u1, eqs, [])

     (* Constructor bindings *) 
     | Ctr (c1, rs1), Ctr (c2, rs2) ->
        if c1 == c2 then 
          foldM (fun b a -> let (r1, r2) = a in 
                            let (k, l, eqs, ms) = b in 
                            unify k r1 r2 eqs >>= fun res ->
                            let (k', r', eqs', ms') = res in 
                            Some (k', r'::l, eqs', ms @ ms')
                ) (Some (k, [], eqs, [])) (List.combine rs1 rs2) >>= fun (k', rs', eqs', ms) ->
          Some (k', Ctr (c1, List.rev rs'), eqs', ms)
        else None

     (* Last hard cases: Constructors vs fixed *) 
     | FixedInput, Ctr (c, rs) ->
        (* Raises a match and potential equalities *)
        raiseMatch k c rs eqs >>= fun (k', m, eqs') ->
        Some (UM.add u1 (Unknown u2) k', Unknown u1, eqs', [(u1, m)])
     | Ctr (c, rs), FixedInput ->
        (* Raises a match and potential equalities *)
        raiseMatch k c rs eqs >>= fun (k', m, eqs') ->
        Some (UM.add u2 (Unknown u1) k', Unknown u2, eqs', [(u2, m)])
     end


(*          


  | Unknown u, FixedInput -> 
     lookup u k >>= fun r -> (* EVERYTHING should have a binding, even if just Undef *)
     match r with 
     | 
     
  | FixedInput, Unknown u ->
     begin match lookup u k with
     | Some r ->
        unify k r FixedInput >>= fun (k', r') ->
        Some (UM.add u r' k', Unknown u)
     | None -> Some (UM.add u FixedInput k, Unknown u)
     end
  | Unknown u1, Unknown u2 ->
     if u1 == u2 then Some (k, Unknown u1)
     else let (u1', u2') = if u1 < u2 then (u1, u2) else (u2, u1) in
          begin match lookup u1 k, lookup u2 k with
          | Some r1, Some r2 ->
             begin match unify k r1 r2 with
             | Some (k', r') -> Some (UM.add u1' (Unknown u2') (UM.add u2' r' k'), Unknown u1')
             | None -> None
             end
          | Some r, None
          | None, Some r -> Some (UM.add u1' (Unknown u2') (UM.add u2' r k), Unknown u1')
(*           | None, None -> None - LEO: Should be an error case - commenting out to see if it happens *)
          end

  | Ctr (c1, rs1), Ctr (c2, rs2) ->
     if c1 == c2 then
       begin match foldM (fun b a -> let (r1, r2) = a in
                               let (k, l) = b in
                               unify k r1 r2 >>= fun b' ->
                               let (k', r') = b' in
                               Some (k', r'::l)
                            ) (Some (k , [])) (List.combine rs1 rs2) with
       | Some (k', rs) -> Some (k', Ctr (c1, List.rev rs))
       | None -> None
       end
     else None
  | _, _ -> None

 *)

let deriveDependent c nc gen_name = 
  let n = parse_integer nc in
  let (ty_ctr, ty_params, ctrs, dep_type) = 
    match coerce_reference_to_dep_dt c with
    | Some dt -> msgerr (str (dep_dt_to_string dt) ++ fnl()); dt 
    | None -> failwith "Not supported type" in 

  let rec is_dep_type = function
    | DArrow (dt1, dt2) -> is_dep_type dt1 || is_dep_type dt2 
    | DProd ((_, dt1), dt2) -> is_dep_type dt1 || is_dep_type dt2 
    | DTyParam _ -> false
    | DTyVar _ -> true
    | DCtr _ -> true
    | DTyCtr (_, dts) -> List.exists is_dep_type dts
  in 

  msgerr (str (string_of_int n) ++ fnl ());
  let gen_type = gGen (gOption (gType ty_params (nthType n dep_type))) in
  debug_coq_expr (gType ty_params dep_type);

  let gen = mk_name_provider "gen" in
  let dec = mk_name_provider "dec" in 

  (* Handling a branch: returns the generator and a boolean (true if base branch) *)
  let handle_branch (c : dep_ctr) : (coq_expr * bool) = 
    let (ctr, typ) = c in
    let b = ref true in 

    let register_unknowns map = 
      let rec aux map = function
        | DArrow (dt1, dt2) -> aux map dt2
        | DProd ((x, dt1), dt2) -> aux (UM.add (ty_var_to_string x) Undef map) dt2
        | _ -> map in
      aux map typ
    in 
    
    let init_map = register_unknowns UM.empty in

    (* Debugging *)
    msgerr (str ("Handling branch: " ^ dep_type_to_string typ) ++ fnl ());
    UM.iter (fun x _ -> msgerr (str ("Bound: " ^ x) ++ fnl ())) init_map;

    dep_fold_ty (fun _ dt1 -> msgerr (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
                (fun _ _ dt1 -> msgerr (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
                (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) typ;
    (* End debugging *)

    (hole ,!b)
  in

  List.iter (fun x -> ignore (handle_branch x)) ctrs;

  let aux_arb rec_name size vars = 
    gMatch (gVar size) 
           [ (injectCtr "O", [], 
              fun _ -> returnGen gNone) (* Base cases *)
           ; (injectCtr "S", ["size'"],
              fun [size'] -> returnGen gNone) (* Non-base cases *)
           ] in

  
  let generator_body = gRecFunIn 
                    ~assumType:(gen_type)
                    "aux_arb" ["size"] (fun (rec_name, size::vars) -> aux_arb rec_name size vars) 
                                               (fun rec_name -> gVar rec_name)
  in

  let input_arguments = 
    let rec aux acc i = function
      | DArrow (dt1, dt2) 
      | DProd ((_,dt1), dt2) -> 
         if i == n then (* i == n means this is what we generate for - ignore *)
           aux acc (i+1) dt2
         else (* otherwise this needs to be an input argument *)
           aux ((gType ty_params dt1) :: acc) (i+1) dt2 
      | DTyParam tp -> acc
      | DTyCtr (c,dts) -> acc
      | DTyVar _ -> acc
    in aux [] 1 dep_type (* 1 because of using 1-indexed counting for the arguments *)       
  in 

  (* TODO: These should be generated through some writer monad *)
  let params = List.map (fun tp -> gArg ~assumName:(gTyParam tp) ()) ty_params in
  let inputs = List.mapi (fun i t -> gArg ~assumName:(gVar (fresh_name (Printf.sprintf "input%d" i))) ~assumType:t ()) (List.rev input_arguments) in
  let gen_needed = [] in
  let dec_needed = [] in

  
  let args = params
           @ inputs
           @ gen_needed
           @ dec_needed in

  let with_args = 
    match args with
    | [] -> generator_body
    | _  -> gFunWithArgs args (fun _ -> generator_body)
  in 

  let fn = defineTypedConstant gen_name with_args hole in
  ()

(*
       let arbitrary_decl =

         (* Need reverse fold for this *)
         let create_for_branch tyParams ps rec_name size (ctr, ty) =
           let rec aux i acc ty : coq_expr =
             match ty with
             | Arrow (ty1, ty2) ->
                bindGen (if isCurrentTyCtr ty1 then gApp (gVar rec_name) (gVar size :: List.map gVar ps) else gInject "arbitrary")
                        (Printf.sprintf "p%d" i)
                        (fun pi -> aux (i+1) ((gVar pi) :: acc) ty2)
             | _ -> returnGen (gApp ~explicit:true (gCtr ctr) (tyParams @ List.rev acc))
           in aux 0 [] ty in

         let bases = List.filter (fun (_, ty) -> isBaseBranch ty) ctrs in
         let aux_arb =
             let explicitly_typed_arguments =
               List.concat (List.map (fun tp ->
                           [ gArg ~assumName:tp ();
                             gArg ~assumName:(gVar (make_up_name())) ~assumType:(gApp (gInject class_name) [tp]) ()]
                          ) coqTyParams) in

             gRecFunInWithArgs
               "aux_arb" (gArg ~assumName:(gInject "size") () :: explicitly_typed_arguments)
               (fun (aux_arb, size::ps) ->
                let tyParams = List.map gVar (list_drop_every 2 ps) in
                gMatch (gVar size)
                       [(injectCtr "O", [],
                         fun _ -> oneof (List.map (create_for_branch tyParams ps aux_arb size) bases))
                       ;(injectCtr "S", ["size'"],
                         fun [size'] -> frequency (List.map (fun (ctr,ty') ->
                                                             ((if isBaseBranch ty' then gInt 1 else gVar size),
                                                              create_for_branch tyParams ps aux_arb size' (ctr,ty'))) ctrs))
                       ])
               (fun x -> gVar x) in

         let fn = defineConstant extra_name aux_arb in
         msgerr (str "Defined" ++ fnl ());

         gApp (gInject "sized") [gFun ["s"] (fun [s] -> gApp (gVar fn) ((gVar s) :: List.map gVar iargs))]
           in
           *)

VERNAC COMMAND EXTEND DependentDerive
  | ["DeriveDependent" constr(c) "for" constr(n) "as" string(s)] -> [deriveDependent c n s]
END;;

(*
type annotation = Size | Weight of int

(* Try to see if a constr represents a _W or _Size annotation *)
let get_annotation (c : Term.constr) : annotation option =
  if Term.eq_constr c (mk_constr "_Size") then Some Size
  else if Term.isApp c then
    let (c', cs) = Term.destApp c in
    if Term.eq_constr c' (mk_constr "_W") then
      Some (Weight number_of_apps cs.(0))
    else None
  else None

let rec strip_prod_aux (l : (Names.name * Term.constr) list) (t : Term.types) : (annotation * Term.types) =
  let ([(n,c)], t) = Term.decompose_prod_n 1 t in
  match get_annotation c with
  | Some Size -> (Size, Term.compose_prod l (Vars.lift (-1) t))
  | Some (Weight n) -> (Weight n, Term.compose_prod l (Vars.lift (-1) t))
  | None -> strip_prod_aux ((n,c)::l) t

let strip_prod (t : Term.types) : (annotation * Term.types) =
  strip_prod_aux [] t

let get_user_arity (i : Declarations.inductive_arity) : Term.constr =
  match i with
  | RegularArity ra -> ra.mind_user_arity
(* Template arity? *)

let strip_last_char (s : string) : string =
  String.sub s 0 (String.length s - 1)


let deriveGenerators c mind_name gen_name =
  match c with
  | CRef (r,_) ->

     let env = Global.env () in

     let glob_ref = Nametab.global r in
     let ind = Globnames.destIndRef glob_ref in
     let (mind, _) = ind in

     let mib = Environ.lookup_mind mind env in
     let oib = mib.mind_packets.(0) in

     let strippedPair = List.map strip_prod (Array.to_list oib.mind_nf_lc) in

     (* Create the new inductive entries *)
     let oie = { mind_entry_typename  = id_of_string mind_name ;
                 mind_entry_arity     = get_user_arity oib.mind_arity ;
                 mind_entry_template  = false; (* LEO: not sure about this *)
                 mind_entry_consnames = List.map (fun i -> id_of_string (strip_last_char (string_of_id i))) (Array.to_list oib.mind_consnames) ;
                 mind_entry_lc = List.map snd strippedPair ;
               } in
     let mie = { mind_entry_record = None ; (* LEO: not a record *)
                 mind_entry_finite = mib.mind_finite ;
                 mind_entry_params = [] ;
                 mind_entry_inds   = [oie] ;             (* TODO: This currently works for non mutually recursive! *)
                 mind_entry_polymorphic = mib.mind_polymorphic ;
                 mind_entry_universes = mib.mind_universes ;
                 mind_entry_private = mib.mind_private ;
               } in

     (* Declare the mutual inductive *)
     ignore (declare_mind mie);

(*
     (* Construct kernel term closure *)
     let env = Global.env () in
     let evd = Evd.empty in
     let mk_kernel c = interp_constr evd env c in

     (* Helpers for return/bind in the Gen monad *)
     let returnGen c =
       (* Not clear why this doesn't want a "QuickChick" qualifier... *)
       CApp (dummy_loc, (None, mk_ref "GenLow.returnGen"), [(c, None)]) in
     let mkEx p x pf =
       CApp (dummy_loc, (None, mk_ref "exist"), [(p, None); (x, None); (pf, None)]) in

     ()
 *)
(*
     (* Start creating the generator *)
     let const_body = mk_kernel (
       (* For the fixpoint "aux", structural recursion on "size" *)
       let aux  = fresh_name "aux" in
       let size = fresh_name "size" in
       let binderList = [LocalRawAssum ([(dummy_loc, Name size)], Default Explicit, mk_ref "nat")] in

       let base = returnGen (mkEx (mk_ref "goodFoo") (mk_ref "Foo1") (mk_ref "Good1")) in

       let fix_body =
         CCases (dummy_loc, Term.RegularStyle, None,
                 [(mk_c size, (None, None))],
                 [(dummy_loc, [dl [CPatCstr (dummy_loc, Ident (dl (id_of_string "O")), [])]], base);
                  (dummy_loc, [dl [CPatCstr (dummy_loc, Ident (dl (id_of_string "S")), [CPatAtom (dummy_loc, None)])]], base)]) in

       let fix_dcl = (dl aux, binderList, (None, CStructRec), fix_body, (dl None)) in

       G_constr.mk_fix (dummy_loc, true, dl aux, [fix_dcl])
     ) in

     (* Define the new constant *)
     ignore (
         declare_constant ~internal:KernelVerbose (id_of_string sg)
         (DefinitionEntry {
              const_entry_body = const_body;
              const_entry_secctx = None;
              const_entry_type = None;
              const_entry_opaque = false
            },
          Decl_kinds.IsDefinition Decl_kinds.Definition)
       )
 *)
  | _ -> msgerr (str "Not a valid identifier" ++ fnl ())

VERNAC COMMAND EXTEND DeriveGenerators
  | ["DeriveGenerators" constr(c) "as" string(s1) "and" string(s2)] -> [deriveGenerators c s1 s2]
END;;
 *)
