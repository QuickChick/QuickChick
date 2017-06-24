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
open SemLib
open Unify
open ArbitrarySizedST
open Feedback

type btyp = ((coq_expr -> coq_expr) * coq_expr)

type atyp = ((coq_expr -> coq_expr) * coq_expr)

let fail_exp (dt : coq_expr) : btyp =
  ( (* gen *)
    (fun s -> returnGen (gNone dt)),
    (* mon *)
    set_incl_refl
  )

let ret_exp (dt : coq_expr) (c : coq_expr) : btyp =
  ( (* gen *)
    (fun s -> returnGen (gSome dt c)),
    (* mon *)
    set_incl_refl
  )

let class_method : atyp =
  ( (* gen *)
    (fun s -> gInject "arbitrary"),
    (* mon *)
    set_incl_refl
  )

let class_methodST (n : int) (pred : coq_expr) : atyp =
  let gen =
    gApp ~explicit:true (gInject "arbitraryST")
      [ hole (* Implicit argument - type A *)
      ; pred
      ; hole (* Implicit instance *)]
  in
  ( (* gen *)
    (fun s -> gen),
    (* mon *)
    set_incl_refl
  )

let rec_method (generator_body : coq_expr)
      (hleq : var) (ih : var) (s2 : coq_expr)
      (n : int) (l : coq_expr list) : atyp =
  let gen_body (size : coq_expr) (args : coq_expr list) =
    gApp generator_body (size :: args)
  in
  let mon = gApp (gVar ih) ((s2 :: l) @ [gVar hleq]) in
  let proof = gApp (gVar ih) l in
  ( (* gen *)
    (fun s -> gen_body s l),
    (* mon *)
    mon
  )

let bind (opt : bool) (m : atyp) (x : string) (f : var -> btyp) : btyp =
  let (gen, mon) = m in
  let genf s x =
    let (gen, _) = f x in gen s
  in
  let monf x =
    let (_, mon) = f x in mon
  in
  ( (* gen *)
    (fun s -> (if opt then bindGenOpt else bindGen) (gen s) x (genf s)),
    (* mon *)
    (if opt then semBindOptSizeOpt_subset_compat else semBindSizeOpt_subset_compat)
      mon (gFun [x] (fun [x] -> monf x))
  )

let ret_mon (s : coq_expr) matcher1 matcher2 =
  set_incl
    (set_int (isSomeSet hole) (semGenSize matcher1 s))
    (set_int (isSomeSet hole) (semGenSize matcher2 s))

let eta g = gSnd (gPair (gInt 1, g))

let ret_type_dec 
      (v : var) (s : coq_expr)
      (left1 : coq_expr) (right1 : coq_expr)
      (left2 : coq_expr) (right2 : coq_expr) =
  ret_mon s
    (gMatch (gVar v)
          [ (injectCtr "left", ["eq"], fun _ -> left1)
          ; (injectCtr "right", ["neq"], fun _ -> right1) ])
    (gMatch (gVar v)
            [ (injectCtr "left", ["eq"], fun _ -> left2)
            ; (injectCtr "right", ["neq"], fun _ -> right2) ])

let check_expr (s : coq_expr) (s1 : coq_expr) (s2 : coq_expr)
      (n : int) (scrut : coq_expr) (left : btyp) (right : btyp) =
  let (lgen, lmon) = left in
  let (rgen, rmon) = right in
  ( (* gen *)
    (fun s ->
       gMatchReturn scrut
         "v" (* as clause *)
         (fun v -> hole)
         [ (injectCtr "left", ["eq" ] , fun _ -> lgen s)
         ; (injectCtr "right", ["neq"], fun _ -> rgen s)
         ]),
    (* mon *)
    gMatchReturn scrut
      "v" (* as clause *)
      (fun v -> ret_type_dec v s (lgen s1) (rgen s1) (lgen s2) (rgen s2))
      [ (injectCtr "left", ["eq"] , fun _ -> lmon)
      ; (injectCtr "right", ["neq"], fun _ -> rmon)
      ])


let match_inp (s : coq_expr) (s1 : coq_expr) (s2 : coq_expr)
      (inp : var) (pat : matcher_pat) (left : btyp) (right : btyp) =
  let (lgen, lmon) = left in
  let (rgen, rmon) = right in
  let proof_typ v =
    ret_mon s
      (construct_match (gVar v) ~catch_all:(Some (rgen s1)) [(pat, lgen s1)])
      (construct_match (gVar v) ~catch_all:(Some (rgen s2)) [(pat, lgen s2)])
  in
  ( (* gen *)
    (fun s ->
       construct_match_with_return
         (gVar inp) ~catch_all:(Some (rgen s)) "v" (fun v -> hole)
         [(pat, lgen s)]),
    (* mon *)
    construct_match_with_return
      (gVar inp) ~catch_all:(Some rmon) "v" proof_typ
      [(pat, lmon)]
  )

let stMaybe (opt : bool) (exp : atyp)
      (x : string) (checks : ((coq_expr -> coq_expr) * int) list) =
  let (gen, mon) = exp in
  let rec sumbools_to_bool x lst e fail =
    match lst with
    | [] -> e
    | (chk, _) :: lst' ->
      matchDec (chk (gVar x)) (fun heq -> fail) (fun hneq -> sumbools_to_bool x lst' e fail)
  in
  let bool_pred checks =
    gFun [x]
      (fun [x] -> sumbools_to_bool x checks gTrueb gFalseb)
  in
  ( (* gen *)
    (fun s ->
       gApp (gInject (if opt then "suchThatMaybeOpt" else "suchThatMaybe"))
         [ gen s (* Use the generator provided for base generator *)
         ; bool_pred checks
         ]),
    (* mon *)
    (if opt then suchThatMaybeOpt_subset_compat else suchThatMaybe_subset_compat)
      (bool_pred checks) mon
  )

let bigcupf s =
  gFun
    ["x"]
    (fun [x] -> set_int (isSomeSet hole) (semGenSize (gSnd (gVar x)) s))

let genSizedSTSMon_body
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

  let base_gens (input_names : var list) (rec_name : coq_expr) =
    base_gens (gInt 0) full_gtyp gen_ctr dep_type ctrs input_names n register_arbitrary rec_name
  in

  let ind_gens (input_names : var list) (size : coq_expr) (rec_name : coq_expr) =
    ind_gens size full_gtyp gen_ctr dep_type ctrs input_names n register_arbitrary rec_name
  in

  let aux_arb (rec_name : coq_expr) size vars =
    gMatch (gVar size)
      [ (injectCtr "O", [], fun _ ->
             uniform_backtracking (base_gens vars rec_name))
      ; (injectCtr "S", ["size'"], fun [size'] ->
            uniform_backtracking (ind_gens vars (gVar size') rec_name))
      ]
  in

  let generator_body : coq_expr =
    (* gInject "arb_aux" *)
    gRecFunInWithArgs
      ~assumType:(gen_type)
      "aux_arb" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs)
      (fun (rec_name, size::vars) -> aux_arb (gVar rec_name) size vars)
      (fun rec_name -> gVar rec_name)
  in

  let add_freq gens =
    List.map gPair (List.combine (List.map (fun _ -> gInt 1) gens) gens) in

  let handle_branch' s s1 s2 hleq ih (ins : var list) =
    handle_branch n dep_type ins
      (fail_exp full_gtyp) (ret_exp full_gtyp) class_method class_methodST
      (rec_method generator_body hleq ih s2) bind
      stMaybe (check_expr s s1 s2) (match_inp s s1 s2)
      gen_ctr (fun _ -> ())
  in

  let base_case s s2 hleq inputs =
    let (cases : coq_expr) =
      List.fold_right
        (fun (c : dep_ctr) (exp : coq_expr) ->
           (* let b = false in *)
           (* let p = hole in *)
           let ((_, p), b) =
             handle_branch' (gVar s) (gInt 0) (gVar s2) hleq (make_up_name ()) inputs c
           in
           if b then
             bigcup_cons_setI_subset_compat_backtrack p exp
           else
             bigcup_cons_setI_subset_pres_backtrack exp
        ) ctrs (bigcup_nil_setI hole hole hole)
    in
    subset_respects_set_eq
      (setI_set_eq_r (semBacktrackSize (gList (add_freq (base_gens inputs generator_body))) (gVar s)))
      (setI_set_eq_r (semBacktrackSize (gList (add_freq (ind_gens inputs (gVar s2) generator_body))) (gVar s)))
      (isSome_subset (setI_subset_compat set_incl_refl cases))
  in

  let ind_case s s1 s2 hleq ih (inputs : var list) =
    let cases =
      List.fold_right
        (fun (c : dep_ctr) (exp : coq_expr) ->
           let ((_, p), b) =
             handle_branch' (gVar s) (gVar s1) (gVar s2) hleq ih inputs c
           in
           bigcup_cons_setI_subset_compat_backtrack p exp
        ) ctrs (bigcup_nil_setI (bigcupf (gVar s)) hole hole)
    in
    subset_respects_set_eq
      (setI_set_eq_r (semBacktrackSize (gList (add_freq (ind_gens inputs (gVar s1) generator_body))) (gVar s)))
      (setI_set_eq_r (semBacktrackSize (gList (add_freq (ind_gens inputs (gVar s2) generator_body))) (gVar s)))
      (isSome_subset (setI_subset_compat set_incl_refl cases))
  in

  let input_vars = List.map fresh_name input_names in

  let ret_type inps s s1 s2 =
    gImpl (gLeq s1 s2)
      (set_incl
         (set_int (isSomeSet hole) (semGenSize (gApp generator_body (s1 :: inps)) s))
         (set_int (isSomeSet hole) (semGenSize (gApp generator_body (s2 :: inps)) s))
      )
  in

  let out_type s =
    gFun ["s1"]
      (fun [s1] ->
         gProdWithArgs ((gArg ~assumName:(gVar (fresh_name "s2")) ()) :: inputs)
           (fun (s2 :: inps) -> ret_type (List.map gVar inps) s (gVar s1) (gVar s2))
      )
  in

  let in_type s s1 =
    gFun ["s2"]
      (fun [s2] ->
         gProdWithArgs inputs
           (fun inps -> ret_type (List.map gVar inps) s s1 (gVar s2))
      )
  in


  let mon_proof =
    gFun ["s"; "s1"; "s2"]
      (fun [s; s1; s2] ->
         gApp
           (nat_ind (* outer induction *)
              (* return type *)
              (out_type (gVar s))
              (* base case -- inner induction *)
              (nat_ind
                 (* inner type *)
                 (in_type (gVar s) (gInt 0))
                 (* reflexivity *)
                 (gFunWithArgs inputs
                    (fun inps ->
                       gFun ["Hleq"]
                         (fun [hleq] -> set_incl_refl))
                 )
                 (gFun
                    ["s2"; "IHs2"]
                    (fun [s2; _] ->
                       gFunWithArgs inputs
                         (fun inps ->
                            gFun ["Hleq"]
                              (fun [hleq] ->
                                 base_case s s2 hleq inps)
                         ))
                 )
              )
              (* inductive case -- inner induction *)
              (gFun ["s1"; "IHs1"]
                 (fun [s1; ihs1] ->
                    nat_ind
                      (* inner type *)
                      (in_type (gVar s) (gSucc (gVar s1)))
                      (* contradiction *)
                      (gFunWithArgs inputs
                         (fun inps ->
                            gFun ["Hleq"]
                              (fun [hleq] -> false_ind hole (lt0_False (gVar hleq))))
                      )
                      (* inductive case *)
                      (gFun
                         ["s2"; "IHs2"]
                         (fun [s2; _] ->
                            gFunWithArgs inputs
                              (fun inps ->
                                 gFun ["Hleq"]
                                   (fun [hleq] ->
                                      ind_case s s1 s2 hleq ihs1 inps)))
                      )
                 )
              )
           )
           ((gVar s1) :: (gVar s2) :: (List.map gVar input_vars))
      )
  in

  msg_debug (str "size mon");
  debug_coq_expr mon_proof;

  gRecord [ ("sizeMonotonicOpt", mon_proof) ]
