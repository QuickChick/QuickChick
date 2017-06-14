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

let appinst meth inst s inps =
  gApp ~explicit:true (gInject meth) [hole; hole; gApp inst inps; s]

(* arguments for completeness *)
type btyp = (coq_expr * coq_expr * coq_expr * (coq_expr -> coq_expr) * coq_expr)

type atyp = (coq_expr * coq_expr * coq_expr * coq_expr * coq_expr)

let fail_exp (dt : coq_expr) : btyp =
  ( (* set *)
    set_empty,
    (* gen *)
    returnGen (gNone dt),
    (* mon *)
    returnGenSizeMonotonic (gNone dt),
    (* comp *)
    (fun hcur -> false_ind hole (imset_set0_incl hole hole hcur)),
    (* sound *)
    gFun ["x"; "Hx"] (fun [x; hx] -> gOrIntroR (rewrite_set_l (semReturn hole) (gVar hx)))
  )

let ret_exp (dt : coq_expr) (c : coq_expr) : btyp =
  ( (* set *)
    set_singleton c,
    (* gen *)
    returnGen (gSome dt c),
    (* mon *)
    returnGenSizeMonotonic (gSome dt c),
    (* comp *)
    (fun hcur -> rewrite (imset_singl_incl hole hole hole hcur) (rewrite_set_r (semReturn hole) (gEqRefl hole))),
    (* sound *)
    gFun ["x"; "Hx"]
      (fun [x; hx] -> gOrIntroL (gExIntro_impl hole (gConjIntro (gEqRefl hole) (rewrite_set_l (semReturn hole) (gVar hx)))))
  )

let class_method : atyp =
  let proof = gInject "arbitraryCorrect" in
  ( (* set *)
    set_full,
    (* gen *)
    gInject "arbitrary",
    (* mon *)
    hole,
    (* comp *)
    set_eq_set_incl_r proof,
    (* soundness *)
    set_eq_set_incl_l proof
  )


let class_methodST (n : int) (pred : coq_expr) : atyp =
  let comp =
    gApp ~explicit:true (gInject "STComplete") [hole; pred; hole; hole]
  in
  let sound =
    gApp ~explicit:true (gInject "STSound") [hole; pred; hole; hole]
  in
  let gen =
    gApp ~explicit:true (gInject "arbitraryST")
      [ hole (* Implicit argument - type A *)
      ; pred
      ; hole (* Implicit instance *)]
  in
  (pred, gen, hole, comp, sound)

let rec_method (inputs : arg list) (setinst : coq_expr) (generator_body : coq_expr) (moninst : coq_expr)
      (ih : var) (size : coq_expr) (n : int) (l : coq_expr list) : atyp =
  let iter_body args : coq_expr =
    appinst "DependentClasses.iter" setinst size args
  in
  let gen_body args : coq_expr =
    gApp generator_body (size :: args)
  in
  let gmon = gApp moninst (size :: l) in
  let proof = gApp (gVar ih) l in
  (iter_body l, gen_body l, gmon, proof, proof)

let bind (opt : bool) (m : atyp) (x : string) (f : var -> btyp) : btyp =
  let (set, gen, mon, comp, sound) = m in
  let setf x =
    let (set, _, _, _, _) = f x in set
  in
  let genf x =
    let (_, gen, _, _, _) = f x in gen
  in
  let monf x =
    let (_, _, mon, _, _) = f x in mon
  in
  let compf x =
    let (_, _, _, pr, _) = f x in pr
  in
  let soundf x =
    let (_, _, _, _, pr) = f x in pr
  in
  let hxc = "Hc_" ^ x in
  let hx = "H_" ^ x in
  let hcur' = "Hl_" ^ x in
  ( (* set *)
    set_bigcup x set setf,
    (* gen *)
    (if opt then bindGenOpt else bindGen) gen x genf,
    (* mon *)
    (if opt then bindOptMonotonic else bindMonotonic) mon x monf,
    (* comp *)
    (let bind =
       (if opt then semBindOptSizeMonotonicIncl_l else semBindSizeMonotonicIncl_l)
         hole mon hole (gFun [x] (fun [x] -> monf x)) comp hole
     in
     (fun hcur ->
        gMatch (imset_bigcup_incl_l hole hole hole hole hcur)
          [(injectCtr "ex_intro", [x; hx],
            fun [w; hcx] ->
              gMatch (gVar hcx)
                [(injectCtr "conj", [hx; hcur'],
                  fun [hx; hcur] ->
                    bind (gExIntro_impl (gVar w) (gConjIntro (gVar hx) (compf w (gVar hcur))))
                 )])])),
    (* sound *)
    (let bind =
       (if opt then semBindOptSizeMonotonicIncl_r else semBindSizeMonotonicIncl_r)
         gen (gFun [x] (fun [x] -> genf x))
         set (gFun [x] (fun [x] -> setf x))
         mon (gFun [x] (fun [x] -> monf x))
     in
     bind sound (gFun [x] (fun [x] -> soundf x)))
  )

let ret_comp (x : var) matcher1 matcher2 =
  gImpl
    (gApp
       (imset (gInject "Some") matcher1)
       [gVar x])
    (gApp
      (semGen matcher2)
      [gVar x])

let ret_sound (x : var) matcher1 matcher2 =
  set_incl
    (semGen matcher2)
    (set_union (imset (gInject "Some") matcher1) (set_singleton (gNone hole)))

let ret_type_dec (ret : var -> coq_expr -> coq_expr -> coq_expr)
      (x : var) (s : var)
      (left1 : coq_expr) (right1 : coq_expr)
      (left2 : coq_expr) (right2 : coq_expr) =
  ret x
    (gMatch (gVar s)
       [ (injectCtr "left", ["eq"], fun _ -> left1)
       ; (injectCtr "right", ["neq"], fun _ -> right1) ])

    (gMatch (gVar s)
       [ (injectCtr "left", ["eq"], fun _ -> left2)
       ; (injectCtr "right", ["neq"], fun _ -> right2) ])

let ret_mon matcher =
  gApp (gInject "SizeMonotonic") [matcher]


let ret_type_mon (s : var)  =
  let matcher =
    gMatch (gVar s)
      [ (injectCtr "left", ["eq"], fun _ -> hole)
      ; (injectCtr "right", ["neq"], fun _ -> hole) ]
  in
  ret_mon matcher

let check_expr (x : var) (n : int) (scrut : coq_expr) (left : btyp) (right : btyp) =
  let (lset, lgen, lmon, lcomp, lsound) = left in
  let (rset, rgen, rmon, rcomp, rsound) = right in
  let namecur = Printf.sprintf "Hc%d" n in
  ( (* set *)
    gMatchReturn scrut
      "v" (* as clause *)
      (fun v -> hole)
      [ (injectCtr "left", ["eq" ] , fun _ -> lset)
      ; (injectCtr "right", ["neq"], fun _ -> rset) 
      ],
    (* gen *)
    gMatchReturn scrut
      "v" (* as clause *)
      (fun v -> ret_type v ret_type_dec)
      [ (injectCtr "left", ["eq" ] , fun _ -> lgen)
      ; (injectCtr "right", ["neq"], fun _ -> rgen) 
      ],
    (* mon *)
    gMatchReturn scrut
      "v" (* as clause *)
      (fun v -> ret_type_mon v)
      [ (injectCtr "left", ["eq" ] , fun _ -> lmon)
      ; (injectCtr "right", ["neq"], fun _ -> rmon) 
      ],
    (* compl *)
    (fun hcur ->
       gApp
         (gMatchReturn scrut
            "v" (* as clause *)
            (fun v -> ret_type_dec ret_comp x v lset rset lgen rgen)
            [ (injectCtr "left", ["eq"] ,
               fun _ -> gFun [namecur] (fun [hcur] -> lcomp (gVar hcur)))
            ; (injectCtr "right", ["neq"],
               fun _ -> gFun [namecur] (fun [hcur] -> rcomp (gVar hcur)))
            ]) [hcur]),
    (* sound *)
    gMatchReturn scrut
      "v" (* as clause *)
      (fun v -> ret_type_dec ret_sound x v lset rset lgen rgen)
      [ (injectCtr "left", ["eq"], fun _ -> lsound)
      ; (injectCtr "right", ["neq"], fun _ -> rsound)
      ])


let match_inp (x : var) (inp : var) (pat : matcher_pat) (left : btyp) (right : btyp) =
  let (lset, lgen, lmon, lcomp, lsound) = left in
  let (rset, rgen, rmon, rcomp, rsound) = right in
  let mon_typ v =
    ret_mon (construct_match (gVar v) ~catch_all:(Some hole) [(pat, hole)])
  in
  let proof_typ ret v =
    ret x
      (construct_match (gVar v) ~catch_all:(Some rset) [(pat, lset)])
      (construct_match (gVar v) ~catch_all:(Some rgen) [(pat, lgen)])
  in
  ( (* set *)
    construct_match_with_return
      (gVar inp) ~catch_all:(Some rset) "v" (fun v -> hole)
      [(pat, lset)],
    (* gen *)
    construct_match_with_return
      (gVar inp) ~catch_all:(Some rgen) "v" (fun v -> hole)
      [(pat, lgen)],
    (* mon *)
    construct_match_with_return
      (gVar inp) ~catch_all:(Some rmon) "v" mon_typ
      [(pat, lmon)],
    (* comp *)
    (fun hcur ->
       gApp
         (construct_match_with_return
            (gVar inp) ~catch_all:(Some (gFun ["hc"] (fun [hcur] -> rcomp (gVar hcur)))) "v" (proof_typ ret_comp)
            [(pat, gFun ["hc"] (fun [hcur] -> lcomp (gVar hcur)))])
         [hcur]),
    (* sound *)
    construct_match_with_return
      (gVar inp) ~catch_all:(Some rsound) "v" (proof_typ ret_sound)
      [(pat, lsound)]
  )

let stMaybe (y : var) (opt : bool) (exp : atyp)
      (x : string) (checks : ((coq_expr -> coq_expr) * int) list) =
  let (set, gen, mon, comp, sound) = exp in
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
  let hxs = "H_" ^ x in
  let ret_comp matcher1 matcher2 =
    gImpl matcher1 (gConj hole matcher2)
  in
  let ret_sound matcher1 matcher2 =
    gImpl (gConj hole matcher2) matcher1
  in
  let rec sumbools_to_bool_comp (x : var) hx lst : coq_expr =
    match lst with
    | [] -> gConjIntro (gVar hx) hole
    | (chk, n) :: lst' ->
      let set d =
        gMatchReturn (gVar d)
          "s"
          (fun v -> gProp)
          [ (injectCtr "left" , ["eq" ], fun _ -> gFalse)
          ; (injectCtr "right", ["neq"], fun _ -> sumbools_to_bool x lst' (gApp set [gVar x]) gFalse)
          ]
      in
      let pred d =
        gIsTrue
          (matchDec (gVar d) (fun heq -> gFalseb)
             (fun hneq -> sumbools_to_bool x lst' gTrueb gFalseb))
      in
      gApp
        (gMatchReturn (chk (gVar x))
           "v" (* as clause *)
           (fun v -> ret_comp (set v) (pred v))
           [ (injectCtr "left", ["heq"],
              fun [heq] -> gFun [hxs] (fun [hx] -> false_ind hole (gVar hx)))
           ; (injectCtr "right", ["hneq"],
              fun [hneq] -> gFun [hxs] (fun [hx] -> sumbools_to_bool_comp x hx lst'))
           ])
        [gVar hx]
  in
  let rec sumbools_to_bool_sound (x : var) hx lst : coq_expr =
    match lst with
    | [] ->
      gMatch (gVar hx)
        [(injectCtr "conj", ["hl"; "hr"], (fun [hl; hr] -> (gVar hl)))]
    | (chk, n) :: lst' ->
      let set d =
        gMatchReturn (gVar d)
          "s"
          (fun v -> gProp)
          [ (injectCtr "left" , ["eq" ], fun _ -> gFalse)
          ; (injectCtr "right", ["neq"], fun _ -> sumbools_to_bool x lst' (gApp set [gVar x]) gFalse)
          ]
      in
      let pred d =
        gIsTrue
          (matchDec (gVar d) (fun heq -> gFalseb)
             (fun hneq -> sumbools_to_bool x lst' gTrueb gFalseb))
      in
      gApp
        (gMatchReturn (chk (gVar x))
           "v" (* as clause *)
           (fun v -> ret_sound (set v) (pred v))
           [ (injectCtr "left", ["heq"],
              fun [heq] ->
                gFun [hxs] (fun [hx] ->
                             gMatch (gVar hx)
                               [(injectCtr "conj", ["hl"; "hr"], (fun [hl; hr] -> false_ind hole (diff_false_true (gVar hr))))]
                           ))
           ; (injectCtr "right", ["hneq"],
              fun [hneq] -> gFun [hxs] (fun [hx] -> sumbools_to_bool_sound x hx lst'))
           ])
        [gVar hx]
  in
  ( (* set *)
    gFun [x] (fun [x] -> sumbools_to_bool x checks (gApp set [gVar x]) gFalse),
    (* gen *)
    gApp (gInject (if opt then "suchThatMaybeOpt" else "suchTha tMaybe"))
     [ gen (* Use the generator provided for base generator *)
     ; bool_pred checks ],
    (* mon *)
    (if opt then suchThatMaybeOptMonotonic else suchThatMaybeMonotonic) mon (bool_pred checks),
    (* comp *)
    set_incl_trans
      (imset_incl (gFun [x; hxs] (fun [x; hx] -> sumbools_to_bool_comp x hx checks)))
      ((if opt then semSuchThatMaybeOpt_complete else semSuchThatMaybe_complete)
         gen (bool_pred checks) hole comp),
    (* sound *)
    set_incl_trans
      ((if opt then semSuchThatMaybeOpt_sound else semSuchThatMaybe_sound)
         gen (bool_pred checks) hole sound)
      (setU_set_subset_compat
         (imset_incl (gFun [x; hxs] (fun [x; hx] -> sumbools_to_bool_sound x hx checks)))
         set_incl_refl)
  )


let genSizedSTCorr_body
      (class_name : string)
      (gen_ctr : ty_ctr)
      (ty_params : ty_param list)
      (ctrs : dep_ctr list)
      (dep_type : dep_type)
      (input_names : string list)
      (inputs : arg list)
      (n : int)
      (register_arbitrary : dep_type -> unit)
      (moninst : coq_expr)
      (geninst : coq_expr)
      (setinst : coq_expr) =

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

  let ind_gens (input_names : var list) (size : var) (rec_name : coq_expr) =
    ind_gens (gVar size) full_gtyp gen_ctr dep_type ctrs input_names n register_arbitrary rec_name
  in

  let aux_arb (rec_name : coq_expr) size vars =
    gMatch (gVar size)
      [ (injectCtr "O", [], fun _ ->
             uniform_backtracking (base_gens vars rec_name))
      ; (injectCtr "S", ["size'"], fun [size'] ->
            uniform_backtracking (ind_gens vars size' rec_name))
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

  let handle_branch' (y : var) (ih : var) (size : coq_expr) (ins : var list) =
    handle_branch n dep_type ins
      (fail_exp full_gtyp) (ret_exp full_gtyp) class_method class_methodST
      (rec_method inputs setinst generator_body moninst ih size) bind (stMaybe y) (check_expr y) (match_inp y)
      gen_ctr (fun _ -> ())
  in

  let some_proof hc =
    gMatch (in_imset hole hole hole hc)
      [(injectCtr "ex_intro", ["z"; "Heqz"],
        fun [z; heq] ->
          rewrite_sym (gFun ["x"] (fun [x] -> isSome (gVar x)))
            (gVar heq) (isSomeSome hole))]
  in

  let base_case =
    gFunWithArgs
      inputs
      (fun inputs ->
         gFun ["x"; "Hin"]
           (fun [x; hin] ->
              rewrite_set_r (semBacktrack (gList (add_freq (base_gens inputs generator_body))))
                (List.fold_right
                   (fun (c : dep_ctr) (exp : coq_expr -> coq_expr -> coq_expr) ->
                      fun hin hg ->
                        let ((_, _, _, p, _), b) =
                          handle_branch' x (make_up_name ()) (gInt 0) inputs c in
                        if b then
                          gMatch (imset_union_incl hole hole hole hole hin)
                            [ (injectCtr "or_introl", ["hin"],
                               fun [hin] ->
                                 gOrIntroL
                                   (gExIntro_impl
                                     hole
                                     (gConjIntro
                                        (gConjIntro hg (succ_neq_zero hole))
                                        (gConjIntro (some_proof (gVar hin)) (p (gVar hin))))))
                             ; (injectCtr "or_intror", ["hin"],
                                fun [hin] -> exp (gVar hin) (gOrIntroR hg))]
                        else exp hin hg)
                   ctrs (fun hin hgen -> false_ind hole (imset_set0_incl hole hole hin))
                   (gVar hin) (gOrIntroL (gEqRefl hole)))))
  in

  let ind_case =
    gFun ["size"; "IHs"]
      (fun [s; ih] ->
         gFunWithArgs
           inputs
           (fun inputs ->
              gFun ["x"; "Hin"]
                (fun [x; hin] ->
                   rewrite_set_r (semBacktrack (gList (add_freq (ind_gens inputs s generator_body))))
                     (List.fold_right
                        (fun (c : dep_ctr) (exp : coq_expr -> coq_expr -> coq_expr) ->
                           fun hin hg ->
                             let ((_, _, _, p, _), b) =
                               handle_branch' x ih (gVar s) inputs c in
                             gMatch (imset_union_incl hole hole hole hole hin)
                               [ (injectCtr "or_introl", ["hin"],
                                  fun [hin] ->
                                    gOrIntroL
                                      (gExIntro_impl
                                         hole
                                         (gConjIntro
                                            (gConjIntro hg (succ_neq_zero hole))
                                            (gConjIntro (some_proof (gVar hin)) (p (gVar hin))))))
                               ; (injectCtr "or_intror", ["hin"],
                                  fun [hin] -> exp (gVar hin) (gOrIntroR hg))])
                        ctrs (fun hin hgen -> false_ind hole (imset_set0_incl hole hole hin))
                        (gVar hin) (gOrIntroL (gEqRefl hole))))))
  in

  let ret_type =
    gFun ["size"]
      (fun [s] ->
         gProdWithArgs
           inputs
           (fun inputs ->
              let inps = List.map gVar inputs in
              set_incl
                (imset (gInject "Some") (appinst "DependentClasses.iter" setinst (gVar s) inps))
                (* (semGen (appinst "arbitrarySizeST" geninst (gVar s) inps)) *)
                (semGen (gApp generator_body ((gVar s) :: inps)))
           ))
  in

  let input_vars = List.map fresh_name input_names in

  let com_proof =
    gFun ["size"]
      (fun [s] ->
         gApp (gInject "nat_ind")
           ([ret_type; base_case; ind_case; gVar s] @ (List.map gVar input_vars)))
  in


  let base_case_sound =
    gFunWithArgs
      inputs
      (fun inputs ->
         let cases =
           List.fold_right
             (fun (c : dep_ctr) (exp :  (coq_expr  -> coq_expr) -> coq_expr) ->
                fun proof ->
                  let ((_, _, _, _, p), b) =
                    handle_branch' (make_up_name ()) (make_up_name ()) (gInt 0) inputs c
                  in
                  if b then
                    bigcup_cons_subset
                    (gProd hole hole) hole
                    (set_incl_setI_r (proof p))
                    (exp (fun e -> lift_subset_pres_r (proof e)))
                else
                  exp proof)
             ctrs (fun e -> bigcup_nil_subset) lift_subset_pres_l
         in
         subset_respects_set_eq_l
           (semBacktrack (gList (add_freq (base_gens inputs generator_body))))
           (set_incl_setU_l
              (bigcup_set_I_l cases)
              (set_incl_setI_l (setU_subset_r hole set_incl_refl))
             ))
  in

  let ind_case_sound =
    gFun ["size"; "IHs"]
      (fun [s; ih] ->
         gFunWithArgs
           inputs
           (fun inputs ->
            let cases =
              List.fold_right
                (fun (c : dep_ctr) (exp : (coq_expr  -> coq_expr) -> coq_expr) ->
                   fun proof ->
                     let ((_, _, _, _, p), b) =
                       handle_branch' (make_up_name ()) ih (gVar s) inputs c
                     in
                     bigcup_cons_subset
                       (gProd hole hole) hole
                       (set_incl_setI_r (proof p))
                       (exp (fun e -> lift_subset_pres_r (proof e))))
                ctrs (fun e -> bigcup_nil_subset) lift_subset_pres_l
            in
            subset_respects_set_eq_l
              (semBacktrack (gList (add_freq (ind_gens inputs s generator_body))))
              (set_incl_setU_l
                 (bigcup_set_I_l cases)
                 (set_incl_setI_l (setU_subset_r hole set_incl_refl))
              )))
  in

  let ret_type_sound =
    gFun ["size"]
      (fun [s] ->
         gProdWithArgs
           inputs
           (fun inputs ->
              let inps = List.map gVar inputs in
              set_incl
                (semGen (gApp generator_body ((gVar s) :: inps)))
                (* (set_union (imset (gInject "Some") (gApp (gInject "aux_iter") ((gVar s) :: inps))) ((set_singleton (gNone hole)))) *)
                (set_union (imset (gInject "Some") (appinst "DependentClasses.iter" setinst (gVar s) inps)) ((set_singleton (gNone hole))))
           ))
  in

  let sound_proof =
    gFun ["size"]
      (fun [s] ->
         gApp (gInject "nat_ind")
           ([ret_type_sound; base_case_sound; ind_case_sound; gVar s] @ (List.map gVar input_vars)))
  in



  (* msg_debug (str "compl"); *)
  (* debug_coq_expr com_proof; *)
  msg_debug (str "sound");
  debug_coq_expr sound_proof;

  gRecord [ ("sizedSTComplete", com_proof)
          ; ("sizedSTSound", sound_proof)
          ]
