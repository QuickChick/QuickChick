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
type btyp = (coq_expr * coq_expr * coq_expr * (coq_expr -> coq_expr))

type atyp = (coq_expr * coq_expr * coq_expr * coq_expr)

let fail_exp (dt : coq_expr) : btyp =
  (set_empty,
   returnGen (gApp ~explicit:true (gInject "None") [dt]),
   returnGenSizeMonotonic gNone,
   fun hcur -> false_ind hole (imset_set0_incl hole hole hcur))

let ret_exp (dt : coq_expr) (c : coq_expr) : btyp =
  (set_singleton c,
   returnGen (gApp ~explicit:true (gInject "Some") [dt; c]),
   returnGenSizeMonotonic (gSome c),
   fun hcur -> rewrite (imset_singl_incl hole hole hole hcur) (rewrite_set_r (semReturn hole) (gEqRefl hole)))

let class_method : atyp =
  let proof = gInject "arbitraryCorrect" in
  (set_full, gInject "arbitrary", hole, set_eq_set_incl_r proof)

let class_methodST (n : int) (pred : coq_expr) : atyp =
  let proof =
   gApp ~explicit:true (gInject "STComplete") [hole; pred; hole; hole]
  in
  let gen =
    gApp ~explicit:true (gInject "arbitraryST")
      [ hole (* Implicit argument - type A *)
      ; pred
      ; hole (* Implicit instance *)]
  in
  (pred, gen, hole, proof)

let rec_method (inputs : arg list) (setinst : coq_expr) (geninst : coq_expr) (moninst : coq_expr)
      (ih : var) (size : coq_expr) (n : int) (l : coq_expr list) : atyp =
  let iter_body args : coq_expr =
    appinst "DependentClasses.iter" setinst size args
  in
  let gen_body args : coq_expr =
    appinst "arbitrarySizeST" geninst size args
  in
  let gmon = gApp moninst (size :: l) in
  let proof = gApp (gVar ih) l in
  (iter_body l, gen_body l, gmon, proof)

let bind (opt : bool) (m : atyp) (x : string) (f : var -> btyp) : btyp =
  let (set, gen, mon, sub) = m in
  let setf x =
    let (set, _, _, _) = f x in set
  in
  let genf x =
    let (_, gen, _, _) = f x in gen
  in
  let monf x =
    let (_, _, mon, _) = f x in mon
  in
  let prf x =
    let (_, _, _, pr) = f x in pr
  in
  let hxc = "Hc_" ^ x in
  let hx = "H_" ^ x in
  let hcur' = "Hl_" ^ x in
  (set_bigcup x set setf,
   (if opt then bindGenOpt else bindGen) gen x genf,
   (if opt then bindOptMonotonic else bindMonotonic) mon x monf,
   let bind = if opt then semBindOptSizeMonotonic else semBindSizeMonotonic in
   (fun hcur ->
      gMatch (imset_bigcup_incl_l hole hole hole hole hcur)
        [(injectCtr "ex_intro", [x; hx],
          fun [xw; hcx] ->
            gMatch (gVar hcx)
              [(injectCtr "conj", [hx; hcur'],
                fun [hx; hcur] ->
                  bind
                    hole mon hole (gFun [x] (fun [x] -> monf x)) sub
                    hole (gExIntro_impl (gVar xw) (gConjIntro (gVar hx) (prf xw (gVar hcur))))
               )])]))

let ret (x : var) matcher1 matcher2 =
  gImpl
    (gApp
       (imset (gInject "Some") matcher1)
       [gVar x])
    (gApp
      (semGen matcher2)
      [gVar x])

let ret_type_dec (x : var) (s : var) (left1 : coq_expr) (right1 : coq_expr)
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
  let (lset, lgen, lmon, lproof) = left in
  let (rset, rgen, rmon, rproof) = right in
  let namecur = Printf.sprintf "Hc%d" n in
  (gMatchReturn scrut
     "v" (* as clause *)
     (fun v -> hole)
     [ (injectCtr "left", ["eq" ] , fun _ -> lset)
     ; (injectCtr "right", ["neq"], fun _ -> rset) 
     ],
   gMatchReturn scrut
     "v" (* as clause *)
     (fun v -> ret_type v ret_type_dec)
     [ (injectCtr "left", ["eq" ] , fun _ -> lgen)
     ; (injectCtr "right", ["neq"], fun _ -> rgen) 
     ],
   gMatchReturn scrut
     "v" (* as clause *)
     (fun v -> ret_type_mon v)
     [ (injectCtr "left", ["eq" ] , fun _ -> lmon)
     ; (injectCtr "right", ["neq"], fun _ -> rmon) 
     ],
   fun hcur ->
     gApp
       (gMatchReturn scrut
          "v" (* as clause *)
          (fun v -> ret_type_dec x v lset rset lgen rgen)
          [ (injectCtr "left", ["eq"] ,
             fun _ -> gFun [namecur] (fun [hcur] -> lproof (gVar hcur)))
          ; (injectCtr "right", ["neq"],
             fun _ -> gFun [namecur] (fun [hcur] -> rproof (gVar hcur)))
          ]) [hcur]
  )


let match_inp (x : var) (inp : var) (pat : matcher_pat) (left : btyp) (right : btyp) =
  let (lset, lgen, lmon, lproof) = left in
  let (rset, rgen, rmon, rproof) = right in
  let mon_typ v =
    ret_mon (construct_match (gVar v) ~catch_all:(Some hole) [(pat, hole)])
  in
  let proof_typ v =
    ret x
      (construct_match (gVar v) ~catch_all:(Some rset) [(pat, lset)])
      (construct_match (gVar v) ~catch_all:(Some rgen) [(pat, lgen)])
  in
  (construct_match_with_return
     (gVar inp) ~catch_all:(Some rset) "v" (fun v -> hole)
     [(pat, lset)],
   construct_match_with_return
     (gVar inp) ~catch_all:(Some rgen) "v" (fun v -> hole)
     [(pat, lgen)],
   construct_match_with_return
     (gVar inp) ~catch_all:(Some rmon) "v" mon_typ
     [(pat, lmon)],
   fun hcur ->
     gApp
       (construct_match_with_return
          (gVar inp) ~catch_all:(Some (gFun ["hc"] (fun [hcur] -> rproof (gVar hcur)))) "v" proof_typ
          [(pat, gFun ["hc"] (fun [hcur] -> lproof (gVar hcur)))])
       [hcur]
  )

(* XXX probably does not work *)
let stMaybe (y : var) (opt : bool) (exp : atyp)
      (x : string) (checks : ((coq_expr -> coq_expr) * int) list) =
  let (set, gen, mon, proof) = exp in
  let rec sumbools_to_bool x lst e fail =
    match lst with
    | [] -> e
    | (chk, _) :: lst' ->
      matchDec (chk (gVar x)) (fun heq -> fail) (fun hneq -> sumbools_to_bool x lst' e fail)
  in
  let bool_pred =
    gFun [x]
      (fun [x] -> sumbools_to_bool x checks gTrueb gFalseb)
  in
  let hxs = "H_" ^ x in
  let ret_type_dec_prop (s : var) (left1 : coq_expr) (right1 : coq_expr)
    (left2 : coq_expr) (right2 : coq_expr)=
    ret y
      (gMatch (gVar s)
         [ (injectCtr "left", ["eq"], fun _ -> left1)
         ; (injectCtr "right", ["neq"], fun _ -> right1) ])
      (gMatch (gVar s)
         [ (injectCtr "left", ["eq"], fun _ -> left2)
         ; (injectCtr "right", ["neq"], fun _ -> right2) ])
  in
  let rec sumbools_to_bool_proof (x : var) hx lst : coq_expr =
    match lst with
    | [] -> gApp proof [gVar x; gVar hx]
    | (chk, n) :: lst' ->
      let set = sumbools_to_bool x lst' (gApp set [gVar x]) gFalse in
      gApp
        (gMatchReturn (chk (gVar x))
           "v" (* as clause *)
           (fun v -> ret_type_dec_prop v set_empty set hole hole)
           [ (injectCtr "left", ["heq"],
              fun [heq] -> gFun [hxs] (fun [hx] -> false_ind hole (gVar hx)))
           ; (injectCtr "right", ["hneq"],
              fun [hneq] -> gFun [hxs] (fun [hx] -> sumbools_to_bool_proof x hx lst'))
           ])
        [gVar hx]
  in
  (gFun [x] (fun [x] -> sumbools_to_bool x checks (gApp set [gVar x]) gFalse),
   gApp (gInject (if opt then "suchThatMaybeOpt" else "suchThatMaybe"))
     [ gen (* Use the generator provided for base generator *)
     ; bool_pred ],
   (if opt then suchThatMaybeMonotonic else suchThatMaybeOptMonotonic) mon bool_pred,
   gFun [x; hxs] (fun [x; hx] -> sumbools_to_bool_proof x hx checks) 
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

  let aux_arb (input_names : var list) (rec_name : coq_expr) size vars =
    gMatch (gVar size)
      [ (injectCtr "O", [], fun _ ->
             uniform_backtracking (base_gens input_names rec_name))
      ; (injectCtr "S", ["size'"], fun [size'] ->
            uniform_backtracking (ind_gens input_names size' rec_name))
      ]
  in

  let generator_body (input_names : var list) : coq_expr =
    gRecFunInWithArgs
      ~assumType:(gen_type)
      "aux_arb" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
      (fun (rec_name, size::vars) -> aux_arb input_names (gVar rec_name) size vars)
      (fun x -> gVar x)
  in

  let add_freq gens =
    List.map gPair (List.combine (List.map (fun _ -> gInt 1) gens) gens) in

  let handle_branch' (y : var) (ih : var) (size : coq_expr) (ins : var list) =
    handle_branch n dep_type ins
      (fail_exp full_gtyp) (ret_exp full_gtyp) class_method class_methodST
      (rec_method inputs setinst geninst moninst ih size) bind (stMaybe y) (check_expr y) (match_inp y)
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
              rewrite_set_r (semBacktrack (gList (add_freq (base_gens inputs (generator_body inputs)))))
                (List.fold_right
                   (fun (c : dep_ctr) (exp : coq_expr -> coq_expr -> coq_expr) ->
                      fun hin hg ->
                        let ((_, _, _, p), b) =
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
                   rewrite_set_r (semBacktrack (gList (add_freq (ind_gens inputs s (generator_body inputs)))))
                     (List.fold_right
                        (fun (c : dep_ctr) (exp : coq_expr -> coq_expr -> coq_expr) ->
                           fun hin hg ->
                             let ((_, _, _, p), b) =
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
                (semGen (appinst "arbitrarySizeST" geninst (gVar s) inps)))
      )
  in

  let input_vars = List.map fresh_name input_names in

  let com_proof =
    gFun ["size"]
      (fun [s] ->
         gApp (gInject "nat_ind")
           ([ret_type; base_case; ind_case; gVar s] @ (List.map gVar input_vars)))
  in

  msg_debug (str "compl");
  debug_coq_expr com_proof;
  gRecord [("sizedSTComplete", com_proof)]
