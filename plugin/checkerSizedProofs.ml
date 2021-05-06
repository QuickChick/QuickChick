open Pp
open Util
open GenericLib
open CoqLib
open GenLib
open SemLib
open Error
open UnifyQC
open ArbitrarySizedST

type btyp = ((coq_expr -> coq_expr) * (* fun size => checker *)
             (coq_expr -> coq_expr)   (* mon true proof. fun Hin' => proof*) 
            )
type atyp = coq_expr -> coq_expr

let fail_exp (dt : coq_expr) : btyp =
  ( (* checker *)
    (fun s -> gSome dt g_false),
    (* mon true *)
    (fun hin -> discriminate hin))

let ret_exp (dt : coq_expr) (c : coq_expr) : btyp =
  ( (* checker *)
    (fun s -> gSome dt g_false),
    (* mon true *)
    (fun hin' -> gEqRefl hole))

let not_enough_fuel_exp (dt : coq_expr) : btyp =
  ( (* checker *)
    (fun s -> gNone dt),
    (* mon true *)
    (fun hin' -> gEqRefl hole))

let instantiate_existential_method = (fun _ -> hole)

let instantiate_existential_methodST (n : int) (pred : coq_expr) =
  failwith "Implement existentials in checkers"

let exist_bind (opt : bool) (m : atyp) (x : string) (f : var -> btyp) : btyp =
  failwith "Implement existentials in checkers"

let stMaybe (opt : bool) (g : atyp) (x : string) (checks : ((coq_expr -> coq_expr) * int) list) =
  failwith "StMaybe unimplemented"

let ret_type_dec (s : var) (left : coq_expr) (right : coq_expr) =
  gMatch (gVar s)
         [ (injectCtr "left", ["eq"], fun _ -> left)
         ; (injectCtr "right", ["neq"], fun _ -> right) ]

let check_expr (n : int) (scrut : coq_expr) (left : btyp) (right : btyp) (out_of_fuel : btyp) =
  let (gl, pmonl) = left in
  let (gr, pmonr) = right in
  let (gf, pmonf) = out_of_fuel in  
  let gen =
    fun s -> gMatchReturn scrut
                          "s" (* as clause *)
                          (fun v -> ret_type v ret_type_dec)
                          [ (injectCtr "Some", ["res_b" ] , fun [b] ->
                                                            (* Why as clauses/returns? *)       
                                                            gMatch (gVar b) 
                                                                   [ (injectCtr "true", [], fun _ -> gl s)
                                                                   ; (injectCtr "false", [], fun _ -> gr s)
                            ])
                          ; (injectCtr "None", [], fun _ -> gf s) 
                          ]
  in
  let mont =
    fun hin ->
    gMatch (destruct_match_true_l hin)
           [ (injectCtr "cinj", ["Heq"; "Hin"], fun [heq; hin'] -> destruct_match_true_r (gVar heq) (pmonl (gVar hin'))) ]
  in
  (gen, mont)

let rec_method
      (rec_name : coq_expr)
      (n : int) (letbinds : unknown list option) (l : coq_expr list) =
  fun size -> gApp rec_name (size :: l)

let rec_bind
      (ih : coq_expr) (hleq : coq_expr)
      (opt : bool) (m : atyp) (x : string) (f : var -> btyp) : btyp =
  let gen =
    fun s -> gMatch (m s)
                    [ (injectCtr "Some", ["res_b" ] , fun [b] ->
                                                      (* Why as clauses/returns? *)       
                                                      gMatch (gVar b) 
                                                             [ (injectCtr "true", [], fun _ -> fst (f b) s)
                                                             ; (injectCtr "false", [], fun _ -> fst (fail_exp hole) s)
                      ])
                    ; (injectCtr "None", [], fun _ -> gNone hole ) 
                    ]
  in
  let mont =
    let ihapp heq = gApp ih [hole; hole; hole; hole; le_S_n hleq; heq] in
    let pmon = snd (f (make_up_name ())) in (* Zoe : Var shound't matter for gens *)
    fun hin ->
    gMatch (destruct_match_true_l hin)
           [ (injectCtr "cinj", ["Heq"; "Hin"], fun [heq; hin'] -> destruct_match_true_r (ihapp (gVar heq)) (pmon (gVar hin'))) ]
  in
  (gen, mont)

let ret_type (s : var) f = hole

let match_inp (inp : var) (pat : matcher_pat) (left : btyp) (right  : btyp) =
  let (gl, pmonl) = left in
  let (gr, pmonr) = right in
  let ret v left right =
    construct_match (gVar v) ~catch_all:(Some right) [(pat, left)]
  in
  let catch_case right = 
    match pat with 
    | MatchCtr (c, ls) -> 
       (* Leo: This is a hack totality check for unary matches *)
       if num_of_ctrs c = 1 && List.for_all (fun x -> match x with MatchU _ -> true | MatchCtr _ -> false) ls 
       then None
       else Some right
    | _ -> failwith "Toplevel match not a constructor?"
  in 
  let gen = fun s -> construct_match_with_return
                       (gVar inp) ~catch_all:(catch_case (gr s)) "s" (fun v -> ret_type v ret)
                       [(pat,gl s)] in
  
  let pmon =
    fun hin -> gApp
                 (construct_match_with_return (gVar inp) ~catch_all:(catch_case (gFun ["Hin"] (fun [hin] -> pmonr (gVar hin)))) "s" (fun v -> hole)
                                              [(pat, gFun ["Hin"] (fun [hin] -> pmonl (gVar hin)))])
                 [hin]
  in
  (gen, pmon)


let letin (s : string) (b : coq_expr) (f : var -> btyp) : btyp =
  ((fun sz -> gLetIn s b (fun x -> fst (f x) sz)),
   (fun hin -> gLetIn s b (fun x -> snd (f x) hin)))
  
let lettuplein (x : var) (xs : var list) (f : btyp) : btyp =
  ((fun sz -> gLetTupleIn x xs (fst f sz)),
   (fun hin -> gLetTupleIn x xs (snd f hin)))
    

type generator_kind = Base_gen | Ind_gen 


let construct_terms
      (kind : generator_kind)
      (full_gtyp : coq_expr)
      (gen_ctr : ty_ctr)
      (dep_type : dep_type)
      (ctrs : dep_ctr list)
      (rec_name : coq_expr)
      (input_ranges : range list)
      (init_umap : range UM.t)
      (init_tmap : dep_type UM.t)
      (result : Unknown.t)
      (ih : coq_expr)
      (hleq : coq_expr) : ((coq_expr -> coq_expr list) * ((coq_expr -> coq_expr) * bool) list)
  =
  (* partially applied handle_branch *)
  let handle_branch' : dep_ctr -> btyp * bool =
    handle_branch dep_type
                  (fail_exp full_gtyp) (not_enough_fuel_exp full_gtyp) (ret_exp full_gtyp)
                  instantiate_existential_method instantiate_existential_methodST exist_bind
                  (rec_method rec_name) (rec_bind ih hleq)
                  stMaybe check_expr match_inp letin lettuplein
                  gen_ctr init_umap init_tmap input_ranges result
  in
  let terms = List.map handle_branch' ctrs in
  let gens = List.map (fun t -> fst (fst t), snd t) terms in
  let mon = List.map (fun t -> snd (fst t), snd t) terms in  
  let padNone =
    if List.exists (fun gb -> not (snd gb)) gens
    then [gNone gBool] else [] in
  let padNone_mon =
    if List.exists (fun gb -> not (snd gb)) mon
    then [((fun hin -> discriminate hin), true)] else [] in
  match kind with
  | Base_gen ->
     ((fun s -> List.map (fun t -> fst t s) (List.filter snd gens) @ padNone), (List.filter snd mon) @ padNone_mon)
  | Ind_gen ->
     ((fun s -> List.map (fun t -> fst t s) gens), mon)

let base_terms = construct_terms Base_gen
let ind_terms  = construct_terms Ind_gen              


let checkerSizedProofs
      (gen_ctr : ty_ctr)
      (ty_params : ty_param list)
      (ctrs : dep_ctr list)
      (dep_type : dep_type)
      (input_names : var list)
      (input_ranges : range list)
      (init_umap : range UM.t)
      (init_tmap : dep_type UM.t)
      (inputs : arg list)
      (result : Unknown.t)
      (rec_name : coq_expr) =
  
  (* type constructor *)
  let coqTyCtr = gTyCtr gen_ctr in

  (* parameters of the type constructor *)
  let coqTyParams = List.map gTyParam ty_params in

  (* Unused, not exported... *)
  (* Fully applied type constructor *)
  let _full_dt = gApp ~explicit:true coqTyCtr coqTyParams in

  (* The type we are generating for -- not the predicate! *)
  let full_gtyp = (gType ty_params (UM.find result init_tmap)) in

  (* The type of the derived checker *)
  let gen_type = (gOption full_gtyp) in

  (* From checkerSizedSt *)
  let aux_arb rec_name size vars =
    gMatch (gVar size)
           [ (injectCtr "O", [],
              fun _ ->
              checker_backtracking
                (base_gens (gVar size) full_gtyp gen_ctr dep_type ctrs rec_name
                           input_ranges init_umap init_tmap result))
           ; (injectCtr "S", ["size'"],
              fun [size'] ->
              checker_backtracking 
                (ind_gens (gVar size') full_gtyp gen_ctr dep_type ctrs rec_name
                          input_ranges init_umap init_tmap result))
           ]
  in

  let generator_body : coq_expr =
    gRecFunInWithArgs
      ~assumType:(gen_type)
      "aux_arb" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
      (fun (rec_name, size::vars) -> aux_arb (gVar rec_name) size vars)
      (fun rec_name -> gFun ["size"] 
                            (fun [size] -> gApp (gVar rec_name) 
                                                (gVar size :: List.map (fun i -> gVar (arg_to_var i)) inputs)
      ))
  in

  let checker inputs size = gApp (gApp generator_body inputs) [size] in
  
  let mon_true_type =
    (* fun k1 -> forall k2, forall inputs, checker k1 = Some true -> checker k2 = Some true *)
    gFun ["s1"] (fun [s1] ->
           gForall 
             (gInject "nat")
             (gFun ["s2"] (fun [s2] ->
                     gProdWithArgs
                       inputs
                       (fun inputs ->
                         let s1 = gVar s1 in
                         let s2 = gVar s2 in
                         let inputs = List.map gVar inputs in
                         gImpl (gLeq s1 s2) (gImpl (gEqType (checker inputs s1) (gSome hole gTrueb))
                                                   (gEqType (checker inputs s2) (gSome hole gTrueb)))))))
  in

  let fold_proofs hin heq proofs ind (* inductive case flag *) =
    let rec aux hin heq proofs path =
      match proofs with
      | [] -> false_ind hole hin
      | (pr, false) :: proofs -> (* base cases *)
         gMatch hin
                [ ( injectCtr "or_introl", ["Hin"],
                    fun [hin] -> gExIntro "" (fun _ -> hole) hole (gConjIntro (path (gOrIntroL (gVar hin))) heq) )
                ; ( injectCtr "or_intror", ["Hin"],
                    fun [hin] -> aux (gVar hin) (gVar hin) proofs (fun t -> gOrIntroR t) )
                ]
      | (pr, true) :: proofs when ind = false -> (* None case in base case *)
         gMatch hin
                [ ( injectCtr "or_introl", ["Hin"],
                    fun [hin] ->
                    gApp (gFun ["hin_rew"] (fun [hin] -> pr (gVar hin)))
                         [rewrite_sym (gFun ["f0"] (fun [f] -> gEqType (gApp (gVar f) [gTt]) (gSome hole (gTrueb))))
                                                                        (gVar hin) heq] )
                ; ( injectCtr "or_intror", ["Hin"],
                    fun [hin] -> aux (gVar hin) (gVar hin) proofs (fun t -> gOrIntroR t) )
                ]
      | (pr, true) :: proofs when ind = false -> (* Inductive case *)
         gMatch hin
                [ ( injectCtr "or_introl", ["Hin"],
                    fun [hin] ->
                    gApp (gFun ["hin_rew"]
                               (fun [hin] -> gExIntro "" (fun _ -> hole) hole (gConjIntro (path (gOrIntroL (gEqRefl hole))) (pr (gVar hin)))))
                         [rewrite_sym (gFun ["f0"] (fun [f] -> gEqType (gApp (gVar f) [gTt]) (gSome hole (gTrueb))))
                                      (gVar hin) heq] )
                ; ( injectCtr "or_intror", ["Hin"],
                    fun [hin] -> aux (gVar hin) (gVar hin) proofs (fun t -> gOrIntroR t) )
                ]
    in aux hin heq proofs (fun t -> t)
  in
  
  let mon_true_base_case =    
    gFun ["s2"] (fun [s2] -> 
           gFunWithArgs inputs
                        (fun inputs ->
                          gFun ["Hleq"; "Htrue"] (fun [hleq;htrue] ->
                                 let s2 = gVar s2 in
                                 let hleq = gVar hleq in
                                 let htrue = gVar htrue in

                                 let (gen, proofs) = base_terms full_gtyp gen_ctr dep_type ctrs rec_name
                                                                input_ranges init_umap init_tmap result hole hleq in
                                 
                                 let gens1 = gList (gen (gInject "O")) in
                                 let gens2 = gList (gen s2) in
                                 
                                 let succ_body =
                                   gMatch (checker_backtrack_spec_l gens1 htrue)
                                          [ ( injectCtr "ex_intro", ["_t"; "f"; "Hand"],
                                              fun [_; f; hand] -> 
                                              gMatch (gVar hand)
                                                     [ ( injectCtr "conj", ["Hin"; "Heq"],
                                                         fun [hin; heq] ->
                                                         checker_backtrack_spec_r gens2 (fold_proofs (gVar hin) (gVar heq) proofs false) ) ] ) ]
                                 in
                                 gMatch s2
                                        [ (injectCtr "O", [], fun _ -> htrue)
                                        ; (injectCtr "S", [], fun _ -> succ_body) ] )))
  in 
  let mon_true_ind_case =    
    gFun ["s1"; "IHs1"; "s2"] (fun [s1; ih; s2] -> 
           gFunWithArgs inputs
                        (fun inputs ->
                          gFun ["Hleq"; "Htrue"] (fun [hleq;htrue] ->
                                 let s1 = gVar s1 in
                                 let ih = gVar ih in
                                 let s2 = gVar s2 in
                                 let hleq = gVar hleq in
                                 let htrue = gVar htrue in

                                 let (gen, proofs) = ind_terms full_gtyp gen_ctr dep_type ctrs rec_name
                                                               input_ranges init_umap init_tmap result ih hleq in
                                 
                                 let gens1 = gList (gen s1) in
                                 let gens2 = gList (gen s2) in
                                 
                                 let succ_body =
                                   gMatch (checker_backtrack_spec_l gens1 htrue)
                                          [ ( injectCtr "ex_intro", ["_t"; "f"; "Hand"],
                                              fun [_; f; hand] -> 
                                              gMatch (gVar hand)
                                                     [ ( injectCtr "conj", ["Hin"; "Heq"],
                                                         fun [hin; heq] ->
                                                         checker_backtrack_spec_r gens2 (fold_proofs (gVar hin) (gVar heq) proofs true) ) ] ) ]
                                 in
                                 gMatch s2
                                        [ (injectCtr "O", [], fun _ -> htrue)
                                        ; (injectCtr "S", [], fun _ -> succ_body) ] )))
  in 

  
  let mon_true_proof =
    gFun ["s1"]
         (fun [s1] ->
           gApp (gInject "nat_ind")
                [mon_true_type; mon_true_base_case; mon_true_ind_case; gVar s1])
  in
  msg_debug (fnl () ++ fnl () ++ str "`Monotonicity (true) proof:" ++ fnl ());
  debug_coq_expr generator_body;
  msg_debug (fnl ());
  gRecord [("mon_true", mon_true_proof)]
