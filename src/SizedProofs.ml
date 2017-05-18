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
open Feedback
open Unify

(* arguments to handle_branch *)
let fail_exp = set_empty

let ret_exp (c : coq_expr) =
  set_singleton c

let ret_type (s : var) (match_expr : var -> coq_expr -> coq_expr -> coq_expr) = hole

let class_method = set_full

let class_methodST (n : int) (pred : coq_expr) =
  pred

let rec_method (rec_name : coq_expr) (size : coq_expr) (n : int)  (l : coq_expr list) =
  gApp rec_name (size :: l)

let bind (opt : bool) (m : coq_expr) (x : string) (f : var -> coq_expr) =
  set_bigcup x m f

let stMaybe (opt : bool) (g : coq_expr) (x : string) (checks : ((coq_expr -> coq_expr) * int) list) =
  let rec sumbools_to_bool x lst =
    match lst with
    | [] -> gApp g [gVar x]
    | (chk, _) :: lst' ->
      matchDec (chk (gVar x)) (fun heq -> gFalse) (fun hneq -> sumbools_to_bool x lst')
  in
  gFun [x] (fun [x] -> sumbools_to_bool x checks)

let ret_type_dec (s : var) (left : coq_expr) (right : coq_expr) =
      gMatch (gVar s)
      [ (injectCtr "left", ["eq"], fun _ -> left)
      ; (injectCtr "right", ["neq"], fun _ -> right) ]


let check_expr (n : int) (scrut : coq_expr) (left : coq_expr) (right : coq_expr) =
  gMatchReturn scrut
    "s" (* as clause *)
    (fun v -> ret_type v ret_type_dec)
    [ (injectCtr "left", ["eq" ] , fun _ -> left)
    ; (injectCtr "right", ["neq"], fun _ -> right) 
    ]

let match_inp (inp : var) (pat : matcher_pat) (left : coq_expr) (right  : coq_expr) =
  let ret v left right =
    construct_match (gVar v) ~catch_all:(Some right) [(pat, left)]
  in
  construct_match_with_return
    (gVar inp) ~catch_all:(Some right) "s" (fun v -> ret_type v ret)
    [(pat,left)]


module OrdInt = struct 
  type t = int
  let compare (x : int) (y : int) : int = compare x y
end

module IntMap = Map.Make(OrdInt)

type proofMap = (coq_expr -> coq_expr) IntMap.t

let sizedEqProofs_body
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
  let full_gtyp = gType ty_params (nthType n dep_type) in

  (* The type of the dependent generator *)
  let gen_type = gGen (gOption full_gtyp) in

  (* Fully applied predicate (parameters and constructors) *)
  let full_pred inputs =
    gFun ["_forGen"] (fun [fg] -> gApp (full_dt) (list_insert_nth (gVar fg) inputs (n-1)))
  in
  (* gen_ctr dep_type gen_type ctrs input_names inputs n register_arbitrary *)
  (* class_name full_gtyp full_pred inputs base_gen ind_gen = *)

  let full_prop gtyp inputs =
    gApp (full_dt) (list_insert_nth gtyp inputs (n-1))
  in

  let input_vars = List.map fresh_name input_names in
  
  let zero_set inputs =
    let handle_branch'  =
      handle_branch n dep_type inputs
        fail_exp ret_exp class_method class_methodST
        (rec_method (gVar (make_up_name ())) (gVar (make_up_name ()))) bind stMaybe check_expr match_inp
        gen_ctr (fun _ -> ())
    in
    (List.fold_right
       (fun c exp ->
          let (p, b) = handle_branch' c in
          if b then
            set_union p exp
          else exp
       )
       ctrs (set_empty))
  in

  let succ_set rec_name size inputs =
    let handle_branch'  =
      handle_branch n dep_type inputs
        fail_exp ret_exp class_method class_methodST
        (rec_method (gVar rec_name) (gVar size)) bind stMaybe check_expr match_inp
        gen_ctr (fun _ -> ())
    in
    (List.fold_right
       (fun c exp ->
          let (p, b) = handle_branch' c in
          set_union p exp
       ) ctrs (set_empty))
  in

    let aux_iter rec_name size vars =
    gMatch (gVar size)
      [ (injectCtr "O", [],
         fun _ -> zero_set vars)
      ; (injectCtr "S", ["size'"],
         fun [size'] -> succ_set rec_name size' vars)
      ]
  in

  let iter_body : coq_expr =
    gRecFunInWithArgs
      "aux_iter" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
      (fun (rec_name, size::vars) -> aux_iter rec_name size vars)
      (fun rec_name -> gFun ["size"] 
          (fun [size] -> gApp (gVar rec_name) (gVar size :: List.map gVar input_vars)
          ))
  in

  let fail_exp_mon : coq_expr * coq_expr * coq_expr =
    (set_empty, set_empty, set_incl_refl)
  in

  let ret_exp_mon (x : coq_expr) : coq_expr * coq_expr * coq_expr =
    (set_singleton x, set_singleton x, set_incl_refl)
  in

  let class_method_mon : coq_expr * coq_expr * coq_expr =
    (set_full, set_full, set_incl_refl)
  in

  let class_methodST_mon (n : int) (pred : coq_expr) : coq_expr * coq_expr * coq_expr =
    (pred, pred, set_incl_refl)
  in

  let rec_method_mon (s1 : coq_expr) (s2 : coq_expr) (ih : coq_expr list -> coq_expr) (n : int) (l : coq_expr list)
    : coq_expr * coq_expr * coq_expr =
    let iter_body args : coq_expr =
      gRecFunInWithArgs
        "aux_iter" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs)
        (fun (rec_name, size::vars) -> aux_iter rec_name size vars)
        (fun rec_name -> gApp (gVar rec_name) args)
    in
    (iter_body (s1 :: l), iter_body (s2 :: l), ih l) (* ih should be already applied to the arguments, only the inputs should be missing *)
  in

  let bind_mon (opt : bool) (m : coq_expr * coq_expr * coq_expr) (x : string) (f : var -> coq_expr * coq_expr * coq_expr) =
    let (s1, s2, p) = m in 
    (set_bigcup x s1 (fun x -> let (s, _, _) =  f x in s),
     set_bigcup x s2 (fun x -> let (_, s, _) =  f x in s),
     incl_bigcup_compat p (gFun [x] (fun [x] -> let (_, _, s) = f x in s)))
  in

  let ret_type_dec (s : var) (left : coq_expr) (right : coq_expr) =
    gMatch (gVar s)
      [ (injectCtr "left", ["eq"], fun _ -> left)
      ; (injectCtr "right", ["neq"], fun _ -> right) ]
  in

  let check_expr_mon (n : int) (scrut : coq_expr)
        (left : coq_expr * coq_expr * coq_expr) (right : coq_expr * coq_expr * coq_expr)
    : coq_expr * coq_expr * coq_expr =
    let (sl1, sl2, pl) = left in
    let (sr1, sr2, pr) = right in
    (gMatchReturn scrut
       "s" (* as clause *)
       (fun v -> ret_type v ret_type_dec)
       [ (injectCtr "left", ["eq" ] , fun _ -> sl1)
       ; (injectCtr "right", ["neq"], fun _ -> sr1) 
       ],
     gMatchReturn scrut
       "s" (* as clause *)
       (fun v -> ret_type v ret_type_dec)
       [ (injectCtr "left", ["eq" ] , fun _ -> sl2)
       ; (injectCtr "right", ["neq"], fun _ -> sr2)
       ],
      gMatchReturn scrut
        "s" (* as clause *)
        (fun v -> set_incl (ret_type_dec v sl1 sr1) (ret_type_dec v sl2 sr2))
        [ (injectCtr "left", ["eq" ] , fun _ -> pl)
        ; (injectCtr "right", ["neq"], fun _ -> pr)
        ])
  in

  let match_inp_mon (inp : var) (pat : matcher_pat)
        (left : coq_expr * coq_expr * coq_expr ) (right : coq_expr * coq_expr * coq_expr )
    : coq_expr * coq_expr * coq_expr =
    let (sl1, sl2, pl) = left in
    let (sr1, sr2, pr) = right in
    let ret v left right =
      construct_match (gVar v) ~catch_all:(Some right) [(pat, left)]
    in
    (construct_match_with_return
       (gVar inp) ~catch_all:(Some sr1) "s" (fun v -> ret_type v ret)
       [(pat,sl1)],
     construct_match_with_return
       (gVar inp) ~catch_all:(Some sr2) "s" (fun v -> ret_type v ret)
       [(pat,sl2)],
    construct_match_with_return
      (gVar inp) ~catch_all:(Some pr)
      "s" (fun v -> set_incl (ret v sl1 sr1) (ret v sl2 sr2))
      [(pat, pl)])
  in

  let stMaybe_mon (opt : bool) (exp : coq_expr * coq_expr * coq_expr) (x : string) (checks : ((coq_expr -> coq_expr) * int) list)
    : coq_expr * coq_expr * coq_expr =
    let (g1, g2, p) = exp in 
    let rec sumbools_to_bool x lst g =
    match lst with
      | [] -> gApp g [gVar x]
      | (chk, _) :: lst' ->
        matchDec (chk (gVar x)) (fun heq -> gFalse) (fun hneq -> sumbools_to_bool x lst' g)
    in
    let rec sumbools_to_bool_proof x lst : coq_expr =
      match lst with
      | [] -> gApp p [gVar x]
      | (chk, n) :: lst' ->
        let s1 = sumbools_to_bool x lst' g1 in
        let s2 = sumbools_to_bool x lst' g2 in
        gMatchReturn (chk (gVar x))
          "s" (* as clause *)
          (fun v -> gImpl (ret_type_dec v gFalse s1) (ret_type_dec v gFalse s2))
          [ (injectCtr "left", ["heq"],
             fun [hn] -> gApp set_incl_refl [gVar x])
          ; (injectCtr "right", ["hneq"],
             fun [hn] -> sumbools_to_bool_proof x lst')
          ]
    in
    (gFun [x] (fun [x] -> sumbools_to_bool x checks g1),
     gFun [x] (fun [x] -> sumbools_to_bool x checks g2),
     gFun [x] (fun [x] -> sumbools_to_bool_proof x checks))
  in

  let rec elim_base_cases_mon s1 s2 (inputs : var list) ctrs =
    let handle_branch' (c : dep_ctr) =
      handle_branch n dep_type inputs
        fail_exp_mon ret_exp_mon class_method_mon class_methodST_mon
        (rec_method_mon s1 s2 (fun _ -> gVar (make_up_name ())))
        bind_mon stMaybe_mon check_expr_mon match_inp_mon
        gen_ctr (fun _ -> ()) c
    in
    match ctrs with
    | [] -> set_incl_refl
    | c :: ctrs' ->
      let ((_, _, p), b) = handle_branch' c in
      if b then
        setU_set_subset_compat p (elim_base_cases_mon s1 s2 inputs ctrs')
      else
        setU_subset_r hole (elim_base_cases_mon s1 s2 inputs ctrs')
  in

  let rec elim_ind_cases_mon s1 s2 (ih : coq_expr list -> coq_expr) (inputs : var list) ctrs =
    let handle_branch' (c : dep_ctr)  =
      handle_branch n dep_type inputs
        fail_exp_mon ret_exp_mon class_method_mon class_methodST_mon
        (rec_method_mon s1 s2 ih)
        bind_mon stMaybe_mon check_expr_mon match_inp_mon
        gen_ctr (fun _ -> ()) c
    in
    match ctrs with
    | [] -> set_incl_refl
    | c :: ctrs' ->
      let ((_, _, p), b) = handle_branch' c in
      setU_set_subset_compat p (elim_ind_cases_mon s1 s2 ih inputs ctrs')
  in

  let mon_proof : coq_expr =
    let iter_body args : coq_expr =
      gRecFunInWithArgs
        "aux_iter" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
        (fun (rec_name, size::vars) -> aux_iter rec_name size vars)
        (fun rec_name -> gApp (gVar rec_name) args)
    in
    let inps = List.map gVar input_vars in
    let ret_type n1 n2 inps = gImpl (gLeq n1 n2) (set_incl ((iter_body (n1 :: inps))) (iter_body (n2 :: inps))) in
    let ind_ret_type = (* fun n1 => forall n2, forall inps, n1 <= n2 -> iter n1 inps \subset iter n2 inps *)
      gFun ["n1"]
        (fun [n1] ->
           gProdWithArgs ((gArg ~assumName:(gVar (fresh_name "n2")) ()) :: inputs)
             (fun (n2 :: inps) -> ret_type (gVar n1) (gVar n2) (List.map gVar inps)))
    in
    let nested_ind_type n1 inps =
      gFun ["n2"] (fun [n2] -> ret_type n1 (gVar n2) inps)
    in
    gFun ["n1"; "n2"]
      (fun [n1; n2] ->
         gApp
           (nat_ind
              ind_ret_type
              (gFun ["n2"]
                 (fun [n2] ->
                    gFunWithArgs inputs
                      (fun inps ->
                         let inps' = List.map gVar inps in
                         gApp
                           (nat_ind
                              (nested_ind_type (gInt 0) inps')
                              (gFun ["Hleq"] (fun [hleq] -> set_incl_refl))
                              (gFun ["n2"; "IHn2"; "Hleq"] (fun [n2; _; hleq] ->
                                                              elim_base_cases_mon (gInt 0) (gVar n2) inps ctrs
                                                            )))
                           [gVar n2])))
              (gFun ["n1"; "IHn1"; "n2"]
                 (fun [n1; ihn1; n2] ->
                    gFunWithArgs inputs
                      (fun inps ->
                         let inps' = List.map gVar inps in
                         gApp
                           (nat_ind
                              (nested_ind_type (gSucc (gVar n1)) inps')
                              (gFun ["Hleq"] (fun [hleq] -> false_ind hole (lt0_False (gVar hleq))))
                              (gFun ["n2"; "IHn2"; "Hleq"] (fun [n2; _; hleq]->
                                                              let ih l = gApp (gApp (gVar ihn1) ((gVar n2) :: l)) [gVar hleq] in
                                                              elim_ind_cases_mon (gVar n1) (gVar n2) ih inps ctrs
                                                            )))
                           [gVar n2]))))
           ((gVar n1) :: (gVar n2) :: inps))
  in

  (* arguments to handle_branch for left to right direction of the proof *)

  let proof_map : proofMap ref = ref IntMap.empty in

  let fail_exp_left : coq_expr * (var -> coq_expr) =
    (set_empty, fun hcur -> false_ind hole (gVar hcur))
  in

  let ret_exp_left (c : dep_ctr) (x : coq_expr) : coq_expr * (var -> coq_expr) =
    (set_singleton x,
     fun hcur ->
       let (c, typ) = c in
       let rec construct_proof typ n acc =
         match typ with
         | DTyCtr _ ->
           (* XXX currently not handling type parameters *)
           rewrite (gVar hcur) (gApp (gCtr c) (List.rev acc))
         | DProd ((x, dt1), dt2) ->
           (* XXX ??? *)
           construct_proof dt2 n (hole :: acc)
         | DArrow (dt1, dt2) ->
           (* at this point the set should be a singleton and curr_set
              just and equality proof *)
           let p =
             try IntMap.find n !proof_map 
             with Not_found -> failwith "Proof not present in the environment"
           in
           construct_proof dt2 (n + 1) ((p (gVar hcur)) :: acc) 
       in
       construct_proof typ 0 [])
  in

  let class_method_left : coq_expr * (var -> (var -> coq_expr) -> coq_expr) =
    (set_full,
     fun (hc : var) (cont : var -> coq_expr) ->
       let name = "HT" in
       gMatch (gVar hc)
         [(injectCtr "conj", [name; "Hcur"],
           fun [ht; hcur] -> cont hcur)])
  in 


  let class_methodST_left (n : int) (pred : coq_expr) : coq_expr * (var -> (var -> coq_expr) -> coq_expr) =
    (pred,
     fun (hc : var) (cont : var -> coq_expr) ->
       let name = Printf.sprintf "Hp%d" n in
       gMatch (gVar hc)
         [(injectCtr "conj", [name; "Hcur"],
           fun [hn; hcur] ->
             (* Add the proof of pred to the map *)
             proof_map :=
               IntMap.add n (fun e -> gVar hn) !proof_map;
             cont hcur)])
  in

  let rec_method_left (ih : coq_expr) (size : coq_expr) (n : int) (l : coq_expr list)
    : coq_expr * (var -> (var -> coq_expr) -> coq_expr) =
    let iter_body args : coq_expr =
      gRecFunInWithArgs
        "aux_iter" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
        (fun (rec_name, size::vars) -> aux_iter rec_name size vars)
        (fun rec_name -> gApp (gVar rec_name) args)
    in
    (iter_body (size :: l),
     fun (hc : var) (cont : var -> coq_expr) ->
       let name = Printf.sprintf "Hp%d" n in
       gMatch (gVar hc)
         [(injectCtr "conj", [name; "Hcur"],
           fun [hn; hcur] ->
             (* Add the proof of pred to the proof map *)
             let proof eq =
               (* rewrite the final equation in the IH and apply to the
                  inputs and hn *)
               gApp ih ((hole :: l) @ [gVar hn])
             in
             proof_map :=
               IntMap.add n proof !proof_map;
             cont hcur)])
  in

  let bind_left (opt : bool) (m : coq_expr * (var -> (var -> coq_expr) -> coq_expr))
        (x : string) (f : var -> coq_expr * (var -> coq_expr)) : coq_expr * (var -> coq_expr) =
    let (m, cont) = m in
    (set_bigcup x m (fun x -> fst (f x)),
     fun hcur ->
       gMatch (gVar hcur)
       [(injectCtr "ex_intro", [x; "Hc"],
         fun [x; hc] -> cont hc (snd (f x))
        )])
  in

  let ret_type_left set x inputs =
    gImpl
      (gApp set [(gVar x)])
      (full_prop (gVar x) (List.map gVar inputs))
  in

  let ret_type_left_hole set x =
    gImpl
      (gApp set [(gVar x)]) hole
  in


  let ret_type_dec (s : var) (left : coq_expr) (right : coq_expr) =
    gMatch (gVar s)
      [ (injectCtr "left", ["eq"], fun _ -> left)
      ; (injectCtr "right", ["neq"], fun _ -> right) ]
  in
  
  let check_expr_left (x : var) (n : int) (scrut : coq_expr)
        (left : coq_expr * (var -> coq_expr)) (right : coq_expr * (var -> coq_expr))
    : coq_expr * (var -> coq_expr) =
    let (lset, lproof) = left in
    let (rset, rproof) = right in
    let name = Printf.sprintf "Hp%d" n in
    let namecur = Printf.sprintf "Hcur%d" n in
    (gMatchReturn scrut
       "s" (* as clause *)
       (fun v -> hole)
       [ (injectCtr "left", ["eq" ] , fun _ -> lset)
       ; (injectCtr "right", ["neq"], fun _ -> rset) 
       ],
     fun hcur ->
       gApp
         (gMatchReturn scrut
            "s" (* as clause *)
            (fun v -> ret_type_left_hole (ret_type_dec v lset rset) x)
            [ (injectCtr "left", [name],
               fun [hn] -> gFun [namecur]
                           (fun [hcur] ->
                              proof_map :=
                                IntMap.add n (fun e -> gVar hn) !proof_map;
                              lproof hcur))
            ; (injectCtr "right", ["neq"],
               fun _ -> gFun [namecur] (fun [hcur] -> rproof hcur))
            ]) [gVar hcur]
    )
  in

  let match_inp_left (x : var) (inp : var) (pat : matcher_pat)
        (left : coq_expr * (var -> coq_expr)) (right  : coq_expr * (var -> coq_expr))
    : coq_expr * (var -> coq_expr) =
    let (lset, lproof) = left in
    let (rset, rproof) = right in
    let ret v left right =
      ret_type_left_hole (construct_match (gVar v) ~catch_all:(Some rset) [(pat, lset)])
        x
    in
    let namecur = Printf.sprintf "Hcur%d" n in
    (construct_match_with_return
       (gVar inp) ~catch_all:(Some rset) "s" (fun v -> hole)
       [(pat, lset)],
     fun hcur ->
       gApp
         (construct_match_with_return
            (gVar inp) ~catch_all:(Some (gFun [namecur] (fun [hcur] -> rproof hcur))) "s" (fun v -> ret v lset rset)
            [(pat, gFun [namecur] (fun [hcur] ->lproof hcur))]) [gVar hcur])
  in

  let stMaybe_left (y : var) (opt : bool) (exp : coq_expr * (var -> (var -> coq_expr) -> coq_expr))
        (x : string) (checks : ((coq_expr -> coq_expr) * int) list)
    : coq_expr * (var -> (var -> coq_expr) -> coq_expr) =
    let ret_type set =
      gImpl set hole
    in
    let rec sumbools_to_bool x lst =
      match lst with
      | [] ->
        let (set, proof) = exp in
        gApp set [gVar x]
      | (chk, _) :: lst' ->
        matchDec (chk (gVar x)) (fun heq -> gFalse) (fun hneq -> sumbools_to_bool x lst')
    in
    let rec sumbools_to_bool_proof x hl hr cont lst : coq_expr =
      match lst with
      | [] ->
        let (set, proof) = exp in
        gApp (gFun ["Hcur"] (fun [hcur] -> proof hcur cont)) [(gConjIntro (gVar hl) (gVar hr))]
      | (chk, n) :: lst' ->
        let set = sumbools_to_bool x lst' in
        let name = Printf.sprintf "Hp%d" n in
        let namecur = Printf.sprintf "Hl%d" n in
        gApp
          (gMatchReturn (chk (gVar x))
             "s" (* as clause *)
             (fun v -> ret_type (ret_type_dec v gFalse set))
             [ (injectCtr "left", ["heq"],
                fun [hn] ->
                  gFun [namecur]
                    (fun [hcur] -> false_ind hole (gVar hcur)))
             ; (injectCtr "right", [name],
                fun [hn] ->
                  gFun [namecur]
                    (fun [hcur] ->
                       proof_map :=
                         IntMap.add n (fun e -> gVar hn) !proof_map;
                       sumbools_to_bool_proof x hcur hr cont lst'))
             ]) [gVar hl]
    in 
    (gFun [x] (fun [x] -> sumbools_to_bool x checks),
     fun hcur cont ->
       gMatch (gVar hcur)
         [(injectCtr "conj", ["Hl"; "Hr"],
           fun [hl; hr] ->
             sumbools_to_bool_proof (fresh_name x) hl hr cont checks)
         ])
  in 

  (* Left to right direction *)

  let ret_type_left_ind  =
    let iter_body args : coq_expr =
      gRecFunInWithArgs
        "aux_iter" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
        (fun (rec_name, size::vars) -> aux_iter rec_name size vars)
        (fun rec_name -> gApp (gVar rec_name) args)
    in
    gFun ["n"]
      (fun [n] ->
         gProdWithArgs
           ((gArg ~assumName:(gVar (fresh_name "x")) ()) :: inputs)
           (fun (x :: inputs) ->
              ret_type_left (iter_body ((gVar n) :: (List.map gVar inputs))) x inputs)
      )
  in

  let rec elim_base_cases x hin ctrs m inputs : coq_expr =
    let hr = Printf.sprintf "Hl%d" m in
    let hl = Printf.sprintf "Hr%d" m in
    let handle_branch' (c : dep_ctr) : (coq_expr * (var -> coq_expr)) * bool =
      handle_branch n dep_type inputs
        fail_exp_left (ret_exp_left c) class_method_left class_methodST_left
        (rec_method_left (gVar (make_up_name ())) (gVar (make_up_name ())))
        bind_left (stMaybe_left x) (check_expr_left x) (match_inp_left x)
        gen_ctr (fun _ -> ()) c
    in
    match ctrs with
    | [] -> false_ind hole (gVar hin)
    | c :: ctrs' ->
      let (p, b) : (coq_expr * (var -> coq_expr)) * bool = handle_branch' c in
      if b then
        gMatch (gVar hin)
          [(injectCtr "or_introl", [hl],
            fun [hl] -> snd p hl);
           (injectCtr "or_intror", [hr],
            fun [hr] -> elim_base_cases x hr ctrs' (m + 1) inputs)]
      else elim_base_cases x hin ctrs' (m + 1) inputs
  in

  let rec elim_ind_cases x hin size ih ctrs m inputs : coq_expr =
    let hr = Printf.sprintf "Hl%d" n in
    let hl = Printf.sprintf "Hr%d" n in
    let handle_branch' c : (coq_expr * (var -> coq_expr)) * bool =
      handle_branch n dep_type inputs
        fail_exp_left (ret_exp_left c) class_method_left class_methodST_left
        (rec_method_left (gVar ih) (gVar size))
        bind_left (stMaybe_left x) (check_expr_left x) (match_inp_left x)
        gen_ctr (fun _ -> ()) c
    in
    match ctrs with
    | [] -> false_ind hole (gVar hin)
    | c :: ctrs' ->
      let (p, b) : (coq_expr * (var -> coq_expr)) * bool = handle_branch' c in
      gMatch (gVar hin)
        [(injectCtr "or_introl", [hl],
          fun [hl] -> snd p hl);
         (injectCtr "or_intror", [hr],
          fun [hr] -> elim_ind_cases x hr size ih ctrs' (m + 1) inputs)]
  in

  let left_base_case =
    gFun ["x"]
      (fun [x] ->
         gFunWithArgs
           inputs
           (fun inputs ->
              gFun ["hin"]
                (fun [hin] -> elim_base_cases x hin ctrs 0 inputs)))
  in

  let left_ind_case =
    gFun ["size"; "IHs"; "x"]
      (* XXX need inputs with gen here!!!!!! *)
      (fun [size; ihs; x] ->
         gFunWithArgs
           inputs
           (fun inputs ->
              gFun ["hin"]
              (fun [hin] ->
                elim_ind_cases x hin size ihs ctrs 0 inputs)))
  in

  let leftp (x : var) : coq_expr =
    (* Hin : \bigcup(n : nat) (succ ^ n zero) x *)
    gFun ["Hin"]
      (fun [hin] ->
         gMatch (gVar hin)
           [(injectCtr "ex_intro", ["s"; "Hc"],
             fun [s; hc] ->
               gMatch (gVar hc)
                 [(injectCtr "conj", ["Hl"; "Hin"],
                   fun [hl; hin] ->
                     gApp
                       (nat_ind ret_type_left_ind left_base_case left_ind_case)
                       (((gVar s) :: (gVar x) :: (List.map gVar input_vars)) @ [gVar hin])
                  )]
            )])
  in

  (* let rightp (x : var) : coq_exp = *)  
  (* in *)

  let spec =
    gFun ["x"]
      (fun [x] -> (leftp x))
  in
  (* msg_debug (str "zero"); *)
  (* debug_coq_expr zero_set; *)
  msg_debug (str "iter");
  debug_coq_expr iter_body;
  msg_debug (str "spec");
  debug_coq_expr spec;
  msg_debug (str "mon proof");
  debug_coq_expr mon_proof;

  gRecord [("iter", iter_body); ("mon", mon_proof); ("spec", spec)]
