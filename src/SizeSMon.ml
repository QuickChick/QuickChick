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

let list_keep_every n l =
  let rec aux i = function
    | [] -> []
    | x::xs ->
      if i == 1 then x :: aux 2 xs
      else if i == n then aux 1 xs
      else aux (i + 1) xs
  in aux 1 l

let sameTypeCtr c_ctr = function
  | TyCtr (ty_ctr', _) -> c_ctr = ty_ctr'
  | _ -> false


let isBaseBranch ty_ctr ty = fold_ty' (fun b ty' -> b && not (sameTypeCtr ty_ctr ty')) true ty

let base_ctrs ty_ctr ctrs = List.filter (fun (_, ty) -> isBaseBranch ty_ctr ty) ctrs

let sizeSMon ty_ctr ctrs iargs ty_ctr  =

  (* Common helpers, refactor? *)
  let coqTyCtr = gTyCtr ty_ctr in
  let coqTyParams = List.map gVar (list_keep_every 1 iargs) in
  let full_dt = gApp ~explicit:true coqTyCtr coqTyParams in
  let isCurrentTyCtr = sameTypeCtr ty_ctr in
  let bases = base_ctrs ty_ctr ctrs in

  (*  Could reuse code from SizeMon.ml here *)
  let rec mon_proof hmon ty n =
    let x = Printf.sprintf "m%d" n in
    match ty with
    | Arrow (ty1, ty2) ->
      let h = if isCurrentTyCtr ty1 then hmon else hole in
      gApp ~explicit:true (gInject "bindMonotonic")
           [hole; hole; hole; hole; h; gFun [x] (fun [x] -> mon_proof hmon ty2 (n+1))]
    | _ -> hole
  in

  let rec proof ih hmon ty n =
    let x = Printf.sprintf "x%d" n in
    match ty with
    | Arrow (ty1, ty2) ->
      let h =
        if isCurrentTyCtr ty1
        then ih
        else gInject "arbitraryCorrect"
      in
      let mon_proof_l = if isCurrentTyCtr ty1 then hmon else hole in
      let mon_proof_r = gFun ["m"] (fun [m] -> mon_proof hmon ty2 0) in
      set_eq_trans
        (gApp (gInject "semBindSizeMonotonic") ~explicit:true
              [hole; hole; hole; hole; mon_proof_l; mon_proof_r])
        (gApp (gInject "eq_bigcup'")
              [h; gFun [x] (fun [x] -> proof ih hmon ty2 (n+1))])
    | _ -> gApp (gInject "semReturn") [hole]
  in

  let rec genCase ih hmon list_typ ctrs =
    match ctrs with
    | [] -> failwith "Invalid type"
    | [(ctr, ty)] ->
      set_eq_trans
        (eq_bigcupl hole hole (singl_set_eq hole hole))
        (set_eq_trans (bigcup_set1 hole list_typ) (proof ih hmon ty 0))
    | (ctr, ty) :: ctrs' ->
      set_eq_trans
        (eq_bigcupl hole hole (cons_set_eq hole hole))
        (set_eq_trans
           (bigcup_setU_l hole hole hole)
           (* Take the first sets of the union *)
           (setU_set_eq_compat
              (set_eq_trans (bigcup_set1 hole list_typ) (proof ih hmon ty 0))
              (genCase ih hmon list_typ ctrs')))
  in

  let mon_proof size =
    let args = (List.flatten (List.map (fun x -> [x; hole; hole; hole]) coqTyParams)) @ [size] in
    gApp ~explicit:true mon_inst_name args
  in

  (* Code that generates the generators. Copy-pasted for the third time. XXX factor it out *)

  (* Code from ArbitrarySize.v. Regenerate generators for type annotations *)
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
    in aux 0 [] ty
  in

  let arb_body =
    gRecFunInWithArgs
      "arb_aux" [gArg ~assumName:(gInject "size") ()]
      (fun (aux_arb, [size]) ->
         gMatch (gVar size)
           [(injectCtr "O", [],
             fun _ -> oneof (List.map (create_for_branch coqTyParams aux_arb size) bases))
           ;(injectCtr "S", ["size'"],
             fun [size'] -> frequency (List.map (fun (ctr,ty') ->
                 ((if isBaseBranch ty_ctr ty' then gInt 1 else gVar size),
                  create_for_branch coqTyParams aux_arb size' (ctr,ty'))) ctrs))
           ])
      (fun x -> gVar x)
  in

  let gen_list size (ctr, ty) =
    let rec aux i acc ty : coq_expr =
      match ty with
      | Arrow (ty1, ty2) ->
        bindGen (if isCurrentTyCtr ty1 then
                   gApp arb_body [size]
                 else gInject "arbitrary")
          (Printf.sprintf "p%d" i)
          (fun pi -> aux (i+1) ((gVar pi) :: acc) ty2)
      | _ -> returnGen (gApp ~explicit:true (gCtr ctr) (coqTyParams @ List.rev acc))
    in aux 0 [] ty
  in

  let base_gens =
    let lst = (List.map (gen_list hole) bases) in
    (List.hd lst, gList (List.tl lst))
  in

  let base_gens_with_freq =
    let lst =
      (List.map
         (fun (ctr,ty') ->
           gPair (gInt 1, (gen_list (gVar size) (ctr,ty'))))
         bases)
    in
    (List.hd lst, gList (List.tl lst))
  in

  let ind_gens size =
    let lst =
      (List.map
         (fun (ctr,ty') ->
           gPair ((if isBaseBranch ty_ctr ty' then gInt 1 else gSucc (gVar size)),
             (gen_list (gVar size) (ctr,ty')))) ctrs)
    in
    (List.hd lst, gList (List.tl lst))
  in

  let ind_case s s1 s2 ihs1 =
    gFun ["n"; "s"; "IHs"]
      (fun [n; s; ihs] ->
        let (gen, gens) = ind_gens n in
         set_eq_trans
           (gApp ~explicit:true (gInject "semFreq") [hole; gen; gens])
           (genCase (gVar ihs) hmon (gPair (hole, hole)) ctrs))
  in

  let base_case s s2 =
    (* The generators should be explicitly passed to the lemmas *)
    let (g, gs) = base_gens in
    let (fg, fgs) = base_gens_with_freq in
    let (ig, igs) = ind_gens s2 in
    (* first write oneOf as freq *)
    subset_respects_set_eq_l
      (oneOf_freq g gs s)
      (* Rewrite with the semantics of freq left and right *)
      (subset_set_eq_compat
         (semFreqSize fg fgs s)
         (semFreqSize ig igs s)
         (incl_bigcup (incl_subset hole hole seq_incl_proof)))
  in

  let ret_type s s1 s2 =
    let sem s' s =
      semGenSize (arbitrarySize s') s
    in
    gImpl
      (gIsTrueLeq s1 s2)
      (set_incl (sem s1 s) (sem s2 s))
  in

  let ret_type1 s =
    gFun ["s1"; "s2"]
      (fun s1 s2 -> ret_type s s1 s2)
  in

  let ret_type2 s s1 =
    gFun ["s2"]
      (fun s2 -> ret_type s s1 s2)
  in

  let smon_proof =
    gFun ["s"]
      (fun [s] ->
         gApp ~explicit:true (gInject "nat_ind")
           [ret_type1;
            (gApp ~explicit:true (gInject "nat_ind")
               [ret_type1 s;
                gFun ["Hleq"] (fun [h] -> incl_refl);
                gFun
                  ["s2"; "IHs2"; "Hleq"]
                  (fun s2 ihs2 hleq -> base_case s s2)
               ]
            );
            (gFun
               ["s1"; "IHs1"]
               (fun s1 ihs1 ->
                 gApp ~explicit:true (gInject "nat_ind")
                   [ret_type2 s s1;
                    gFun ["Hleq"] (fun [leq] -> false_ind hole (lt0_False hleq));
                    gFun
                      ["s2"; "IHs2"; "Hleq"]
                      (fun s2 ihs2 hleq -> ind_case s s1 s2 ihs1)
                   ]
               )
            )])
  in
  debug_coq_expr smon_proof;
  gRecord [("sizeMonotonic", smon_proof)]
