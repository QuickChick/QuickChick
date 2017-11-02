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
open Error
    
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


let rec fst_leq_proof ctrs =
  match ctrs with
  | [] -> forall_nil (gProd hole hole)
  | c :: ctrs ->
     forall_cons (gProd hole hole) ltnOSn_pair (fst_leq_proof ctrs)

let isBaseBranch ty_ctr ty = fold_ty' (fun b ty' -> b && not (sameTypeCtr ty_ctr ty')) true ty

let base_ctrs ty_ctr ctrs = List.filter (fun (_, ty) -> isBaseBranch ty_ctr ty) ctrs

let genCorr ty_ctr ctrs iargs inst_name s_inst_name c_inst_name mon_inst_name =

  (* Common helpers, refactor? *)
  let coqTyCtr = gTyCtr ty_ctr in
  let coqTyParams = List.map gVar (list_keep_every 3 iargs) in
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

  let g_instance =
    let args = (List.flatten (List.map (fun x -> [x; hole]) coqTyParams)) in
    gApp ~explicit:true inst_name args
  in

  let s_instance =
    let args = (List.flatten (List.map (fun x -> [x; hole]) coqTyParams)) in
    gApp ~explicit:true s_inst_name args
  in  

  let c_instance =
    let args = (List.flatten (List.map (fun x -> [x; hole; hole]) coqTyParams)) in
    gApp ~explicit:true c_inst_name args
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

  let ind_gens size =
    let lst =
      (List.map
         (fun (ctr,ty') ->
           gPair ((if isBaseBranch ty_ctr ty' then gInt 1 else gSucc (gVar size)),
             (gen_list (gVar size) (ctr,ty')))) ctrs)
    in
    (List.hd lst, gList (List.tl lst))
  in

  let ind_case hmon =
    gFun ["n"; "s"; "IHs"]
      (fun [n; s; ihs] ->
        let (gen, gens) = ind_gens n in
         match ctrs with
         | [] -> failwith "Must have base cases"
         | [(ctr, ty)] -> proof (gVar ihs) hmon ty 0
         | _ :: _ ->
           set_eq_trans
             (semFreq gen gens (fst_leq_proof ctrs))
             (genCase (gVar ihs) hmon (gPair (hole, hole)) ctrs))
  in

  let base_case =
    match bases with
    | [] -> failwith "Must have base cases"
    | [(ctr, ty)] -> proof hole hole ty 0
    | _ :: _ ->
      set_eq_trans
        (gApp ~explicit:true (gInject "semOneOf") [hole; fst base_gens; snd base_gens])
        (genCase hole hole hole bases)
  in

  let ret_type =
    gFun ["n"; "s"]
      (fun [n; s] ->
        set_eq
          (gApp (gInject ("semGen")) [gApp (gInject "arbitrarySized") [gVar n]])
          (gVar s))
  in

  let gen_proof =
    gFun ["n"]
      (fun [n] ->
         nat_set_ind
           full_dt g_instance s_instance c_instance base_case (ind_case (mon_proof (gVar n))) (gVar n))
  in
  msg_debug (str "Sized proof");
  debug_coq_expr gen_proof;
  gRecord [("arbitrarySizedCorrect", gen_proof)]
