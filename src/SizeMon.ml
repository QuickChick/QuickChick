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

let list_drop_every n l =
  let rec aux i = function
    | [] -> []
    | x::xs -> if i == n then aux 1 xs else x::aux (i+1) xs
  in aux 1 l

let sameTypeCtr c_ctr = function
  | TyCtr (ty_ctr', _) -> c_ctr = ty_ctr'
  | _ -> false


let isBaseBranch ty_ctr ty = fold_ty' (fun b ty' -> b && not (sameTypeCtr ty_ctr ty')) true ty

let base_ctrs ty_ctr ctrs = List.filter (fun (_, ty) -> isBaseBranch ty_ctr ty) ctrs

let sizeMon ty_ctr ctrs size iargs genName =

  (* Common helpers, refactor? *)
  let coqTyCtr = gTyCtr ty_ctr in
  let coqTyParams = List.map gVar (list_drop_every 2 iargs) in
  let full_dt = gApp ~explicit:true coqTyCtr coqTyParams in
  let isCurrentTyCtr = sameTypeCtr ty_ctr in
  let bases = base_ctrs ty_ctr ctrs in

  let rec proof ih ty n =
    let x = Printf.sprintf "x%d" n in
    match ty with
    | Arrow (ty1, ty2) ->
      let h = if isCurrentTyCtr ty1 then ih else hole in
      gApp ~explicit:true (gInject "bindMonotonic") [hole; hole; hole; hole; h; gFun [x] (fun [x] -> proof ih ty2 (n+1))]
    | _ -> hole
  in

  let rec elim_cases h ih ctrs n =
    let hr = Printf.sprintf "Hl%d" n in
    let hl = Printf.sprintf "Hr%d" n in

    match ctrs with
    | [] -> false_ind hole h
    | (ctr, ty) :: ctrs' ->
      gMatch h
        [(injectCtr "or_introl", [hl],
          fun [hl] -> gMatch (gVar hl) [(injectCtr "erefl", [], fun [] -> proof ih ty 0)]);
         (injectCtr "or_intror", [hr],
          fun [hr] -> elim_cases (gVar hr) ih ctrs' (n+1))]
  in
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

  let base_gens = gList (List.map (gen_list hole) bases) in
  let ind_gens size =
    gList
      (List.map
         (fun (ctr,ty') ->
            gPair ((if isBaseBranch ty_ctr ty' then gInt 1 else gSucc (gVar size)),
                   (gen_list (gVar size) (ctr,ty')))) ctrs)
  in
  let base_case =
    (gApp
       (gInject "oneofMonotonic")
       [hole; hole; gFun [("x")] (fun [x] -> gFunTyped [("H", gApp (gInject "seq_In") [base_gens; gVar x])] (fun [h] -> elim_cases (gVar h) hole bases 0))])
  in

  let ind_case =
    gFun ["size"; "IHs"]
      (fun [size; ihs] ->
         gApp
           (gInject "frequencySizeMonotonic_alt")
           [hole; hole; hole; gFun [("x")] (fun [x] -> gFunTyped [("H", gApp (gInject "seq_In") [ind_gens size; gVar x])] (fun [h] -> elim_cases (gVar h) (gVar ihs) ctrs 0))])
  in

  let ret_type =
    gFun ["s"]
         (fun [s] -> 
          gApp (gInject "SizeMonotonic")
            (* [gApp (gInject "arbitrarySized") [gVar s]]) *)
            [gApp ~explicit:true (gInject "arbitrarySized") [full_dt; genName; gVar s]])
  in 
  let mon_proof =
    gApp ~explicit:true (gInject "monotonic") [hole; hole; (gApp (gInject "nat_ind") [ret_type; base_case; ind_case; size])]
  in
  debug_coq_expr mon_proof;
  gRecord [("monotonic", mon_proof)]
