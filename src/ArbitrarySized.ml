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


(* Derivation of ArbitrarySized. Contains mostly code from derive.ml *)

let list_drop_every n l =
  let rec aux i = function
    | [] -> []
    | x::xs -> if i == n then aux 1 xs else x::aux (i+1) xs
  in aux 1 l

let rec replace v x = function
  | [] -> []
  | y::ys -> if y = v then x::ys else y::(replace v x ys)


let arbitrarySized_decl ty_ctr ctrs iargs =

  let isCurrentTyCtr = function
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in
  let isBaseBranch ty = fold_ty' (fun b ty' -> b && not (isCurrentTyCtr ty')) true ty in
  let base_ctrs = List.filter (fun (_, ty) -> isBaseBranch ty) ctrs in

  let tyParams = List.map gVar (list_drop_every 2 iargs) in

  let arbitrary_decl =
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

    let arb_body =
      gRecFunInWithArgs
        "arb_aux" [gArg ~assumName:(gInject "size") ()]
        (fun (aux_arb, [size]) ->
           gMatch (gVar size)
             [(injectCtr "O", [],
               fun _ -> oneof (List.map (create_for_branch tyParams aux_arb size) bases))
             ;(injectCtr "S", ["size'"],
               fun [size'] -> frequency (List.map (fun (ctr,ty') ->
                   ((if isBaseBranch ty' then gInt 1 else gVar size),
                    create_for_branch tyParams aux_arb size' (ctr,ty'))) ctrs))
             ])
        (fun x -> gVar x) in
    gFun ["s"] (fun [s] -> gApp arb_body [gVar s])
  in

  (* Derive shrinking *)
  let shrink_decl = 
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

  gRecord [("arbitrarySize", arbitrary_decl); ("shrinkSize", shrink_decl)]
