open RocqExpr
open GenLib
open RocqLib

type size_inputs =
  { _ty_ctr : ty_ctr 
  ; _ctrs   : ctr_rep list
  ; _rocqTyCtr : rocq_expr
  ; _rocqTyParams : rocq_expr list
  ; _full_dt     : rocq_expr
  ; _isCurrentTyCtr : rocq_type -> bool
  } 
   
let gen_list (arg : size_inputs) size arb_body (ctr, ty) =
  let rec aux i acc ty : rocq_expr =
    match ty with
    | Arrow (ty1, ty2) ->
       bindGen (if arg._isCurrentTyCtr ty1 then
                  gApp arb_body [size]
                else gInject "arbitrary")
         (Printf.sprintf "p%d" i)
         (fun pi -> aux (i+1) ((gVar pi) :: acc) ty2)
    | _ -> returnGen (gApp ~explicit:true (gCtr ctr) (arg._rocqTyParams @ List.rev acc))
  in aux 0 [] ty

let rec fst_leq_proof ctrs =
  match ctrs with
  | [] -> forall_nil (gProd hole hole)
  | _c :: ctrs ->
     forall_cons (gProd hole hole) ltnOSn_pair (fst_leq_proof ctrs)

