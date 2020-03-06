open Pp
open Util
open GenericLib
open SetLib
open CoqLib
open Feedback

let distanceM = gInject "QuickChick.ExtractReal.dist"
let dist x y = gApp distanceM [x ; y]
let rlarge = gInject "QuickChick.ExtractReal.Rlarge"
let r0 = gInject "R0"
let rplus x y = gApp (gInject "Rplus") [x ; y]
              
(* Produces the record of the Distance typeclass *)
(* Arguments x y:
   match x with 
   | C_i vs => 
     match y with 
     | C_i vs' => 
       sum (map dist (vs, vs'))
     | _ => infinity
   | ...
 *)              
let distance_decl ty_ctr ctrs =
  let distance_body x y =
    (* For each constructor ctr of type ty: *)
    let create_branch y' rec_name (ctr, ty) =
      (ctr, generate_names_from_type "p" ty,
       fun vs ->
       gMatch ~catchAll:(Some rlarge) (gVar y')
         [ (ctr, generate_names_from_type "q" ty,
            fun vs' ->
            fold_ty_vars2 (fun _ (v1, v2) ty' ->
                            (* If recursive, distance is rec_name *)
                            if sameTypeCtr ty_ctr ty' then
                              gApp (gVar rec_name) [gVar v1; gVar v2]
                            (* Otherwise it is dist *)
                            else dist (gVar v1) (gVar v2)
                          ) 
              rplus r0 ty (List.combine vs vs')
           )
         ])
(*          
       (* if the constructor is not recursive, then it doesn't contribute to the depth *)
       if isBaseBranch ty_ctr ty then fun _ -> gInt 0
       (* Otherwise we recursively calculate the size of each recursive argument *)
       else
         fun vs ->
           let opts = fold_ty_vars (fun _ v ty' ->
               if sameTypeCtr ty_ctr ty' then [(gApp (gVar rec_name) [gVar v])]
               else []) (fun l1 l2 -> l1 @ l2) [] ty vs
           in
           (* And compute the maximum *)
           gApp (gInject "S") [maximum opts])
 *)
    in
    gRecFunIn "aux_dist" ["x'"; "y'"]
      (fun (aux_dist, [x'; y']) ->
        gMatch (gVar x') (List.map (create_branch y' aux_dist) ctrs))
      (fun aux_dist -> gApp (gVar aux_dist) [gVar x; gVar y])
  in
  gRecord [("dist", gFun ["x"; "y"] (fun [x;y] -> distance_body x y))]
                          
