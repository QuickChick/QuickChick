open Constrexpr
open Error

open GenericLib
open Pp

(* P : c1 es | .... => P_ : c1_ es* .... *)
let renamer (ty_ctr, ty_params, ctrs, typ) : dep_dt =
  let ty_ctr' = gInjectTyCtr ((ty_ctr_to_string ty_ctr) ^ "_") in
  let rec rename_dt = function
      | DTyCtr (tc, dts) ->
         if tc = ty_ctr then
           DTyCtr (ty_ctr', List.map rename_dt dts)
         else
           DTyCtr (tc, List.map rename_dt dts)
      | DArrow (dt1, dt2) ->
          DArrow (rename_dt dt1, rename_dt dt2)
      | DProd  ((v, dt1), dt2) ->
         DProd ((v, rename_dt dt1), rename_dt dt2)
      | DTyParam tp -> DTyParam tp
      | DCtr (c, dts) ->
         DCtr (c, List.map rename_dt dts)
      | DTyVar v -> DTyVar v
      | DApp (dt, dts) ->
         DApp (rename_dt dt, List.map rename_dt dts)
      | DNot dt -> DNot (rename_dt dt)
      | DHole -> DHole
  in
  let rename_dep_ctr (c, dt) : dep_ctr =
    let c' = injectCtr (constructor_to_string c ^ "_") in
    (c', rename_dt dt)
  in
  let ctrs' = List.map rename_dep_ctr ctrs in
  let typ' = rename_dt typ in
  (ty_ctr', ty_params, ctrs', typ')
   
let merge ind1 ind2 ind = 
(* (fun id => body) *)  
  match ind1 with 
  | { CAst.v = CLambdaN ([CLocalAssum ([{ CAst.v = Names.Name id1; CAst.loc = _loc2 }], _kind, _type)], body1); _ } ->
    (* Extract (x1,x2,...) if any, P and arguments *)
    let (p1, args1) =
      match body1 with 
      | { CAst.v = CApp (p, args); _ } -> (p, args)
      | _ -> qcfail "Merge/Not App"
    in     
    let dt1 : (ty_ctr * ty_param list * dep_ctr list * dep_type) = 
      match coerce_reference_to_dep_dt p1 with
      | Some dt -> msg_debug (str (dep_dt_to_string dt) ++ fnl()); dt 
      | None -> failwith "Not supported type"
    in
    msg_debug (str (dep_dt_to_string (renamer dt1)) ++ fnl ());
    define_new_inductive (renamer dt1)
  | _ -> qcfail "Merge/NotLam"
