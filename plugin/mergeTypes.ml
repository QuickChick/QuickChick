open Constrexpr
open Error

open GenericLib
open Pp

open Libnames (*I think this is where qualid is*)
(* open Names (*I think this is where Id.t is*) *)
open UnifyQC

(*
 make clean
 make install
 make -C ..

 emacs commands compile and recompile
*)


(*
data Term = Term Ctr [Term] | Hole String Hole deriving (Eq, Show)

data Constructor = Constructor String [(String, [Term])] [([Term], Term)] [Term] Term
--                              ^ other relations being called ^ recursive calls ^output As ^output T
data Relation = Relation String [Constructor] *)

(*
The plan is that I will use vars directly instead of holes.
genericLib already gives me vars where I need them, and they already have the exact behavior that I want.
*)

type rec_arg = dep_type list * dep_type (*arguments to a recursive call. Separate term is the shared parameter*)
type ctr_data =
  (var * dep_type) list (*forall variables*)
  * rec_arg list (*recursive calls*)
  (* * (ty_ctr * dep_type list) list (*nonrecursive calls*) *)
  * dep_type list (*nonrecursive calls*)
  * rec_arg (*output parameters*)

(* Separate out the shared parameter from a list of parameters *)
let rec separate_shared (terms : 'a list) (param_pos : int) : 'a list * 'a = 
  match terms with
  | term :: terms -> if param_pos = 0
    then (terms, term)
    else let (ts, t) = separate_shared terms (param_pos - 1) in
         (term :: ts, t)


(* The reverse of separate_shared. param_pos should be the position where shared will end up in
the resulting output list. *)
let rec replace_shared ((terms, shared) : 'a list * 'a) (param_pos : int) : 'a list = 
  if param_pos = 0
    then shared :: terms
    else match terms with (term :: terms) -> term :: replace_shared (terms, shared) (param_pos - 1)

let convertConstructor (me : ty_ctr) (ctr : dep_type) (param_pos : int) : ctr_data =
  let rec convertConstructorAux (ctr : dep_type) (me : ty_ctr) vs rs os : ctr_data =
    match ctr with
    | DProd  ((v, dt1), dt2) -> convertConstructorAux dt2 me ((v , dt1) :: vs) rs os
    | DTyCtr (tc, dts) -> (vs , rs , os , separate_shared dts param_pos) (* The output of the constructor *)
    | DArrow (DTyCtr (c , dts), dt2) -> if c = me then (* Parse an argument to constructor, which could be recursive *)
      convertConstructorAux dt2 me vs (separate_shared dts param_pos :: rs) os (* recursive *)
      else
      convertConstructorAux dt2 me vs rs (DTyCtr (c , dts) :: os) (* nonrecursive *)
    | DArrow (t, dt2) -> convertConstructorAux dt2 me vs rs (t :: os) (* Parse an argument of any form, definitely nonrecursive *)
    | _ -> failwith ("in convertConstructor, constructor contains unsupported thing: " ^ dep_type_to_string ctr)
    (* | DNot dt -> 
    | DTyParam tp -> 
    | DCtr (c, dts) ->
    | DTyVar v -> 
    | DApp (dt, dts) ->
    | DHole ->  *)
  in
  convertConstructorAux ctr me [] [] []

let convertBack (me : ty_ctr) ((vs , rs , os , outs) : ctr_data) (param_pos : int) : dep_type =
    let rec convertVars vs ty : dep_type =
      match vs with
      | [] -> ty
      | (v :: vs) -> convertVars vs (DProd (v , ty))
    in
    let rec convertRecCalls rs ty : dep_type =
      match rs with
      | [] -> ty
      | (r :: rs) -> convertRecCalls rs (DArrow ((DTyCtr (me , replace_shared r param_pos)), ty))
    in
    let rec convertOtherCalls os ty : dep_type =
      match os with
      | [] -> ty
      | (t :: os) -> convertOtherCalls os (DArrow (t, ty))
    in
    convertVars vs (convertRecCalls rs (convertOtherCalls os (DTyCtr (me, replace_shared outs param_pos))))

(*Is this how you make a (Map var dep_type) in ocaml?*)
module IdMap = Map.Make(UnknownOrd)
type sub = dep_type IdMap.t

let rec sub_term (s : sub) (t : dep_type) : dep_type =
  match t with
  | DTyCtr (tc, dts) -> DTyCtr (tc, List.map (sub_term s) dts)
  | DArrow (dt1, dt2) -> DArrow (sub_term s dt1, sub_term s dt2)
  | DProd  ((v, dt1), dt2) -> DProd ((v , sub_term s dt1), sub_term s dt2)
  | DTyParam tp -> DTyParam tp
  | DCtr (c, dts) -> DCtr (c, List.map (sub_term s) dts)
  | DTyVar v -> (match IdMap.find_opt v s with
                | None -> DTyVar v
                | Some t -> t)
  | DApp (dt, dts) -> DApp (sub_term s dt, List.map (sub_term s) dts)
  | DNot dt -> DNot (sub_term s dt)
  | DHole -> DHole

let compose_sub  (sub1 : sub) (sub2 : sub) : sub =
    IdMap.union (fun _ _ _ -> failwith "shouldn't get here") (IdMap.map (sub_term sub1) sub2) sub1

let rec occurs (v : var) (t : dep_type) : bool =
  match t with
  | DTyCtr (tc, dts) -> List.exists (occurs v) dts
  | DArrow (dt1, dt2) -> occurs v dt1 || occurs v dt2
  | DProd  ((v, dt1), dt2) -> occurs v dt1 || occurs v dt2
  | DTyParam tp -> false
  | DCtr (c, dts) -> List.exists (occurs v) dts
  | DTyVar v' -> v = v'
  | DApp (dt, dts) -> occurs v dt || (List.exists (occurs v) dts)
  | DNot dt -> occurs v dt
  | DHole -> false

(*merge_disjoint from stackoverflow:*)
let merge_disjoint m1 m2 = 
  IdMap.merge 
    (fun k x0 y0 -> 
       match x0, y0 with 
         None, None -> None
       | None, Some v | Some v, None -> Some v
       | _, _ -> invalid_arg "merge_disjoint: maps are not disjoint")
    m1 m2

let rec unify (t1 : dep_type) (t2 : dep_type) : sub option =
  match t1, t2 with
  | DTyVar v, _ -> if t2 = DTyVar v then Some IdMap.empty else if occurs v t2 then None else Some (IdMap.singleton v t2)
  | t, DTyVar v -> unify (DTyVar v) t
  | DTyCtr (tc, dts), DTyCtr (tc', dts') -> if tc = tc' then unifys dts dts' else None
  | DArrow (dt1, dt2), DArrow (dt1', dt2') ->
      Option.bind (unify dt1 dt1') (fun sub1 ->
      Option.bind (unify (sub_term sub1 dt2) (sub_term sub1 dt2')) (fun sub2 ->
      Some (compose_sub sub1 sub2)))
  | DProd  ((v, dt1), dt2), DProd ((v', dt1'), dt2') ->
      Option.bind (unify dt1 dt1') (fun sub1 ->
      Option.bind (unify (sub_term sub1 dt2) (sub_term sub1 dt2')) (fun sub2 ->
      Some (compose_sub sub1 sub2)))
  | DTyParam tp, DTyParam tp' -> Some IdMap.empty
  | DCtr (c, dts), DCtr (c', dts') -> if not (constructor_to_string c = constructor_to_string c') then None
      else unifys dts dts'
  | DApp (dt, dts), DApp (dt', dts') -> 
      Option.bind (unify dt dt') (fun sub1 ->
      Option.bind (unifys (List.map (sub_term sub1) dts) (List.map (sub_term sub1) dts')) (fun sub2 ->
      Some (compose_sub sub1 sub2)))
  | DNot dt, DNot dt' -> unify dt dt'
  | DHole, DHole -> Some IdMap.empty
  | _, _ -> None

and unifys (t1s : dep_type list) (t2s : dep_type list) : sub option =
      match t1s, t2s with
      | [], [] -> Some IdMap.empty
      | (t1 :: t1s), (t2 :: t2s) -> 
        Option.bind (unify t1 t2) (fun s ->
          Option.bind (unifys (List.map (sub_term s) t1s) (List.map (sub_term s) t2s)) (fun s2 ->
          Some (merge_disjoint s s2)))
      | _, _ -> failwith "error, shouldn't get here!"
(*
For now, I'll just assume that the shared parameter is the last parameter.
Later, I'll figure out how to actually get that input from the command.
   *)

(* TODO: move the type to be used in def of ctr_data *)
(* If a is in l, returns l with a removed *)
let rec remove (l : rec_arg list) (shared_param_match : dep_type) : (rec_arg * rec_arg list) option =
  match l with
  | [] -> None
  | ((params, shared_param) :: xs) -> if shared_param = shared_param_match
      then Some ((params, shared_param) , xs)
      else Option.bind (remove xs shared_param_match) (fun (arg, l) -> Some (arg, ((params, shared_param) :: l)))

(* Inputs two sets of recursive arguments, and outputs three lists of arguments:
   combined arguments, arguments from 1 which were unmatched, and arguments from
   2 which were unmatched respectively.*)
  
let merge_recs (rs1 : rec_arg list) (rs2 : rec_arg list)
  : (rec_arg list * rec_arg list * rec_arg list) =
  List.fold_left (fun (both, just1, rs2) (params1, shared_1) ->
    match remove rs2 shared_1 with
    | None -> (both, (params1, shared_1) :: just1, rs2)
    | Some ((params2, _), rs2') -> ((params1 @ params2, shared_1) :: both, just1, rs2')
    )
    ([],[], rs2) rs1

(*returns a renaming for variables in vs2 which maps to names distinct from names in vs1*)
let generate_distinct_names (vs1 : (var * dep_type) list) (vs2 : (var * dep_type) list)
  : var IdMap.t =
  let names = List.map (fun (v, _) -> var_to_string v) vs1 in
  let rec name_starting_with (s : string) : string =
    if List.mem s names then name_starting_with (s ^ "'") else s
  in
  (* List.map (fun (v, ty) -> (inject_var (name_starting_with (var_to_string v)), ty)) vs2 *)
  let pairs = List.map (fun (v, ty) -> (v, inject_var (name_starting_with (var_to_string v)))) vs2 in
  IdMap.of_seq (List.to_seq pairs)
  
let merge_ctrs (name1 : ty_ctr) (name2 : ty_ctr) (vs1, rs1, os1, (as1, t1) : ctr_data)
  (vs2, rs2, os2, (as2, t2) : ctr_data)
  (param_pos1 : int) (param_pos2 : int)
  : ctr_data option =
  (* Get a renaming for variables in vs2. vs1 and vs2 should already be unique within themselves, but we can't
     have names clash between them. *)
  let var_renaming = generate_distinct_names vs1 vs2 in
  let ren = fun v -> IdMap.find v var_renaming in
  let var_sub = IdMap.map (fun t -> DTyVar t) var_renaming in
  (* apply variable renaming to everything from second relation *)
  let vs2 = List.map (fun (v, t) -> (ren v, t)) vs2 in
  let rs2 = List.map (fun (params, shared_param) -> (List.map (sub_term var_sub) params, sub_term var_sub shared_param)) rs2 in
  let os2 = List.map (sub_term var_sub) os2 in
  let as2 = List.map (sub_term var_sub) as2 in
  let t2 = sub_term var_sub t2 in
  (* split output parameters into shared value and others *)
  (* Check if shared parameter of both constructors unify *)
  Option.bind (unify t1 t2) (fun sub ->
    (* In the case where they do unify, apply the resulting substitution to everything: *)
    let s = sub_term sub in
    let rs1' = List.map (fun (params, sh_param) -> (List.map s params, s sh_param)) rs1 in
    let rs2' = List.map (fun (params, sh_param) -> (List.map s params, s sh_param)) rs2 in
    let os1' = List.map s os1 in
    let os2' = List.map s os2 in
    (* Build the pieces of the resulting constructor by combining pieces from the two input constructors: *)
    let t = s t1 in (*this should be equal to s t2*)
    let as_ = List.append (List.map s as1) (List.map s as2) in
    (* Any recursive arguments which match up should be combined, and other should be left as is: *)
    let (rs, more_os1, more_os2) = merge_recs rs1' rs2' in
    (* Collect the other non-recursive arguments: *)
    let os = os1' @ os2' @ (List.map (fun args -> DTyCtr (name1, replace_shared args param_pos1)) more_os1)
      @ (List.map (fun args -> DTyCtr (name2, replace_shared args param_pos2)) more_os2) in
    (* Collect new list of forall bound variables, which is the union of the lists of the inputs except with variables
       which got substituted during unification removed *)
    let was_subbed = fun v -> not (IdMap.mem v sub) in
    let vs = List.filter (fun (v, _) -> was_subbed v) vs1 @ List.filter (fun (v, _) -> was_subbed v) vs2 in
    Some (vs, rs, os, (as_, t))
  )

(*Note: I need to deal with if two constructors happen to have a forall bound variable
   of the same name.*)

let rec convert_type (ty : dep_type) : dep_type list =
  match ty with
  | DArrow (a, b) -> a :: convert_type b
  | out -> []

let rec convert_type_back (params : dep_type list) : dep_type =
  match params with 
  | [] -> DTyCtr (gInjectTyCtr "Prop", [])
  | param :: params -> DArrow (param, convert_type_back params)

type relation = (ty_ctr * ty_param list * dep_ctr list * dep_type)

let range (n : int) : int list =
  let rec range_aux (n : int) (so_far : int list) : int list =
    if n = 0 then so_far else range_aux (n - 1) (n :: so_far)
  in range_aux n []

(* inputs constructors from one type, and two parameters which tell it how to position the parameters in the output
   type: other_type_num_params is how many parameters the other type to be merged with has, and left_or_right
   is false if this type's params go on the left, or true if they go on the right.
   Outputs (unchanged constructors, irrelevant constructors adjusted for output type)*)
let rec irrelevant_constructor_pass (ctrs : (GenericLib.constructor * ctr_data) list) (other_type_params : dep_type list) (left_or_right : bool)
  : ((GenericLib.constructor * ctr_data) list * (GenericLib.constructor * ctr_data) list) =
  let ctr_irrelevant_try ((vs, rs, os, (params_out, shared_out)) : ctr_data) : ctr_data option =
    if List.length rs = 1
      then let (r_params, r_shared) = List.nth rs 0 in
        if r_shared = shared_out
          then let new_vars = List.map (fun s -> inject_var ("x_generated_" ^ string_of_int s))
                (range (List.length other_type_params)) in
              let new_vars_terms = List.map (fun v -> DTyVar v) new_vars in
              let new_r_params = if left_or_right then new_vars_terms @ r_params else r_params @ new_vars_terms in
              let new_params_out = if left_or_right then new_vars_terms @ params_out else params_out @ new_vars_terms in
              Some (vs @ (List.combine new_vars other_type_params),
                [ new_r_params, r_shared ],
                os,
                (new_params_out, shared_out))
          else None
      else None
  in
  match ctrs with
  | [] -> ([], [])
  | ((name, ctr) :: rest) ->
    let (normal, irrelevant) = irrelevant_constructor_pass rest other_type_params left_or_right in
    match ctr_irrelevant_try ctr with
    | None -> ((name, ctr) :: normal, irrelevant)
    | Some out_ctr -> (normal, (injectCtr ((constructor_to_string name) ^ "'"), out_ctr) :: irrelevant)
let merge_relations ((tyctr1, params1, ctrs1, ty1) : relation)
                    (param_pos1 : int)
                    ((tyctr2, params2, ctrs2, ty2) : relation)
                    (param_pos2 : int)
                    tyctr
  : relation =
  let params = params1 @ params2 in
  let converted_ty1 = separate_shared (convert_type ty1) param_pos1 in
  let converted_ty2 = separate_shared (convert_type ty2) param_pos2 in
  let ty = (convert_type_back ((fst converted_ty1) @ (fst converted_ty2) @ [ snd converted_ty1 ])) in
  let (ctrs1_regular, ctrs1_irrelevant) = irrelevant_constructor_pass
    (List.map (fun (name, ctr) -> (name, convertConstructor tyctr1 ctr param_pos1)) ctrs1)
    (fst converted_ty2) false in
  let (ctrs2_regular, ctrs2_irrelevant) = irrelevant_constructor_pass
    (List.map (fun (name, ctr) -> (name, convertConstructor tyctr2 ctr param_pos2)) ctrs2)
    (fst converted_ty1) true in
  let param_pos = (List.length (convert_type ty) - 1) in
  let ctrs_regular = List.fold_left (fun acc (name1, ctr1) -> (List.fold_left (fun acc (name2, ctr2) -> 
    match merge_ctrs tyctr1 tyctr2 ctr1 ctr2 param_pos1 param_pos2 with
    | Some ctr -> let new_ctr = convertBack tyctr ctr param_pos in (*TODO: think here later*)
        let new_name = (injectCtr (constructor_to_string name1 ^ constructor_to_string name2)) in
        (new_name, new_ctr) :: acc
    | None -> acc
    ) acc ctrs2_regular)) [] ctrs1_regular in
  let ctrs = (List.map (fun (name, ctr) -> (name, convertBack tyctr ctr param_pos)) ctrs1_irrelevant)
    @ (List.map (fun (name, ctr) -> (name, convertBack tyctr ctr param_pos)) ctrs2_irrelevant) 
    @ ctrs_regular in
  (tyctr, params, ctrs, ty)

let extract_relation ind : relation * int =
  match ind with 
  | { CAst.v = CLambdaN ([CLocalAssum ([{ CAst.v = Names.Name id1; CAst.loc = _loc2 }], _kind, _type)], body1); _ } ->
    (* Extract (x1,x2,...) if any, P and arguments *)
    let (p1, args1) =
      match body1 with 
      | { CAst.v = CApp (p, args); _ } -> (p, args)
      | _ -> qcfail "Merge/Not App"
    in     
    let rec find f lst = (*from stackoverflow*)
    match lst with
    | [] -> raise (failwith "Parameter bound parameter not in argument list")
    | h :: t -> if f h then 0 else 1 + find f t in
    (* Find position of id1 in args1 to get parameter position *)
    let param_pos = find (function | ({CAst.v = CRef (id,_) ; _} , _) -> qualid_basename id = id1) args1 in
    match coerce_reference_to_dep_dt p1 with
    | Some dt -> msg_debug (str (dep_dt_to_string dt) ++ fnl());
        let num_named_params = match dt with (_ , params , _ , _) -> List.length params in
        dt , param_pos - num_named_params
    | None -> failwith "Not supported type"

let extract_tyctr ind : ty_ctr =
  match ind with 
  | { CAst.v =  CRef (r,_) ; _ } -> gInjectTyCtr (string_of_qualid r)

let merge ind1 ind2 ind = 
  let rel1, param_pos1 = extract_relation ind1 in
  let rel2, param_pos2 = extract_relation ind2 in
  let rel = merge_relations rel1 param_pos1 rel2 param_pos2 (extract_tyctr ind) in
  (* failwith ("relation is: \n" ^ (dep_dt_to_string rel)) *)
  define_new_inductive rel

(*

TODO still:
4) Generate the mappings back and forth P as x /\ Q bs x <-> PQ as bs x
7) find out why stdlib le doesn't work
8) Add error checks with useful error messages for
  - shared parameter types are different
  - number of arguments is not same as number that the type family actually takes
   
*)
