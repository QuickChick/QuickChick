open Pp
open Util
open GenericLib
open Error

(* TODO : move to utils or smth *)
type name_provider = { next_name : unit -> string }

let mk_name_provider s = 
  let cnt = ref 0 in
  { next_name = fun () -> 
      let res = Printf.sprintf "%s_%d_" s !cnt in
      incr cnt;
      res
  }

(* Ranges are undefined, unknowns or constructors applied to ranges *)
module Unknown = struct
  type t = var

  let to_string = var_to_string
  let from_string x = fresh_name x
  let from_var x = x
  let from_id x = var_of_id x                 

  let undefined = fresh_name "Ireallywantundefinedherebutwedonthavelaziness"

end

module UnknownOrd = struct
  type t = Unknown.t
  let compare x y = compare (Unknown.to_string x) (Unknown.to_string y)
end

type unknown = Unknown.t

type range = Ctr of constructor * range list
           | Unknown of unknown
           | Undef of dep_type
           | FixedInput
           | Parameter of ty_param
           | RangeHole

let is_parameter r =
  match r with
  | Parameter _ -> true
  | _ -> false
           
let rec range_to_string = function
  | Ctr (c, rs) -> constructor_to_string c ^ " " ^ str_lst_to_string " " (List.map range_to_string rs)
  | Unknown u -> Unknown.to_string u
  | Undef dt -> Printf.sprintf "Undef (%s)" (dep_type_to_string dt)
  | FixedInput -> "FixedInput"
  | RangeHole  -> "_"
  | Parameter p -> ty_param_to_string p

let ranges_to_string rs = String.concat " " (List.map range_to_string rs)

let rec matcher_pat_to_range m =
  match m with
  | MatchCtr (c,ms) -> Ctr (c, List.map matcher_pat_to_range ms)
  | MatchU u -> Unknown u
  | MatchParameter p -> Parameter p

module UM = Map.Make(UnknownOrd)
(* module US = Set.Make(UnknownOrd) *)
          
(* Maps unknowns to range *)
type umap = range UM.t

let umfind k m = 
  try UM.find k m 
  with Not_found ->
    CErrors.user_err (str (Printf.sprintf "Can't find: %s" (Unknown.to_string k)) ++ fnl())

let lookup (k : unknown) (m : umap) = try Some (UM.find k m) with Not_found -> None

(* For equality handling: require ordered (String, String) *)
module OrdTSS = struct 
  type t = unknown * unknown
  let compare x y = compare x y
end

module EqSet = Set.Make(OrdTSS)

let eq_set_add u1 u2 eqs = 
  let (u1', u2') = if u1 < u2 then (u1, u2) else (u2, u1) in
  EqSet.add (u1', u2') eqs

module OrdTyp = struct 
  type t = dep_type
  let compare = compare
end

module ArbSet = Set.Make(OrdTyp)

type unknown_provider = { next_unknown : unit -> Unknown.t }

let unk_provider = 
  let np = mk_name_provider "unkn" in
  { next_unknown = fun () -> Unknown.from_string (np.next_name ()) }


(* Match a constructor/ranges list to a fixed input *)
(* Range list is toplevel, so it's mostly unifications.
   If any of the unknowns in rs is "FixedInput", then 
   we need to create a fresh unknown, bind it to the other unknown and 
   raise an equality check *)
let rec raiseMatch (k : umap) (c : constructor) (rs : range list) (eqs: EqSet.t) 
        : (umap * matcher_pat * EqSet.t) option = 
  (foldM (fun (k, l, eqs) r ->
         match r with 
         | Ctr (c', rs') ->
            raiseMatch k c' rs' eqs >>= fun (k', m, eqs') ->
            Some (k', m::l, eqs')
         | Unknown u ->
            let rec go u = 
              lookup u k >>= fun r' ->
              begin match r' with 
              | Undef _ -> (* The unknown should now be fixed *)
                 Some (UM.add u FixedInput k, (MatchU u)::l, eqs)
              | FixedInput -> (* The unknown is already fixed, raise an eq check *)
                 let u' = unk_provider.next_unknown () in
                 Some (UM.add u' (Unknown u) k, (MatchU u')::l, eq_set_add u' u eqs)
              | Ctr (c', rs') ->
                 raiseMatch k c' rs' eqs >>= fun (k', m, eqs') ->
                 Some (k', m :: l, eqs')
              | Unknown u' -> go u'
              | RangeHole -> failwith "Internal: RangeHoles should not appear past entry"
              | Parameter _p -> failwith "QC Internal: Does this occur (Parameter in match)?"
              end
            in go u
         | Parameter p -> Some (k, MatchParameter p :: l, eqs)
         | _ -> failwith "Toplevel ranges should be Unknowns or constructors"
        ) (Some (k, [], eqs)) rs) >>= fun (k', l, eqs') ->
  Some (k', MatchCtr (c, List.rev l), eqs')

(* Invariants: 
   -- Everything has a binding, even if just Undef 
   -- r1, r2 are never FixedInput, Undef (handled inline)
   -- TopLevel ranges can be unknowns or constructors applied to toplevel ranges
   -- Constructor bindings in umaps are also toplevel. 
   -- Only unknowns can be bound to Undef/FixedInput
*)
let rec unify (k : umap) (r1 : range) (r2 : range) (eqs : EqSet.t)
        : (umap * range * EqSet.t * (unknown * matcher_pat) list) option =
  msg_debug (str (Printf.sprintf "Calling unify with %s %s" (range_to_string r1) (range_to_string r2)) ++ fnl ());
  match r1, r2 with
  | Unknown u1, Unknown u2 ->
     if u1 = u2 then Some (k, Unknown u1, eqs, []) else
     lookup u1 k >>= fun r1 -> 
     lookup u2 k >>= fun r2 ->
     msg_debug (str (Printf.sprintf "Unifying two unknowns with ranges: %s %s" (range_to_string r1) (range_to_string r2)) ++ fnl ());
     begin match r1, r2 with 
     (* "Delay" cases - unknowns call unify again *)
     (* TODO: rething return value *)
     | Unknown u1', _ -> 
        unify k (Unknown u1') (Unknown u2) eqs >>= fun (k', _r', eqs', ms') ->
        Some (k', Unknown u1, eqs', ms')
     | _, Unknown u2' ->
        unify k (Unknown u1) (Unknown u2') eqs >>= fun (k', _r', eqs', ms') ->
        Some (k', Unknown u2, eqs', ms')

     (* "Hard" case: both are fixed. Need to raise an equality check on the inputs *)
     | FixedInput, FixedInput -> 
        let (u1', u2') = if u1 < u2 then (u1, u2) else (u2, u1) in
        (* Need to insert an equality between u1 and u2 *)
        let eqs' = EqSet.add (u1, u2) eqs in 
        (* Unify them in k *)
        Some (UM.add u1' (Unknown u2') k, Unknown u1', eqs', [])

     (* Easy cases: When at least one is undefined, it binds to the other *)
     (* Can probably replace fixed input with _ *)
     | Undef _ , Undef _ ->
        let (u1', u2') = if u1 < u2 then (u1, u2) else (u2, u1) in
        Some (UM.add u1' (Unknown u2') k, Unknown u1', eqs, [])
     | _, Undef _ ->
        Some (UM.add u2 (Unknown u1) k, Unknown u2, eqs, [])
     | Undef _, _ ->
        Some (UM.add u1 (Unknown u2) k, Unknown u1, eqs, [])

     (* Constructor bindings *) 
     | Ctr (c1, rs1), Ctr (c2, rs2) ->
        msg_debug (str (Printf.sprintf "Constructors: %s - %s\n"
                                         (String.concat " " (List.map range_to_string rs1))
                                         (String.concat " " (List.map range_to_string rs2)))
                         ++ fnl ());
        if c1 = c2 then 
          foldM (fun b a -> let (r1, r2) = a in 
                            let (k, l, eqs, ms) = b in 
                            unify k r1 r2 eqs >>= fun res ->
                            let (k', r', eqs', ms') = res in 
                            Some (k', r'::l, eqs', ms @ ms')
                ) (Some (k, [], eqs, [])) (List.combine rs1 rs2) >>= fun (k', rs', eqs', ms) ->
          Some (k', Ctr (c1, List.rev rs'), eqs', ms)
        else None

     (* Last hard cases: Constructors vs fixed *) 
     | FixedInput, Ctr (c, rs) ->
        (* Raises a match and potential equalities *)
        raiseMatch k c rs eqs >>= fun (k', m, eqs') ->
        Some (UM.add u1 (Unknown u2) k', Unknown u1, eqs', [(u1, m)])
     | Ctr (c, rs), FixedInput ->
        (* Raises a match and potential equalities *)
        raiseMatch k c rs eqs >>= fun (k', m, eqs') ->
        Some (UM.add u2 (Unknown u1) k', Unknown u2, eqs', [(u2, m)])
     | Parameter p, Parameter q ->
        if p = q then Some (k, Parameter p, eqs, []) else None
     | _ -> failwith "QC Internal: RangeHole/Parameter in unify"
     end
   | Ctr (c1, rs1), Ctr (c2, rs2) ->
        msg_debug (str (Printf.sprintf "Constructors2: %s - %s\n"
                                         (String.concat " " (List.map range_to_string rs1))
                                         (String.concat " " (List.map range_to_string rs2)))
                         ++ fnl ());
      if c1 = c2 then 
        foldM (fun b a -> let (r1, r2) = a in 
                          let (k, l, eqs, ms) = b in 
                          unify k r1 r2 eqs >>= fun res ->
                          let (k', r', eqs', ms') = res in 
                          Some (k', r'::l, eqs', ms @ ms')
              ) (Some (k, [], eqs, [])) (List.combine rs1 rs2) >>= fun (k', rs', eqs', ms) ->
        Some (k', Ctr (c1, List.rev rs'), eqs', ms)
      else None
   | Unknown u, Ctr (c, rs) 
   | Ctr (c, rs), Unknown u ->
      lookup u k >>= fun r ->
      begin match r with 
      | FixedInput -> 
        (* Raises a match and potential equalities *)
        raiseMatch k c rs eqs >>= fun (k', m, eqs') ->
        Some (UM.add u (Ctr (c,rs)) k', Unknown u, eqs', [(u, m)])
      | Undef _ -> Some (UM.add u (Ctr (c,rs)) k, Unknown u, eqs, [])
      | Ctr (c', rs') -> 
        msg_debug (str (Printf.sprintf "Constructors3: %s \n"
                                         (String.concat " " (List.map range_to_string rs')))
                         ++ fnl ());
        if c = c' then 
          foldM (fun b a -> let (r1, r2) = a in 
                            let (k, l, eqs, ms) = b in 
                            unify k r1 r2 eqs >>= fun res ->
                            let (k', r', eqs', ms') = res in 
                            Some (k', r'::l, eqs', ms @ ms')
                ) (Some (k, [], eqs, [])) (List.combine rs rs') >>= fun (k', _rs', eqs', ms) ->
          Some (k', Unknown u, eqs', ms)
        else None
      | Unknown u' -> 
         unify k (Ctr (c,rs)) (Unknown u') eqs >>= fun (k', _r', eqs', m') ->
         Some (k', Unknown u, eqs', m')
      | _ -> failwith "QC Internal: Range Hole in toplevel?"
      end
   | Parameter p, Parameter q ->
      if p = q then Some (k, Parameter p, eqs, []) else None
   | _, _ -> failwith "QC Internal: TopLevel ranges should be Unknowns or Constructors"

let rec fixRange u r k = 
    match r with 
    | FixedInput -> k
    | Undef _ -> UM.add u FixedInput k 
    | Unknown u' ->
       begin
         try fixRange u' (UM.find u' k) k
         with Not_found -> UM.add u' FixedInput k
       end
    | Ctr (_, rs) -> List.fold_left (fun k r -> fixRange Unknown.undefined r k) k rs
    | Parameter _p -> k
    | RangeHole -> failwith "QC Internal: RangeHole in fixrange"

let fixVariable x k =
  try fixRange x (UM.find x k) k
  with Not_found -> UM.add x FixedInput k

(* Since this can fail - return an option *)
let rec convert_to_range dt = 
  match dt with 
  | DTyVar x -> Some (Unknown x)
  | DCtr (c,dts) ->
     option_map (fun dts' -> Ctr (c, dts')) (sequenceM convert_to_range dts)
  | DTyCtr (c, dts) -> 
     option_map (fun dts' -> Ctr (ty_ctr_to_ctr c, dts')) (sequenceM convert_to_range dts)
  | DTyParam param -> Some (Parameter param)
  | DHole -> Some RangeHole
  | _ -> None

let rec is_fixed_range k = function
    | Undef _ -> false
    | FixedInput -> true
    | Unknown u' -> is_fixed_range k (umfind u' k)
    | Ctr (_, rs) -> List.for_all (is_fixed_range k) rs
    | RangeHole -> true (*TODO *)
    | Parameter _ -> true (* TODO *)
       
let is_fixed k dt = 
  option_map (is_fixed_range k) (convert_to_range dt)

(* convert a range to a coq expression *)
let rec range_to_coq_expr k r = 
  match r with 
  | Ctr (c, rs) -> 
     gApp ~explicit:true (gCtr c) (List.map (range_to_coq_expr k) rs)
  | Unknown u -> 
     begin match umfind u k with
     | FixedInput -> gVar u
     | Undef _ -> (msg_debug (str "It's stupid that this is called" ++ fnl ()); gVar u)
     | Unknown u' -> range_to_coq_expr k (Unknown u')
     | Ctr (c, rs) -> gApp (gCtr c) (List.map (range_to_coq_expr k) rs)
     | Parameter p -> gTyParam p
     | RangeHole -> hole
     end
  | RangeHole -> hole
  | Parameter p -> gTyParam p
  | _ -> failwith "QC Internal: TopLevel ranges should be Unknowns or Constructors"

let rec dt_to_coq_expr k dt =
  match dt with
  | DTyVar u ->
     begin try 
       begin match umfind u k with
       | FixedInput -> gVar u
       | Undef _ -> (msg_debug (str "It's stupid that this is called" ++ fnl ()); gVar u)
       | Unknown u' -> range_to_coq_expr k (Unknown u')
       | Ctr (c, rs) -> gApp (gCtr c) (List.map (range_to_coq_expr k) rs)
       | Parameter p -> gTyParam p
       | RangeHole -> hole
       end
       with _ -> gVar u
     end
  | DCtr (c,dts) ->
     gApp ~explicit:true (gCtr c) (List.map (dt_to_coq_expr k) dts)     
  | DTyCtr (c, dts) ->
     gApp ~explicit:true (gCtr (ty_ctr_to_ctr c)) (List.map (dt_to_coq_expr k) dts)     
  | DApp (dt, dts) ->
     gApp ~explicit:true (dt_to_coq_expr k dt) (List.map (dt_to_coq_expr k) dts)
  | DHole -> hole
  | _ -> failwith "QC Internal: dt_to_coq_expr"
  
let rec is_dep_type = function
  | DArrow (dt1, dt2) -> is_dep_type dt1 || is_dep_type dt2 
  | DProd ((_, dt1), dt2) -> is_dep_type dt1 || is_dep_type dt2 
  | DTyParam _ -> false
  | DTyVar _ -> true
  | DCtr _ -> true
  | DTyCtr (_, dts) -> List.exists is_dep_type dts
  | DApp (dt, dts) -> List.exists is_dep_type (dt::dts)
  | DNot dt -> is_dep_type dt
  | DHole -> false

type check = (coq_expr -> coq_expr) * int

module CMap = Map.Make(OrdDepType)
type cmap = (check list) CMap.t

let lookup_checks k m = try Some (CMap.find k m) with Not_found -> None

(* TODO: When handling parameters, this might need to add additional arguments *)
(** Takes an equality map and two coq expressions [cleft] and [cright]. [cleft]
    is returned if all of the equalities hold, otherwise [cright] is
    returned. *)
let handle_equalities init_size eqs (check_expr : coq_expr -> 'a -> 'a -> 'a -> 'a)
      (cleft : 'a) (cright : 'a) (cfuel : 'a) = 
  EqSet.fold (fun (u1,u2) c -> 
               let checker =
                 gApp ~explicit:true (gInject "decOpt")
                   [ gApp (gInject "Logic.eq") [gVar u1; gVar u2]
                   ; hole
                   ; init_size]
               in
               check_expr checker c cright cfuel
             ) eqs cleft

type mode = Recursive of (Unknown.t * dep_type) list
                       * (Unknown.t * dep_type) list
                       * range list
          | NonRecursive of (Unknown.t * dep_type) list (* List of all unknowns that are still undefined *)

type range_mode =
  | ModeFixed
  | ModeUndefUnknown of (Unknown.t * dep_type)
  | ModePartlyDef of ((Unknown.t * Unknown.t) list * (Unknown.t * dep_type) list * matcher_pat)
  | ModeParameter

let range_mode_to_string = function
  | ModeFixed -> "Fixed"
  | ModeParameter -> "Param"
  | ModeUndefUnknown (u,_) -> Printf.sprintf "Unknown %s" (Unknown.to_string u)
  | ModePartlyDef (eqs, unks, pat) ->
     Printf.sprintf "Partial (eqs = %s, unks = %s, pat = %s)"
       (String.concat " " (List.map (fun (u1, u2) -> Printf.sprintf "%s = %s" (Unknown.to_string u1) (Unknown.to_string u2)) eqs))
       (String.concat " " (List.map (fun (u,t) -> Unknown.to_string u) unks))
       (matcher_pat_to_string pat)
                   
type compatible = Compatible | Incompatible | PartCompatible | InstCompatible

exception Incompatible_mode
                                                             
let mode_analysis init_ctr curr_ctr (init_ranges : range list) (init_map : range UM.t)
      (curr_ranges : range list) (curr_map : range UM.t) =
  msg_debug (str (Printf.sprintf "Look here!! init_ctr = %s, curr_ctr = %s" (ty_ctr_to_string init_ctr) (ty_ctr_to_string curr_ctr)) ++ fnl ());
  ignore (find_typeclass_bindings "EnumSizedSuchThat" curr_ctr);
  let unknowns_for_mode  = ref [] in
  let remaining_unknowns = ref [] in
  let all_unknowns = ref [] in
  let actual_inputs = ref [] in

  (* Filter out parameters ranges -- hack! *)
  let init_ranges = List.filter (fun r -> not (is_parameter r)) init_ranges in
  let curr_ranges = List.filter (fun r -> not (is_parameter r)) curr_ranges in
  
  (* Compare ranges takes two ranges (the initial range r1 and the current range r2)
     as well as their parents, and returns:
     - true, if we can convert the current range to the same
       mode as the original range by instantiating a list of unknowns
     - false, if we can not convert (i.e. some things are more instantiated 
       than they should be)
   *)
  let rec compare_ranges isTop p1 r1 p2 r2 =
    match r1, r2 with
    | Unknown u1, _ -> compare_ranges isTop u1 (UM.find u1 init_map) p2 r2
    | _, Unknown u2 -> compare_ranges isTop p1 r1 u2 (UM.find u2 curr_map)
    | FixedInput, FixedInput ->
       if isTop then actual_inputs := Unknown p2 :: !actual_inputs;
       true
    | FixedInput, Undef dt   ->
       if isTop then actual_inputs := Unknown p2 :: !actual_inputs; 
       unknowns_for_mode := (p2, dt) :: !unknowns_for_mode;
       all_unknowns := (p2, dt) :: !all_unknowns;
       true
    | FixedInput, Ctr (c, rs) ->
       if isTop then actual_inputs := (Ctr (c,rs)) :: !actual_inputs; 
       (* iterate through all the rs against fixed inputs *)
       List.for_all (fun b -> b) (List.map (compare_ranges false Unknown.undefined FixedInput Unknown.undefined) rs)
    | Undef _, FixedInput ->
       (* todo: something is wrong here *)
       false
    | Undef _, Undef dt    ->
       (* Add the second range's parent to the list of unknowns that are free, 
          but do not need to be instantiated for the mode to work *)
       remaining_unknowns := (p2,dt) :: !remaining_unknowns;
       all_unknowns := (p2, dt) :: !all_unknowns;
       true
    | Undef _, Ctr (_c, rs) ->
       List.iter (fun r' -> ignore (compare_ranges false p1 r1 Unknown.undefined r')) rs; false
    | _, _ -> qcfail (Printf.sprintf "Implement constructors for initial ranges: %s vs %s"
                           (range_to_string r1) (range_to_string r2))
  in
  if not (init_ctr = curr_ctr) then
    let rec find_all_unknowns p r =
      match r with
      | Unknown u  -> find_all_unknowns u (UM.find u curr_map)
      | FixedInput -> ()
      | Undef dt -> all_unknowns := (p, dt) :: !all_unknowns
      | Ctr (_c, rs) -> List.iter (find_all_unknowns Unknown.undefined) rs
      | RangeHole -> ()
      | Parameter _ -> ()
    in (List.iter (find_all_unknowns Unknown.undefined) curr_ranges;
        msg_debug (str "Mismatched constructors in mode analysis" ++ fnl ());
        NonRecursive !all_unknowns)
  else if List.for_all (fun b -> b) (List.map2 (fun r1 r2 -> compare_ranges true Unknown.undefined r1 Unknown.undefined r2) init_ranges curr_ranges) 
  then Recursive (List.rev !unknowns_for_mode, List.rev !remaining_unknowns, List.rev !actual_inputs)
  else NonRecursive !all_unknowns

let isTyParam = function
  | DTyParam _ -> true
  | _ -> false 

let warn_uninstantiated_variables =
  CWarnings.create ~name:"quickchick-uninstantiated-variables"
    ~category:"quickchick"
    ~default:CWarnings.Enabled
    (fun allUnknowns ->
      str "After proccessing all constraints, there are still uninstantiated variables: "
      ++ prlist_with_sep (fun _ -> strbrk " , ") str (List.map var_to_string allUnknowns)
      ++ str ". Proceeding with caution..."
      ++ fnl ())
       
let handle_branch
      (type a) (type b) (* I've started to love ocaml again because of this *)
      (prod_class_names : string list)
      (_dep_type : dep_type)
      (init_size : coq_expr)
      (fail_exp : b)
      (not_enough_fuel_exp : b)
      (ret_exp : coq_expr -> b)
      (instantiate_existential_method : a)
      (instantiate_existential_methodST : int -> coq_expr (* pred *) -> a)
      (ex_bind : bool (* opt *) -> a -> string -> (var -> b) -> b)
      (rec_method : int -> unknown list option -> coq_expr list -> a)
      (rec_bind : bool (* opt *) -> a -> string -> (var -> b) -> b)
      (stMaybe : bool (* opt *) -> a -> string -> ((coq_expr -> coq_expr) * int) list -> a)
      (check_expr : int -> coq_expr -> b -> b -> b -> b)
      (match_inp : var -> matcher_pat -> b -> b -> b)
      (let_in_expr : string -> coq_expr -> (var -> b) -> b)
      (let_tuple_in_expr : var -> var list -> b -> b)
      (gen_ctr : ty_ctr)
      (init_umap : range UM.t)
      (init_tmap : dep_type UM.t)
      (input_ranges : range list)
      (result : Unknown.t)
      (c : dep_ctr)
    : (b * bool) =

  (* ************************ *)
  (* Step 0 : Initializations *)
  (* ************************ *)
  
  let (ctr, typ) = c in

  (* Local reference : is this constructor recursive or not? *)
  let is_base = ref true in

  (* Local references to handle map updates. Keep init_umap intact for mode analysis. *)
  let umap = ref init_umap in
  let tmap = ref init_tmap in

  (* Check map - registers necessary checks for variable instantiation *)
  let cmap = ref CMap.empty in
  
  (* Add all universally quantified unknowns in the u/t environments. *)
  let rec register_unknowns = function
      | DArrow (_dt1, dt2) -> register_unknowns dt2
      | DProd ((x, dt1), dt2) ->
         umap := UM.add x (Undef dt1) !umap;
         tmap := UM.add x dt1 !tmap;
         register_unknowns dt2
      | _ -> ()
  in
  register_unknowns typ;

  msg_debug (str "Debug branch" ++ fnl ());
  msg_debug (str ("Calculating ranges: " ^ dep_type_to_string (dep_result_type typ)) ++ fnl ());

  (* !! Possibility of failure: 
     The conclusion of each constructor must not contain function calls.
     
     Possible solution: 
     Automatically transform such constructors to include an additional equality with 
     a fresh unknown? 
   *)
  let result_ranges =
    match dep_result_type typ with
    | DTyCtr (_, dts) as res ->
       begin match sequenceM convert_to_range (List.filter (fun dt -> not (isTyParam dt)) dts) with
       | Some ranges -> ranges
       | None ->
          qcfail (Printf.sprintf "Arguments to result of constructor %s can only be variables or constructors applied to variables: %s" (constructor_to_string ctr) (dep_type_to_string res))
       end
    | res ->
       qcfail (Printf.sprintf "Result type of constructor %s is not a type constructor applied to arguments: %s" (constructor_to_string ctr) (dep_type_to_string res))
  in 

  (* Debugging init map *)
  msg_debug (str ("Handling branch: " ^ dep_type_to_string typ) ++ fnl ());
  UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) !umap;
  dep_fold_ty (fun _ dt1 -> msg_debug (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
    (fun _ _ dt1 -> msg_debug (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
    (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) typ;
  (* End debugging *)

  (* ********************************************* *)  
  (* Step 1: Unify result ranges with input ranges *)
  (* ********************************************* *)

  (* Set of equality checks necessary *)
  let eq_set  = ref EqSet.empty in
  (* List of necessary pattern matches *)
  let matches = ref [] in
  (* Function to handle a single argument *)
  let unify_single_pair r_in r_res =
    match unify !umap r_in r_res !eq_set with
    | Some (umap', _range, eq_set', extra_matches) ->
       (* Unification succeeded; update info *)
       umap := umap';
       eq_set := eq_set';
       matches := extra_matches @ !matches
    | None ->
       (* Unification failed. *)
       qcfail "Matching result type error" (* TODO: Better error message here? *)
  in
  List.iter2 unify_single_pair input_ranges result_ranges;

  msg_debug (str "Unification complete" ++ fnl ());
  
  (* ********************************************************* *)
  (* Interlude: Helper functions to instantiate a single range *)
  (* ********************************************************* *)

  (* Note: These functions should theoretically live outside of this block, but they rely 
     on the parameterized arguments. Move to the front? *)

  (* Note - Existential handling: *)
  (* There is a mismatch between the monads in generation and checking.
     In generation, the main bind is G, the bind opt is G . option.
     In checking, the main function is of type option bool. For instantiating something
     (enumerable?) we need a list-monad bind. Which is to be used whenever we do 
     instantiations. 
     My solution would be to either:
     (a) lift the entire option monad (in the let fix declaration) to a list monad
         and convert back to an option at the end
     (b) decouple the instantiation bind from the call bind.
     Not sure what works better - to be discussed. 
   *) 
  (* Opt = list, not opt = opt *)

  
  (* When instantiating a single unknown, see if it must satisfy any additional predicates. *)
  (* Old comment: Process check map. XXX generator specific *)

  let process_checks bind x opt g (cont : var -> b) : b =
    msg_debug (str ("Processing checks for variable: " ^ (Unknown.to_string x)) ++ fnl ());
    match lookup_checks (DTyVar x) !cmap with
    | Some checks -> 
       (* Remove checks from cmap *)
       msg_debug (str "Actual checks needed" ++ fnl ());
       cmap := CMap.remove (DTyVar x) !cmap;
       umap := fixVariable x !umap;
       bind true
         (stMaybe opt g (var_to_string x) checks)
         (var_to_string x)
         (fun x -> cont x)
    | None ->
       umap := fixVariable x !umap;
       bind opt g (var_to_string x) (fun x -> cont x)
  in

  (* Two mutually recursive functions follow for instantiating ranges. *)
  
  (* Function to instantiate a single range; uses the input check-map for additional checks. 
     Takes a continuation that receives the (instantiated) range to produce a result. *)
  let rec instantiate_range_cont (parent : unknown) r (cont : range -> b) =
    msg_debug (str ("Calling instantiate_range_cont with : " ^ range_to_string r) ++ fnl ());
    match r with 
    | Ctr (c,rs) ->
       (* We need to recursively instantiate all the ranges rs, using the function below *)
       instantiate_toplevel_ranges_cont rs []
         (fun rs' -> cont (Ctr (c, rs')))
    | Undef _dt ->
       (* For undefined, we need to instantiate the parent by processing its checks. *)
         process_checks ex_bind parent false instantiate_existential_method
           (fun x -> cont (Unknown x))
    | Unknown u ->
       (* Unknowns just propagate one step further *)
       instantiate_range_cont u (umfind u !umap) cont
    | FixedInput ->
       (* Just call the continuation on the parent. *)
       cont (Unknown parent)
    | Parameter p -> cont (Parameter p)
    | RangeHole -> cont RangeHole

  (* Function that operates on multiple top-level ranges at once, mapping the above over a list *)
  and instantiate_toplevel_ranges_cont (rs : range list) (acc : range list)
            (cont : range list -> b) : b =
    match rs with
    | r ::rs' ->
       (* For each range r, we need to recursively call instantiate_range with the 
          current umap and cmap, and no defined parent. *)
       instantiate_range_cont Unknown.undefined r
         (* The continuation receives an updated umap', cmap' and a new range res,
            representing the (potentially instantiated) range.
            We then add res to an accumulator list and continue the traversal. *)
         (fun res -> instantiate_toplevel_ranges_cont rs' (res::acc) cont)
    | [] ->
       (* When we are done traversing the rs, we reverse the accumulator and call the continuation *)
       cont (List.rev acc)
  in 

  (* Another helper function that ensures no function calls are left in the representation.
     Traverses the representation of each datatype and whenever it encounters a 
     function call, it evaluates it after potentially instantiating its arguments, 
     binds the result to a fresh unknown, and creates a new dep_type.

     Assumes: 
     The input datatypes are range-convertible apart from any function calls.
   *)
  (* For your sanity, ask someone to explain this function before tweaking anything. *)
  let rec instantiate_function_calls_cont dts (acc : dep_type list) (cont : dep_type list -> b) : b =
    match dts with 
    | [] -> cont (List.rev acc)
    | dt::dts' -> 
       begin match dt with
       | DCtr (c, inner_dts) ->
          (* Call the instantiate function to first instantiate the inner datatypes *)
          instantiate_function_calls_cont inner_dts []
            (fun inner_dts' ->
              (* Call the instantiate function as its continuation after repacking DCtr *)
              instantiate_function_calls_cont dts' (DCtr (c, inner_dts') :: acc) cont)
       | DTyVar x ->
          (* Just continue along instantiating the rest of the function calls *)
          instantiate_function_calls_cont dts' (DTyVar x :: acc) cont
       | DApp (DTyVar f, argdts) ->
          (* Again, instantiate the inner dts' function calls if necessary first *)
          instantiate_function_calls_cont argdts []
            (fun argdts' ->
              (* Convert the datatypes to ranges *)
              let ranges =
                match sequenceM convert_to_range argdts' with
                (* TODO Message *)
                | None -> qcfail "Could not convert datatypes to ranges in function call" 
                | Some ranges -> ranges
              in 
                 
              (* Then actually instantiate the ranges *)
              instantiate_toplevel_ranges_cont ranges []
                (fun ranges' ->
                  (* Create a fresh unknown u *)
                  let u = unk_provider.next_unknown () in
                  (* Convert the ranges to coq_exprs *)
                  let coq_expr_args = List.map (range_to_coq_expr !umap) ranges' in

                  (* Bind the result of the application f args to u *)
                  let_in_expr (Unknown.to_string u)
                    (gApp (gVar f) coq_expr_args)
                    (fun uvar ->
                      umap := UM.add uvar FixedInput !umap;
                      (* Given the variable representation of u, proceed to instantiate 
                         the rest of the dts' *)
                      instantiate_function_calls_cont dts' (DTyVar uvar :: acc) cont)))
       | DTyCtr (_c,_dts) ->
          instantiate_function_calls_cont dts' (dt :: acc) cont
       | DTyParam p ->
          (* Just continue along instantiating the rest of the function calls *)
          instantiate_function_calls_cont dts' (DTyParam p :: acc) cont
       | DHole ->
          (* Just continue along instantiating the rest of the function calls *)
          instantiate_function_calls_cont dts' (DHole :: acc) cont
       | _ -> failwith ("Not a type! " ^ (dep_type_to_string dt))
       end
  in 

  (* *********************************************************** *)
  (* Actual computations - multiple mutually recursive functions *)
  (* *********************************************************** *)

  (* Main Function - handle_TyCtr :
     Handles a single constraint of the form (C e1 e2 ...)
     Inputs:
     - ctr_index : The index of the handled constraint. For example, if the constructor we are 
       currently processing is : forall x y, A e -> C e1 e2 -> D e3 e4 -> P e5 e6 and we are 
       handling (C e1 e2), then m = 2).
     - is_pos : A boolean flag that signifies if we are processing (C e1 e2 ..) or ~ (C e1 e2 ...)
     - c : The constraint type constructor C
     - dts : The arguments to the type constructor (e1 e2 ...)
     - dt' : The remainder constraints that are left to be processed.

     Notes:
     
   *)
  let rec handle_TyCtr (ctr_index : int) (is_pos : bool) (c : ty_ctr)
            (dts : dep_type list) (dt' : dep_type) =

    (* First instantiate the function calls in the dep_type list *)
    instantiate_function_calls_cont dts [] (fun dts' ->

    (* Convert the modified dep_types to ranges *)
    let ranges = match sequenceM convert_to_range dts' with
      | Some ranges -> ranges
      | None -> qcfail "Internal: After instantiating function calls, datatypes should be convertible to ranges."
    in 

    (* Rewrite: Actually look at available instances. *)

    (* Inv: r has to be a toplevel range. *)
    let mode_analyze r umap =
      if is_parameter r then ModeParameter else
      if is_fixed_range umap r then ModeFixed
      else 
        let handle_partial r umap =
          let eqs = ref [] in
          let unks = ref [] in 
          let rec convert_to_pat parent r =
            match r with
            | Parameter x -> MatchParameter x
            | Ctr (ctr, rs) -> MatchCtr (ctr, List.map (convert_to_pat Unknown.undefined) rs)
            | Unknown u -> convert_to_pat u (UM.find u umap)
            | FixedInput ->
               (* introduce fresh unknown, match that, yield equality *)               
               let u = make_up_name () in
               eqs := (u, parent) :: !eqs;
               MatchU u
            | Undef dt ->
               (* register as unknown to be generated from pattern *)
               if List.exists (fun ut -> (fst ut) = parent) !unks then
                 begin
                   (* Already fixed from another pattern. Test equality *)
                   let u = make_up_name () in
                   (* Add it in the map temporarily - will be fixed soon. *)
                   eqs := (u, parent) :: !eqs;
                   MatchU u
                 end
               else
                 begin
                   unks := (parent, dt) :: !unks;
                   MatchU parent
                 end
          in ModePartlyDef (!eqs, !unks, convert_to_pat Unknown.undefined r)
        in
        (* At this point, it can only be an unknown or a constructor. *)        
        match r with
        | Unknown u ->
           let rec unknown_chain u =
             match UM.find u umap with
             | Undef dt -> ModeUndefUnknown (u,dt) (* TODO which u? *)
             | Unknown u' -> unknown_chain u'
             | _ -> handle_partial r umap in
           unknown_chain u
        | Ctr _ -> handle_partial r umap
        | _ -> failwith "Not U/C MA"
    in

    (* r: range
       b: boolean
          false = input, true = output.
       m: Mode *)
    let compatible b m =
      match m, b with
      | ModeFixed, false -> Compatible
      | ModeUndefUnknown _, false -> InstCompatible
      | ModePartlyDef (eqs, unks, pat), false -> InstCompatible
      | ModeFixed, true  -> Incompatible
      | ModeUndefUnknown _ , true -> Compatible
      | ModePartlyDef _, true -> PartCompatible
    in
    let mode_score bs ms filter_bs =
      let rec walk_scores ms bs =
        match ms, bs with
        | ModeParameter::ms', _::bs' when filter_bs-> walk_scores ms' bs'
        | ModeParameter::ms', bs when not filter_bs-> walk_scores ms' bs
        | m::ms', b::bs' -> compatible b m :: walk_scores ms' bs'
        | _, _ -> []
      in
      let cs = walk_scores ms bs in
      (*      let cs = List.map2 compatible bs ms in *)
      ((List.filter (fun c -> c == Compatible) cs),
       (List.filter (fun c -> c == InstCompatible) cs),
       (List.filter (fun c -> c == Incompatible) cs),
       (List.filter (fun c -> c == PartCompatible) cs))
    in 
             
    (*  LOGIC: 
        - Filter out incompatible
        - Prioritize production
          + Prioritize Modes that don't have PartCompatible
          + Default to PartCompatible with the shallowest pattern (TODO)
        - Fallback to checker
        - If none exist, fail with a more useful error message
          + Alternative: Call a let-bound generator to show the instance to the user 
     *)
    (* Quick-and-dirty sorting based on logic above. 
       Most of the time there will only be one producer, and the 
       effect will be filtering for (in)compatibility.
     *)
    msg_debug (str (Printf.sprintf "Look here v2!! %s %s" (ty_ctr_to_string gen_ctr) (ty_ctr_to_string c)) ++ fnl ());
    
    let producer_classes =
      List.concat (List.map (fun n -> find_typeclass_bindings n c) prod_class_names) in
    let checker_classes =
      List.concat (List.map (fun n -> find_typeclass_bindings n c) ["DecOpt"; "Dec"]) in      
    let curr_modes  = List.map (fun r -> mode_analyze r !umap) ranges in
    msg_debug (str (Printf.sprintf "Current Ranges: %s" (ranges_to_string ranges)) ++ fnl ());
    msg_debug (str (Printf.sprintf "Current Modes: %s\n" (String.concat " " (List.map range_mode_to_string curr_modes))) ++ fnl ());
    
    msg_debug (str "Producer classes: " ++ fnl ());
    List.iter (fun bs -> msg_debug (str (String.concat " " (List.map (fun b -> Printf.sprintf "%b" b) bs)) ++ fnl ())) producer_classes;
    msg_debug (str "Checker classes: " ++ fnl ());
    List.iter (fun bs -> msg_debug (str (String.concat " " (List.map (fun b -> Printf.sprintf "%b" b) bs)) ++ fnl ())) checker_classes; 
    
    let ranked_producers =
      List.sort (fun ((c1,i1,_,p1),_) ((c2,i2,_,p2),_) ->
          compare (List.length p1, List.length i1)
            (List.length p2, List.length i2)) 
        (List.filter (fun ((_,_,inc,_),_) -> List.length inc == 0)
           (List.map (fun bs -> (mode_score bs curr_modes true, bs)) producer_classes)) in

    msg_debug (str (Printf.sprintf "Look here v2!! %s %s" (ty_ctr_to_string gen_ctr) (ty_ctr_to_string c)) ++ fnl ());
    List.iter (fun ((c,i,inc,p), bs) ->
        msg_debug (str (Printf.sprintf "%d-%d-%d-%d" (List.length c) (List.length i) (List.length inc) (List.length p)) ++ fnl ());
        msg_debug (str (String.concat " " (List.map (Printf.sprintf "%b") bs)) ++ fnl ());
      ) ranked_producers;

    (* Invariant: filter out params in recursive mode *)
    let compute_for_mode (ms : range_mode list) (bs : bool list) (is_rec : bool) =

      msg_debug (str "Computing for Mode: " ++
                   str (String.concat " " (List.map range_mode_to_string ms)) ++
                   str (String.concat " " (List.map (Printf.sprintf "%b") bs)) ++
                   fnl ());
                   
      let uts = ref UM.empty in
      let need_filtering = ref None in
      let unknown_gen    = ref None in
      let add_to_map u dt =
        try
          if UM.find u !uts = dt then ()
          else failwith "Trying to add unknown in two different types?"
        with
          Not_found -> uts := UM.add u dt !uts in
      let process_mb_pair i m b =
        match m, b with
        | ModeFixed, false -> ()
        | ModeUndefUnknown (u,dt), false -> add_to_map u dt
        | ModePartlyDef (_, unks, _), false ->
           List.iter (fun (u,dt) -> add_to_map u dt) unks
        | ModeFixed, true -> raise Incompatible_mode
        | ModeUndefUnknown (u,dt), true ->
           unknown_gen := Some (u, dt, i)
        | ModePartlyDef (eqs,unks,pat), true ->
           need_filtering := Some (eqs, unks, pat, i)
      in
      let rec walk_mbs i ms bs =
        match ms, bs with
        | ModeParameter::ms',_ when is_rec -> walk_mbs i ms' bs
        | ModeParameter::ms',false::bs' when not is_rec -> walk_mbs i ms' bs'
        | m::ms', b::bs' ->
           process_mb_pair i m b;
           walk_mbs (i+1) ms' bs'
        | _, _ -> ()
      in
      walk_mbs 0 ms bs;
      (!uts, !need_filtering, !unknown_gen)
    in

    if not (gen_ctr = c) then
      begin
        msg_debug (str "Non-recursive constructor" ++ fnl ());

        begin match ranked_producers with
        | (_,bs) :: _ when is_pos ->
           msg_debug (str ("Found Producer! " ^ String.concat "," (List.map (Printf.sprintf "%b") bs)) ++ fnl ());
           (* Begin producer stuff. *)

           (* Step 1: Figure out which unknowns need to be instantiated for mode to work out *)
           (* Invariant: These are not Incompatible *)
           let (uts, need_filtering, unknown_gen) = compute_for_mode curr_modes bs false in
           let unknowns_for_mode = UM.bindings uts in
           msg_debug (str "Unknowns for mode: " ++ str (String.concat " " (List.map (fun (u,_) -> Unknown.to_string u) unknowns_for_mode)) ++ fnl ());

           (* Instantiate any unknowns that need to be for the mode to work. *)
           instantiate_toplevel_ranges_cont (List.map (fun (x,_t) -> Unknown x) unknowns_for_mode) [] (fun _ranges ->
           (* TODO: Need filtering. *)

           let unknown_to_generate_for =
             match need_filtering, unknown_gen with
             | None, Some (u, dt, i) -> u
             | Some (eqs, unks, pat, i), None -> unk_provider.next_unknown ()
             | _, _ -> failwith "Simultaneous Some/None/1" 
           in
           let ranges_for_pred =
             let rs = List.map (range_to_coq_expr !umap) ranges in
             match need_filtering with
             | Some (_,_,_,i) -> List.mapi (fun j x -> if i = j then gVar unknown_to_generate_for else x) rs
             | _ -> rs 
           in 
           let pred_result = gApp ~explicit:true (gTyCtr c) ranges_for_pred in
           let pred = (* predicate we are generating for *)
             gFun [var_to_string unknown_to_generate_for] (fun _ -> pred_result)
           in

           (* Need to add the unknown in the map. The type as it will be fixed soon. *)
           umap := UM.add unknown_to_generate_for (Undef DHole) !umap;

           process_checks ex_bind unknown_to_generate_for true (instantiate_existential_methodST ctr_index pred) 
             (fun _x' ->
               let cont () = recurse_type (ctr_index + 1) dt' in
               let rec construct_eqs = function
                 | [] -> cont ()
                 | (u1,u2)::eqs' ->
                    msg_debug (str (Printf.sprintf "Handling eq: %s = %s" (Unknown.to_string u1) (Unknown.to_string u2)) ++ fnl ());
                    msg_debug (str "Before fixing..." ++ fnl ());
                    UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) !umap;
                    (*                    umap := fixVariable u1 !umap; *)
                    msg_debug (str "After fixing..." ++ fnl ());
                    UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) !umap;
                    
                    let checker =
                      gApp ~explicit:true (gInject "decOpt")
                        [ gApp (gInject "Logic.eq") [gVar u1; gVar u2]
                        ; hole
                        ; init_size]
                    in
                    check_expr ctr_index checker (construct_eqs eqs') fail_exp not_enough_fuel_exp
               in 
               match need_filtering with
               | None -> cont ()
               | Some (eqs, unks, pat, i) ->
                  msg_debug (str (Printf.sprintf "0/Before matching %s with %s..." (Unknown.to_string unknown_to_generate_for) (matcher_pat_to_string pat)) ++ fnl ());
                  msg_debug (str (Printf.sprintf "About to fix: %s" (String.concat " " (List.map (fun (x,_) -> Unknown.to_string x) unks))) ++ fnl ());
                  UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) !umap;
                  List.iter (fun (u,_) -> umap := fixVariable u !umap) unks;
                  List.iter (fun (u,_) -> umap := fixVariable u !umap) eqs;                  
                  umap := UM.add unknown_to_generate_for (matcher_pat_to_range pat) !umap;
                  msg_debug (str "After matching..." ++ fnl ());
                  UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) !umap;
                  match_inp unknown_to_generate_for pat (construct_eqs eqs) fail_exp
             )
           
           )
        | _ ->
           begin match checker_classes with
           | bs :: _ ->
              msg_debug (str ("Found Checker ! " ^ String.concat "," (List.map (Printf.sprintf "%b") bs)) ++ fnl ());
              (* Begin checker stuff. *)

              (* Then just make the checker call. *)
              let (uts, need_filtering, unknown_gen) = compute_for_mode curr_modes bs false in
        
              let unknowns_for_mode = UM.bindings uts in
              (* Instantiate any unknowns that need to be for the mode to work. *)
              instantiate_toplevel_ranges_cont (List.map (fun (x,_t) -> Unknown x) unknowns_for_mode) [] (fun _ranges ->
                  (* Generate a fresh boolean unknown *)
                  (* 
              let unknown_to_generate_for = unk_provider.next_unknown () in
              umap := UM.add unknown_to_generate_for (Undef (DCtr (injectCtr "Coq.Init.Datatypes.bool", []))) !umap;
                   *)
                  
              let inputs_for_pred =
                List.map (range_to_coq_expr !umap) ranges (* (List.filter (fun r -> not (is_parameter r)) ranges) *)
              in
              let pred = gApp ~explicit:true (gTyCtr c) inputs_for_pred in

              let body_cont = recurse_type (ctr_index + 1) dt' in
              let body_fail = fail_exp in

              (* Construct the checker for the current type constructor *)
              let checker = 
                gApp ~explicit:true (gInject "decOpt") 
                  (* P : Prop := c dts*)
                  [ pred
                  
                  (* Instance *)
                  ; hole 

                  (* Size. TODO: what do we do about this size? *)
                  ; init_size
                  
                  ] 
              in

              if is_pos then
                check_expr ctr_index
                  checker body_cont body_fail not_enough_fuel_exp
              else
                check_expr ctr_index
                  checker body_fail body_cont not_enough_fuel_exp
                )
           | _ -> failwith "TODO: ERR MSG. No Classes found."
           end
        end
      end
    else begin
      
      msg_debug (str (Printf.sprintf "Recursive:\nInput ranges: %s\nMode Ranges: %s\n" (ranges_to_string input_ranges) (ranges_to_string ranges)) ++ fnl ());

      let rec_ms = List.map (fun r -> mode_analyze r init_umap) input_ranges in
      
      msg_debug (str (Printf.sprintf "Current Modes: %s\nRec Modes: %s\n" (String.concat " " (List.map range_mode_to_string curr_modes)) (String.concat " " (List.map range_mode_to_string rec_ms))) ++ fnl ());

      let mode_to_b = function
        | ModeFixed -> false
        | ModeUndefUnknown _ -> true
        | _ -> failwith "Partial toplevel input?"
      in 
      let rec_bs = List.map mode_to_b rec_ms in

      let can_use_recursive =
        msg_debug (str "Trying compute..." ++ fnl ());
        try begin
            ignore (compute_for_mode curr_modes rec_bs true);
            msg_debug (str "Reaching here somehow?" ++ fnl ());
            true
          end
        with Incompatible_mode -> false in
      msg_debug (str (Printf.sprintf "Is it? %b" can_use_recursive) ++ fnl ());
        
      (* If the recursive case is a producer... *)
      if List.exists (fun b -> b) rec_bs && can_use_recursive then begin

        msg_debug (str "Entering recursive producer handler" ++ fnl ());
        is_base := false;
          
        (* Then just make the recursive call. *)
        let (uts, need_filtering, unknown_gen) = compute_for_mode curr_modes rec_bs true in
        
        let unknowns_for_mode = UM.bindings uts in
        (* Instantiate any unknowns that need to be for the mode to work. *)
        instantiate_toplevel_ranges_cont (List.map (fun (x,_t) -> Unknown x) unknowns_for_mode) [] (fun _ranges ->
        let unknown_to_generate_for =
          match need_filtering, unknown_gen with
          | None, Some (u, dt, i) -> u
          | Some (eqs, unks, pat, i), None -> unk_provider.next_unknown ()
          | _, _ -> failwith "Simultaneous Some/None/2" 
        in
        umap := UM.add unknown_to_generate_for (Undef DHole) !umap;
        msg_debug (str (Printf.sprintf "Unknown to generate for: %s\n" (Unknown.to_string (unknown_to_generate_for))) ++ fnl ());
        
        let inputs_for_rec_method =
          let rs = List.map (range_to_coq_expr !umap) (List.filter (fun r -> not (is_parameter r)) ranges) in
          List.map fst (List.filter (fun (r,b) -> not b) (List.combine rs rec_bs))
        in 

        let letbinds = None in
        process_checks rec_bind unknown_to_generate_for true
          (rec_method ctr_index letbinds inputs_for_rec_method)
          (fun _shouldletthis ->
               let cont (_ : unit) = recurse_type (ctr_index + 1) dt' in
               let rec construct_eqs = function
                 | [] -> cont ()
                 | (u1,u2)::eqs' ->
                    (*                    umap := fixVariable u1 !umap; *)
                    let checker =
                      gApp ~explicit:true (gInject "decOpt")
                        [ gApp (gInject "Logic.eq") [gVar u1; gVar u2]
                        ; hole
                        ; init_size]
                    in
                    check_expr ctr_index checker (construct_eqs eqs') fail_exp not_enough_fuel_exp
               in 
               match need_filtering with
               | None -> cont ()
               | Some (eqs, unks, pat, i) ->
                  msg_debug (str (Printf.sprintf "1/Before matching %s with %s..." (Unknown.to_string unknown_to_generate_for) (matcher_pat_to_string pat)) ++ fnl ());
                  msg_debug (str (Printf.sprintf "About to fix: %s" (String.concat " " (List.map (fun (x,_) -> Unknown.to_string x) unks))) ++ fnl ());
                  UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) !umap;
                  List.iter (fun (u,_) -> umap := fixVariable u !umap) eqs;                  
                  List.iter (fun (u,_) -> umap := fixVariable u !umap) unks;
                  umap := UM.add unknown_to_generate_for (matcher_pat_to_range pat) !umap;
                  msg_debug (str "After matching..." ++ fnl ());
                  UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) !umap; 
                  match_inp unknown_to_generate_for pat (construct_eqs eqs) fail_exp
          )
        )
        end
      else if List.exists (fun b -> b) rec_bs && not can_use_recursive then begin
          msg_debug (str "Can't use recursive producer - checker must exist." ++ fnl ());
          begin match checker_classes with
          | bs :: _ ->
             msg_debug (str ("Found Checker ! " ^ String.concat "," (List.map (Printf.sprintf "%b") bs)) ++ fnl ());
             (* Begin checker stuff. *)
             
             (* Then just make the checker call. *)
             let (uts, need_filtering, unknown_gen) = compute_for_mode curr_modes bs false in
             
             let unknowns_for_mode = UM.bindings uts in
             (* Instantiate any unknowns that need to be for the mode to work. *)
             instantiate_toplevel_ranges_cont (List.map (fun (x,_t) -> Unknown x) unknowns_for_mode) [] (fun _ranges ->
                 (* Generate a fresh boolean unknown *)
                 (* 
              let    unknown_to_generate_for = unk_provider.next_unknown () in
              umap : = UM.add unknown_to_generate_for (Undef (DCtr (injectCtr "Coq.Init.Datatypes.bool", []))) !umap;
                  *)
                 
             let inputs_for_pred =
               List.map (range_to_coq_expr !umap) ranges (* (List.filter (fun r -> not (is_parameter r)) ranges) *)
             in
             let pred = gApp ~explicit:true (gTyCtr c) inputs_for_pred in
             
             let body_cont = recurse_type (ctr_index + 1) dt' in
             let body_fail = fail_exp in
             
             (* Construct the checker for the current type constructor *)
             let checker = 
               gApp ~explicit:true (gInject "decOpt") 
                 (* P : Prop := c dts*)
                 [ pred
                 
                 (* Instance *)
                 ; hole 
                 
                 (* Size. TODO: what do we do about this size? *)
                 ; init_size
                 
                 ] 
             in
             
             if is_pos then
               check_expr ctr_index
                 checker body_cont body_fail not_enough_fuel_exp
             else
               check_expr ctr_index
                 checker body_fail body_cont not_enough_fuel_exp
               )
          | _ -> failwith "TODO: ERR MSG. No Classes found."
          end
        end
      else begin
        (* The recursive case is not a producer - check if there is an enumerator that works better! *)
        msg_debug (str "Entering non-recursive handler" ++ fnl ());
        match ranked_producers with
        | (_,bs) :: _ ->
           msg_debug (str ("Found producer instead of recursive checker! " ^ String.concat "," (List.map (Printf.sprintf "%b") bs)) ++ fnl ());
           (* Begin producer stuff. *)
           (* Step 1: Figure out which unknowns need to be instantiated for mode to work out *)
           (* Invariant: These are not Incompatible *)
           let (uts, need_filtering, unknown_gen) = compute_for_mode curr_modes bs false in
           let unknowns_for_mode = UM.bindings uts in
           (* Instantiate any unknowns that need to be for the mode to work. *)
           instantiate_toplevel_ranges_cont (List.map (fun (x,_t) -> Unknown x) unknowns_for_mode) [] (fun _ranges ->
           (* TODO: Need filtering. *)

           let unknown_to_generate_for =
             match need_filtering, unknown_gen with
             | None, Some (u, dt, i) -> u
             | Some (eqs, unks, pat, i), None -> unk_provider.next_unknown ()
             | _, _ -> failwith "Simultaneous Some/None/3" 
           in
           let ranges_for_pred =
             let rs = List.map (range_to_coq_expr !umap) ranges in (* (List.filter (fun r -> not (is_parameter r)) ranges) in*)
             match need_filtering with
             | Some (_,_,_,i) -> List.mapi (fun j x -> if i = j then gVar unknown_to_generate_for else x) rs
             | _ -> rs 
           in 
           let pred_result = gApp ~explicit:true (gTyCtr c) ranges_for_pred in
           let pred = (* predicate we are generating for *)
             gFun [var_to_string unknown_to_generate_for] (fun _ -> pred_result)
           in

           (* Need to add the unknown in the map. The type as it will be fixed soon. *)
           umap := UM.add unknown_to_generate_for (Undef DHole) !umap;

           (* TODO: Filtering. *)
           process_checks ex_bind unknown_to_generate_for true (instantiate_existential_methodST ctr_index pred) 
             (fun _x' ->
               let cont () = recurse_type (ctr_index + 1) dt' in
               let rec construct_eqs = function
                 | [] -> cont ()
                 | (u1,u2)::eqs' ->
                    (*                    umap := fixVariable u1 !umap;*)
                    let checker =
                      gApp ~explicit:true (gInject "decOpt")
                        [ gApp (gInject "Logic.eq") [gVar u1; gVar u2]
                        ; hole
                        ; init_size]
                    in
                    check_expr ctr_index checker (construct_eqs eqs') fail_exp not_enough_fuel_exp
               in 
               match need_filtering with
               | None -> cont ()
               | Some (eqs, unks, pat, i) ->
                  msg_debug (str (Printf.sprintf "2/Before matching %s with %s..." (Unknown.to_string unknown_to_generate_for) (matcher_pat_to_string pat)) ++ fnl ());
                  msg_debug (str (Printf.sprintf "About to fix: %s" (String.concat " " (List.map (fun (x,_) -> Unknown.to_string x) unks))) ++ fnl ());
                  UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) !umap;
                  List.iter (fun (u,_) -> umap := fixVariable u !umap) unks;
                  List.iter (fun (u,_) -> umap := fixVariable u !umap) eqs;                  
                  umap := UM.add unknown_to_generate_for (matcher_pat_to_range pat) !umap;
                  msg_debug (str "After matching..." ++ fnl ());
                  UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) !umap;                   
                  match_inp unknown_to_generate_for pat (construct_eqs eqs) fail_exp
             )
           )
        | _ ->
           (* There is no good producer, just instantiate everything and make a recursive call. *)
           msg_debug (str "Entering recursive checker call" ++ fnl ());
           is_base := false;
          
           (* Then just make the recursive call. *)
           let (uts, need_filtering, unknown_gen) = compute_for_mode curr_modes rec_bs true in
        
           let unknowns_for_mode = UM.bindings uts in
           (* Instantiate any unknowns that need to be for the mode to work. *)
           instantiate_toplevel_ranges_cont (List.map (fun (x,_t) -> Unknown x) unknowns_for_mode) [] (fun _ranges ->
           (* Generate a fresh boolean unknown *)
           let unknown_to_generate_for = unk_provider.next_unknown () in
           umap := UM.add unknown_to_generate_for (Undef (DCtr (injectCtr "Coq.Init.Datatypes.bool", []))) !umap;
           
           let inputs_for_rec_method =
             List.map (range_to_coq_expr !umap) (List.filter (fun r -> not (is_parameter r)) ranges)
           in 
           
           let letbinds = None in
           process_checks rec_bind unknown_to_generate_for true
             (rec_method ctr_index letbinds inputs_for_rec_method)
             (fun _shouldletthis -> recurse_type (ctr_index+1) dt')
           )
        end
      end
      )
(*    
    (* TODO: positive/negative context *)
    (* Then do mode analysis on the new dts *)
    match mode_analysis gen_ctr c input_ranges init_umap ranges !umap with
    | Recursive (unknowns_for_mode, remaining_unknowns, actual_inputs) ->

       msg_debug (str "Mode analysis: Recursive." ++ fnl ());
       let ums = String.concat " " (List.map (fun (u,t) -> Unknown.to_string u ^ " : " ^ dep_type_to_string t) unknowns_for_mode) in
       let rus = String.concat " " (List.map (fun (u,t) -> Unknown.to_string u ^ " : " ^ dep_type_to_string t) remaining_unknowns) in
       let ais = String.concat " " (List.map range_to_string actual_inputs) in
       msg_debug (str (ums ^ " - " ^ rus ^ " - " ^ ais) ++ fnl ());
       (* Mark recursiveness of branch *)
       is_base := false;
       (* Instantiate all the unknowns needed for the mode to work out *)
       instantiate_toplevel_ranges_cont (List.map (fun (x,_t) -> Unknown x) unknowns_for_mode) [] (fun _ranges ->

       (* We will instantiate an unknown. First create a fresh one *)
       let fresh_unknown =
         match remaining_unknowns with
         | [(x,_)] -> x
         | _ -> unk_provider.next_unknown ()
       in 
       let unknown_type =
         match remaining_unknowns with
         | [] -> DCtr (injectCtr "Coq.Init.Datatypes.bool", [])
         | _ -> dtTupleType (List.map snd remaining_unknowns)
       in
       let unknown_range =
         match remaining_unknowns with
         | [] -> Undef unknown_type
         | [(_x,_)] -> Undef unknown_type
         | _ -> listToPairAux (fun (acc, x) -> Ctr (injectCtr "Coq.Init.Datatypes.pair", [acc; x]))
                  (List.map (fun (x,_) -> Unknown x) remaining_unknowns)
       in
       umap := UM.add fresh_unknown unknown_range !umap;

       let letbinds =
         match remaining_unknowns with
         | [] -> None
         | [_] -> None
         | _ -> Some (List.map fst remaining_unknowns)
       in 

       let args = List.map (range_to_coq_expr !umap) actual_inputs in
       (* TODO: Gather all checks, and add them to the check map *)
       process_checks rec_bind fresh_unknown true
         (rec_method ctr_index letbinds args)
         (fun _shouldletthis ->
           (* If letbinds exist, need to actually bind them *)
           match letbinds with
           | Some binds ->
              msg_debug (str "In let binds in process checks" ++ fnl ());
              let_tuple_in_expr fresh_unknown binds 
                (recurse_type (ctr_index+1) dt')
           | None ->
              recurse_type (ctr_index+1) dt'
         )
         )
    | NonRecursive [] ->

       msg_debug (str "Mode analysis: NonRecursive/Checker." ++ fnl ());
       (* Checker *)

       let body_cont = recurse_type (ctr_index + 1) dt' in
       let body_fail = fail_exp in

       (* Construct the checker for the current type constructor *)
       let checker args = 
         gApp ~explicit:true (gInject "decOpt") 
           (* P : Prop := c dts*)
           [ gApp ~explicit:true (gTyCtr c) args

           (* Instance *)
           ; hole 

           (* Size. TODO: what do we do about this size? *)
           ; init_size
           
           ] 
       in

       (* Calculate arguments *)
       let args =
         msg_debug (str ("Calculating arguments with: " ^ (String.concat " " (List.map dep_type_to_string dts))) ++ fnl ());
         List.map (dt_to_coq_expr !umap) dts
(*         match sequenceM (dt_to_coq_expr !umap) dts with
         | Some rs -> rs
         | None -> qcfail "Uninstantiated function calls after instantiation?"*)
       in 
       
       if is_pos then
         check_expr ctr_index
           (checker args) body_cont body_fail not_enough_fuel_exp
       else
         check_expr ctr_index
           (checker args) body_fail body_cont not_enough_fuel_exp
    | NonRecursive all_unknowns ->

       msg_debug (str "Mode analysis: NonRecursive/Unknowns." ++ fnl ());
       let ais = String.concat " " (List.map var_to_string (List.map fst all_unknowns)) in
       msg_debug (str ais ++ fnl ());

       (* Call to arbitrarySizedST *)
       (* @arbitrarySizeST {A} (P : A -> Prop) {Instance} (size : nat) -> G (option A) *)
       (* We will instantiate an unknown. First create a fresh one *)
       let fresh_unknown =
         match all_unknowns with
         | [(x,_)] -> x
         | _ -> unk_provider.next_unknown ()
       in 
       let unknown_type = dtTupleType (List.map snd all_unknowns) in
       let unknown_range =
         match all_unknowns with
         | [] -> failwith "IMPOSSIBLE"
         | [(_x,_)] -> Undef unknown_type
         | _ -> listToPairAux (fun (acc, x) -> Ctr (injectCtr "Coq.Init.Datatypes.pair", [acc; x]))
                  (List.map (fun (x,_) -> Unknown x) all_unknowns)
       in
       umap := UM.add fresh_unknown unknown_range !umap;

       let letbinds =
         match all_unknowns with
         | [] -> None
         | [_] -> None
         | _ -> Some (List.map fst all_unknowns)
       in 

       (* LEO: LOOK AT THIS *)
       let _args = List.map (range_to_coq_expr !umap) ranges in

       let pred_result = gApp ~explicit:true (gTyCtr c) (List.map (range_to_coq_expr !umap) ranges) in
       let pred = (* predicate we are generating for *)
         gFun [var_to_string fresh_unknown]
           (fun _ ->
             match letbinds with
             | Some binds -> gLetTupleIn fresh_unknown binds pred_result
             | None -> pred_result
           )
       in

       process_checks ex_bind fresh_unknown true (instantiate_existential_methodST ctr_index pred) 
            (fun _x' -> recurse_type (ctr_index + 1) dt')

    ) 

 *)
    
(*    
      let finalizer k cmap numbered_dts = 

      match List.filter (fun (i, dt) -> not (is_fixed k dt)) numbered_dts with
      | [] -> (* Every argument to the constructor is fixed - perform a check *)

        (* Check if we are handling the current constructor. If yes, mark the need for decidability of current constructor *)
        (* need_dec is a ref in scope *)
        if c = gen_ctr then (need_dec := true; b := false) else ();

        (* Continuation handling dt2 : recurse one dt2 / None based on positivity *)
        let body_cont = recurse_type (m + 1) k cmap dt2 in
        let body_fail = fail_exp in

        if pos then check_expr m (checker (List.map (fun dt -> dt_to_coq_expr k dt) dts)) body_cont body_fail
        else check_expr m (checker (List.map (fun dt -> dt_to_coq_expr k dt) dts)) body_fail body_cont

      | [(i, DTyVar x)] -> begin (* Single variable to be generated for *)
        msg_debug (str (Printf.sprintf "%d %d %s %s %b \n" i n (ty_ctr_to_string c) (ty_ctr_to_string gen_ctr) pos) ++ fnl ());
        if i = n && c = gen_ctr && pos then begin (* Recursive call *)
          b := false;
          let args = List.map snd (List.filter (fun (i, _) -> not (i = n)) (List.mapi (fun i dt -> (i+1, dt_to_coq_expr k dt)) dts)) in
          process_checks k cmap x 
            (* Generate using recursive function *)
            true
            (rec_method ctr_index args)
            (fun k' cmap' x -> recurse_type (ctr_index + 1) k' cmap' dt2)
        end
        else if pos then begin (* Generate using "arbitrarySizeST" and annotations for type *)
          if c = gen_ctr then b := false;
          (* @arbitrarySizeST {A} (P : A -> Prop) {Instance} (size : nat) -> G (option A) *)
          let pred = (* predicate we are generating for *)
            gFun [var_to_string x]
              (fun [x] ->
                 gApp ~explicit:true (gTyCtr c) (List.map (fun (j, dt) -> 
                                             (* Replace the i-th variable with x - we're creating fun x => c dt_1 dt_2 ... x dt_{i+1} ... *)
                                             if i = j then gVar x else dt_to_coq_expr k dt
                                           ) numbered_dts))
          in
          process_checks k cmap x true (class_methodST m pred) 
            (fun k' cmap' x' -> recurse_type (m + 1) k' cmap' dt2)
        end
        else (* Negation. Since we expect the *positive* versions to be sparse, we can use suchThatMaybe for negative *)
          (* TODO: something about size for backtracking? *)
          let new_check = fun x -> checker (List.map (fun (j,dt) -> if i = j then x else dt_to_coq_expr k dt) numbered_dts) in
          let cmap' = match lookup_checks (DTyVar x) cmap with 
            | Some checks -> CMap.add (DTyVar x) ((new_check, m) :: checks) cmap
            | _ -> CMap.add (DTyVar x) [(new_check, m)] cmap in
          recurse_type (m + 1) k cmap' dt2
        end
      | [(i, dt) ] -> failwith ("Internal error: not a variable to be generated for" ^ (dep_type_to_string dt)) 

      (* Multiple arguments to be generated for. Generalized arbitrarySizeST? *)
      | filtered -> if pos then begin
          (* For now, check if n is in the filtered list *)
          if c = gen_ctr then begin 
            match List.filter (fun (i,dt) -> i = n) filtered with 
            | [(_, DTyVar x)] -> begin
                b := false; 
                (* Every other variable generated using "arbitrary" *)
                let rec build_arbs k cmap acc = function 
                  | [] -> 
                    (* base case - recursive call *)
                    if pos then 
                      let generator = rec_method m (List.rev acc) in
                      process_checks k cmap x true generator 
                        (fun k' cmap' x' -> recurse_type (m + 1) k' cmap' dt2)
                    else failwith "Negation / build_arbs"
                  | (i,dt)::rest -> 
                    if i = n then build_arbs k cmap acc rest (* Recursive argument - handle at the end *)
                    else if is_fixed k dt then (* Fixed argument - do nothing *)
                      build_arbs k cmap (dt_to_coq_expr k dt :: acc) rest 
                    else (* Call arbitrary and bind it to a new name *)
                      let rdt = convert_to_range dt in
                      instantiate_range_cont k cmap Unknown.undefined 
                        (fun k cmap c -> (* Continuation: call build_arbs on the rest *)
                           build_arbs k cmap (c :: acc) rest
                        ) rdt
                in build_arbs k cmap [] numbered_dts
              end 
            | _ -> failwith "non-recursive call with multiple arguments"
          end 
          else 
             (* TODO: factor out *)
              let rec build_arbs k cmap acc = function 
                (* TODO: Hacky: should try and find out which one is a variable *)
                | [(i,DTyVar x)] -> 
                  (* base case - recursive call *)
                  if pos then begin 
                      (* @arbitrarySizeST {A} (P : A -> Prop) {Instance} (size : nat) -> G (option A) *)
                      let pred = (* predicate we are generating for *)
                        gFun [var_to_string x]
                          (fun [x] ->
                             gApp ~explicit:true (gTyCtr c) (List.map (fun (j, dt) -> 
                                                         (* Replace the i-th variable with x - we're creating fun x => c dt_1 dt_2 ... x dt_{i+1} ... *)
                                                         if i = j then gVar x else dt_to_coq_expr k dt
                                                       ) numbered_dts))
                      in
                      process_checks k cmap x true (class_methodST m pred) 
                        (fun k' cmap' x' -> recurse_type (m + 1) k' cmap' dt2)
                  end
                  else failwith "Negation / build_arbs"
                | (i,dt)::rest -> 
                   if is_fixed k dt then (* Fixed argument - do nothing *)
                    build_arbs k cmap (dt_to_coq_expr k dt :: acc) rest 
                  else (* Call arbitrary and bind it to a new name *)
                    let rdt = convert_to_range dt in
                    instantiate_range_cont k cmap Unknown.undefined 
                      (fun k cmap c -> (* Continuation: call build_arbs on the rest *)
                         build_arbs k cmap (c :: acc) rest
                      ) rdt
              in build_arbs k cmap [] numbered_dts

             (* TODO: Special handling for equality? *)
             
(*          | _ -> failwith (Printf.sprintf "Mode failure: %s\n" (String.concat " " (List.map (fun (i,d) -> Printf.sprintf "(%d, %s)" i (dep_type_to_string d)) filtered))) *)
                             end
        else failwith "TODO: Negation with many things to be generated"
      in 
      let rec instantiate_function_calls_cont k cmap dts acc = 
        match dts with 
        | [] -> finalizer k cmap (List.rev acc)
        | (i,dt)::dts -> 
           begin match dt with 
           | DApp (DTyVar f, argdts) -> 
              (* TODO: Nested recursive calls *)
              let rec traverse_dts k cmap acc_args = function 
                | [] ->
                   let u = unk_provider.next_unknown () in
                   let_in_expr (Unknown.to_string u)
                               (gApp (gVar f) (List.rev acc_args))
                               (fun x -> 
                   instantiate_function_calls_cont (UM.add x FixedInput k) cmap dts 
                                                   ((i,DTyVar x)::acc)
                               )
                | arg::argdts' ->
(*                    traverse_dts k cmap (arg :: acc_args) argdts' *)
                   (* WARNING: ARG HERE COULD ALSO BE A FUNCTION *)
                   instantiate_range_cont k cmap Unknown.undefined 
                     (fun k' c' e' ->
                      traverse_dts k' c' (e' :: acc_args) argdts'
                     )
                     (convert_to_range arg) 
              in traverse_dts k cmap [] argdts
           | _ -> instantiate_function_calls_cont k cmap dts ((i,dt)::acc)
           end
      in 
      instantiate_function_calls_cont k cmap numbered_dts []
 *)
(*    
    and handle_app m (pos : bool) (f : dep_type) (xs : dep_type list)
                   (k : umap) (cmap : cmap) (dt2 : dep_type) =
      (* Construct the checker for the current application *)
      let checker args = 
        gApp ~explicit:true (gInject "dec") 
          (* P : Prop := c dts*)
          [ gApp ~explicit:true (gType [] f) args

          (* Instance *)
          ; hole 

          ] 
      in
      UM.iter (fun x r -> msg_debug (str ("Bound: " ^ var_to_string x ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) k; 
      let numbered_dts = List.mapi (fun i dt -> (i+1, dt)) xs in (* +1 because of nth being 1-indexed *)

      match List.filter (fun (i, dt) -> not (is_fixed k dt)) numbered_dts with
      | [] -> failwith "Check/app"
      | [x] -> failwith "Gen/1"
      | filtered -> 
         if pos then begin
           let rec build_arbs k cmap acc = function 
             (* TODO: Hacky: should try and find out which one is a variable *)
             | [(i,DTyVar x)] -> 
                  (* base case - recursive call *)
                  if pos then begin 
                      (* @arbitrarySizeST {A} (P : A -> Prop) {Instance} (size : nat) -> G (option A) *)
                      let pred = (* predicate we are generating for *)
                        gFun [var_to_string x]
                          (fun [x] ->
                             gApp ~explicit:true (gType [] f) (List.map (fun (j, dt) -> 
                                                         (* Replace the i-th variable with x - we're creating fun x => c dt_1 dt_2 ... x dt_{i+1} ... *)
                                                         if i = j then gVar x else dt_to_coq_expr k dt
                                                       ) numbered_dts))
                      in
                      process_checks k cmap x true (class_methodST m pred) 
                        (fun k' cmap' x' -> recurse_type (m + 1) k' cmap' dt2)
                  end
                  else failwith "Negation / build_arbs / application "
                | (i,dt)::rest -> 
                   if is_fixed k dt then (* Fixed argument - do nothing *)
                    build_arbs k cmap (dt_to_coq_expr k dt :: acc) rest 
                  else (* Call arbitrary and bind it to a new name *)
                    let rdt = convert_to_range dt in
                    instantiate_range_cont k cmap Unknown.undefined 
                      (fun k cmap c -> (* Continuation: call build_arbs on the rest *)
                         build_arbs k cmap (c :: acc) rest
                      ) rdt
           in build_arbs k cmap [] numbered_dts
         end
         else failwith "Negation / application"
 *)
    (* Dispatcher for constraints *)
    and handle_dt (n : int) pos dt1 dt2 : b = 
      match dt1 with 
      | DTyCtr (c,dts) -> 
        handle_TyCtr n pos c dts dt2
      | DNot dt -> 
        handle_dt n (not pos) dt dt2
(*
      | DApp (dt, dts) -> 
        handle_app n pos dt dts umap cmap dt2
 *)
      | _ -> failwith "Constraints should be type constructors/negations"

    (* Iterate through constraints *)
    and recurse_type (n : int) dt : b =
      msg_debug (str ("Recursing on type: " ^ dep_type_to_string dt) ++ fnl ());
      match dt with 
      | DProd (_, dt) -> (* Only introduces variables, doesn't constrain them *)
        recurse_type n dt
      | DArrow (dt1, dt2) ->
        msg_debug (str ("Darrowing: " ^ ((dep_type_to_string dt1))) ++ fnl ());
        handle_dt n true dt1 dt2
      | DTyCtr _ -> (* result *) 
         (* Instantiate result *)
         msg_debug (str ("Instantiating result: " ^ (Unknown.to_string result)) ++ fnl ());
         UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) !umap;

         instantiate_range_cont Unknown.undefined (Unknown result) (fun res_range ->

         msg_debug (str ("Continuation of inst range in result") ++ fnl ());
         (* Search if there is anything that is not fixed that requires instantiation *)
         let allUnknowns = List.map fst (UM.bindings !umap) in
         match List.filter (fun u -> match is_fixed !umap (DTyVar u) with
                                     | Some b -> not b
                                     | _ -> qcfail "Internal - filter") allUnknowns with
         | [] ->
            msg_debug (str "Final ret_exp call" ++ fnl ());
            ret_exp (range_to_coq_expr !umap res_range)
         | us -> begin
             warn_uninstantiated_variables allUnknowns;
             instantiate_toplevel_ranges_cont (List.map (fun u -> Unknown u) us) []
               (fun _unused_ranges ->
                 ret_exp (range_to_coq_expr !umap res_range)
               )
           end
           )
      | _ -> failwith "Wrong type" in

  let branch_gen =
    msg_debug (str "Creating branch gen" ++ fnl ());
    let rec walk_matches = function
      | [] ->
         msg_debug (str "Match output complete" ++ fnl ());
         handle_equalities init_size !eq_set (check_expr (-1)) (recurse_type 0 typ) (fail_exp) not_enough_fuel_exp
      | (u,m)::ms -> begin
          msg_debug (str (Printf.sprintf "Processing Match: %s @ %s" (Unknown.to_string u) (matcher_pat_to_string m)) ++ fnl ());
          match_inp u m (walk_matches ms) fail_exp
        end in
    (* matches are the matches returned by unification with the result type *)
    walk_matches !matches
  in 

  (* Debugging resulting match *)
  (* UM.iter (fun x r -> msg_debug (str ("Bound: " ^ var_to_string x ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) map; *)
    (* EqSet.iter (fun (u,u') -> msg_debug (str (Printf.sprintf "Eq: %s = %s\n" (Unknown.to_string u) (Unknown.to_string u')) ++ fnl())) eqs; *)
    (* List.iter (fun (u,m) -> msg_debug (str ((Unknown.to_string u) ^ (matcher_pat_to_string m)) ++ fnl ())) matches; *)

  msg_debug (str "Generated..." ++ fnl ()); 
  (* debug_coq_expr branch_gen;  *)
  (* End debugging *)

  (branch_gen ,!is_base)
