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

type range = Ctr of constructor * range list | Unknown of unknown | Undef of dep_type | FixedInput

let rec range_to_string = function
  | Ctr (c, rs) -> constructor_to_string c ^ " " ^ str_lst_to_string " " (List.map range_to_string rs)
  | Unknown u -> Unknown.to_string u
  | Undef dt -> Printf.sprintf "Undef (%s)" (dep_type_to_string dt)
  | FixedInput -> "FixedInput"

module UM = Map.Make(UnknownOrd)

(* Maps unknowns to range *)
type umap = range UM.t

let umfind k m = 
  try UM.find k m 
  with Not_found -> (msg_error (str (Printf.sprintf "Can't find: %s" (Unknown.to_string k)) ++ fnl()); failwith "Not found")

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
            lookup u k >>= fun r' ->
            begin match r' with 
            | Undef _ -> (* The unknown should now be fixed *)
               Some (UM.add u FixedInput k, (MatchU u)::l, eqs)
            | FixedInput -> (* The unknown is already fixed, raise an eq check *)
               let u' = unk_provider.next_unknown () in
               Some (UM.add u' (Unknown u) k, (MatchU u')::l, eq_set_add u' u eqs)
            | _ -> failwith "Not supported yet"
            end
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
        unify k (Unknown u1') (Unknown u2) eqs >>= fun (k', r', eqs', ms') ->
        Some (k', Unknown u1, eqs', ms')
     | _, Unknown u2' ->
        unify k (Unknown u1) (Unknown u2') eqs >>= fun (k', r', eqs', ms') ->
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
                ) (Some (k, [], eqs, [])) (List.combine rs rs') >>= fun (k', rs', eqs', ms) ->
          Some (k', Unknown u, eqs', ms)
        else None
      | Unknown u' -> 
         unify k (Ctr (c,rs)) (Unknown u') eqs >>= fun (k', r', eqs', m') ->
         Some (k', Unknown u, eqs', m')
      end
   | _, _ -> failwith "QC Internal: TopLevel ranges should be Unknowns or Constructors"

let rec fixRange u r k = 
    match r with 
    | FixedInput -> k
    | Undef _ -> UM.add u FixedInput k 
    | Unknown u' -> fixRange u' (umfind u' k) k
    | Ctr (_, rs) -> List.fold_left (fun k r -> fixRange Unknown.undefined r k) k rs 

let fixVariable x k = fixRange x (umfind x k) k

(* Since this can fail - return an option *)
let rec convert_to_range dt = 
  match dt with 
  | DTyVar x -> Some (Unknown x)
  | DCtr (c,dts) ->
     Option.map (fun dts' -> Ctr (c, dts')) (sequenceM convert_to_range dts)
  | DTyCtr (c, dts) -> 
     Option.map (fun dts' -> Ctr (ty_ctr_to_ctr c, dts')) (sequenceM convert_to_range dts)
  | _ -> None

let is_fixed k dt = 
  let rec aux = function
    | Undef _ -> false
    | FixedInput -> true
    | Unknown u' -> aux (umfind u' k)
    | Ctr (_, rs) -> List.for_all aux rs
  in Option.map aux (convert_to_range dt)

(* convert a range to a coq expression *)
let rec range_to_coq_expr k r = 
  match r with 
  | Ctr (c, rs) -> 
     gApp (gCtr c) (List.map (range_to_coq_expr k) rs)
  | Unknown u -> 
     begin match umfind u k with
     | FixedInput -> gVar u
     | Undef _ -> (msg_debug (str "It's stupid that this is called" ++ fnl ()); gVar u)
     | Unknown u' -> range_to_coq_expr k (Unknown u')
     | Ctr (c, rs) -> gApp (gCtr c) (List.map (range_to_coq_expr k) rs)
     end
   | _ -> failwith "QC Internal: TopLevel ranges should be Unknowns or Constructors"

let dt_to_coq_expr k dt = 
  Option.map (range_to_coq_expr k) (convert_to_range dt)

let rec is_dep_type = function
  | DArrow (dt1, dt2) -> is_dep_type dt1 || is_dep_type dt2 
  | DProd ((_, dt1), dt2) -> is_dep_type dt1 || is_dep_type dt2 
  | DTyParam _ -> false
  | DTyVar _ -> true
  | DCtr _ -> true
  | DTyCtr (_, dts) -> List.exists is_dep_type dts
  | DApp (dt, dts) -> List.exists is_dep_type (dt::dts)
  | DNot dt -> is_dep_type dt

type check = (coq_expr -> coq_expr) * int

module CMap = Map.Make(OrdDepType)
type cmap = (check list) CMap.t

let lookup_checks k m = try Some (CMap.find k m) with Not_found -> None

(* TODO: When handling parameters, this might need to add additional arguments *)
(** Takes an equality map and two coq expressions [cleft] and [cright]. [cleft]
    is returned if all of the equalities hold, otherwise [cright] is
    returned. *)
let handle_equalities eqs (check_expr : coq_expr -> 'a -> 'a -> 'a)
      (cleft : 'a) (cright : 'a) = 
  EqSet.fold (fun (u1,u2) c -> 
               let checker =
                 gApp ~explicit:true (gInject "dec") [ gApp (gInject "eq") [gVar u1; gVar u2]
                                                     ; hole ]
               in
               check_expr checker c cright
             ) eqs cleft

type mode = Recursive of Unknown.t list * Unknown.t list  (* List of unknowns that need to be instantiated before recursive call and remaining unknowns *)
          | NonRecursive of Unknown.t list (* List of all unknowns that are still undefined *)

let mode_analysis (init_ranges : range list) (init_map : range UM.t)
      (curr_ranges : range list) (curr_map : range UM.t) =
  let unknowns_for_mode  = ref [] in
  let remaining_unknowns = ref [] in
  let all_unknowns = ref [] in
  (* Compare ranges takes two ranges (the initial range r1 and the current range r2)
     as well as their parents, and returns:
     - true, if we can convert the current range to the same
       mode as the original range by instantiating a list of unknowns
     - false, if we can not convert (i.e. some things are more instantiated 
       than they should be)
   *)
  let rec compare_ranges p1 r1 p2 r2 =
    match r1, r2 with
    | Unknown u1, _ -> compare_ranges u1 (UM.find u1 init_map) p2 r2
    | _, Unknown u2 -> compare_ranges p1 r1 u2 (UM.find u2 curr_map)
    | FixedInput, FixedInput -> true
    | FixedInput, Undef dt   ->
       unknowns_for_mode := p2 :: !unknowns_for_mode;
       all_unknowns := p2 :: !all_unknowns;
       true
    | FixedInput, Ctr (c, rs) ->
       (* iterate through all the rs against fixed inputs *)
       List.for_all (fun b -> b) (List.map (compare_ranges Unknown.undefined FixedInput Unknown.undefined) rs)
    | Undef _, FixedInput -> false
    | Undef _, Undef _    ->
       (* Add the second range's parent to the list of unknowns that are free, 
          but do not need to be instantiated for the mode to work *)
       remaining_unknowns := p2 :: !remaining_unknowns;
       all_unknowns := p2 :: !all_unknowns;
       true
    | Undef _, Ctr (c, rs) ->
       List.iter (fun r' -> ignore (compare_ranges p1 r1 Unknown.undefined r')) rs; false
    | _, _ -> qcfail "Implement constructors for initial ranges"
  in
  if List.for_all (fun b -> b) (List.map2 (fun r1 r2 -> compare_ranges Unknown.undefined r1 Unknown.undefined r2) init_ranges curr_ranges) 
  then Recursive (List.rev !unknowns_for_mode, List.rev !remaining_unknowns)
  else NonRecursive !all_unknowns

let isTyParam = function
  | DTyParam _ -> true
  | _ -> false 
  
let handle_branch
      (type a) (type b) (* I've started to love ocaml again because of this *)
      (n : int)
      (dep_type : dep_type)
      (fail_exp : b)
      (ret_exp : coq_expr -> b)
      (instantiate_existential_method : a)
      (instantiate_existential_methodST : int -> coq_expr (* pred *) -> a)
      (rec_method : int -> coq_expr list -> a)
      (bind : bool (* opt *) -> a -> string -> (var -> b) -> b)
      (stMaybe : bool (* opt *) -> a -> string -> ((coq_expr -> coq_expr) * int) list -> a)
      (check_expr : int -> coq_expr -> b -> b -> b)
      (match_inp : var -> matcher_pat -> b -> b -> b)
      (let_in_expr : string -> coq_expr -> (var -> b) -> b)
      (gen_ctr : ty_ctr)
      (init_umap : range UM.t)
      (init_tmap : dep_type UM.t)
      (input_ranges : range list)
      (c : dep_ctr) : (b * bool) =

  (* ************************ *)
  (* Step 0 : Initializations *)
  (* ************************ *)
  
  let (ctr, typ) = c in

  (* Local reference : is this constructor recursive or not? *)
  let is_base = ref true in

  (* Local references to handle map updates. Keep init_umap intact for mode analysis. *)
  let umap_ref = ref init_umap in
  let tmap_ref = ref init_tmap in

  (* Check map - registers necessary checks for variable instantiation *)
  let cmap_ref = ref CMap.empty in
  
  (* Add all universally quantified unknowns in the u/t environments. *)
  let rec register_unknowns = function
      | DArrow (dt1, dt2) -> register_unknowns dt2
      | DProd ((x, dt1), dt2) ->
         umap_ref := UM.add x (Undef dt1) !umap_ref;
         tmap_ref := UM.add x dt1 !tmap_ref;
         register_unknowns dt2
      | _ -> ()
  in
  register_unknowns typ;
  
  let arb = mk_name_provider "arb" in

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
  UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) !umap_ref;
  dep_fold_ty (fun _ dt1 -> msg_debug (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
    (fun _ _ dt1 -> msg_debug (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
    (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) typ;
  (* End debugging *)

  (* ********************************************* *)  
  (* Step 1: Unify result ranges with input ranges *)
  (* ********************************************* *)

  (* Set of equality checks necessary *)
  let eq_set_ref  = ref EqSet.empty in
  (* List of necessary pattern matches *)
  let matches_ref = ref [] in
  (* Function to handle a single argument *)
  let unify_single_pair r_in r_res =
    match unify !umap_ref r_in r_res !eq_set_ref with
    | Some (umap', _range, eq_set', extra_matches) ->
       (* Unification succeeded; update info *)
       umap_ref    := umap';
       eq_set_ref  := eq_set';
       matches_ref := extra_matches @ !matches_ref
    | None ->
       (* Unification failed. *)
       qcfail "Matching result type error" (* TODO: Better error message here? *)
  in
  List.iter2 unify_single_pair input_ranges result_ranges;

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
  (* ZOE: What do you mean by XXX generator specific? Is this comment still relevant? *)
  let process_checks umap cmap x opt g (cont : umap -> cmap -> var -> b) : b = 
    match lookup_checks (DTyVar x) cmap with
    | Some checks -> 
       (* Remove checks from cmap *)
       let cmap' = CMap.remove (DTyVar x) cmap in
       bind true
         (stMaybe opt g (var_to_string x) checks)
         (var_to_string x)
         (fun x -> cont (fixVariable x umap) cmap' x)
    | None -> 
       bind opt g (var_to_string x)
         (fun x -> cont (fixVariable x umap) cmap x)
  in

  (* Two mutually recursive functions follow for instantiating ranges. *)
  
  (* Function to instantiate a single range; uses an input check-map for additional checks. 
     Takes a continuation that receives the potentially updated unknown- and check-maps, as 
     well as the (instantiated) range to produce a result. *)
  let rec instantiate_range_cont umap cmap (parent : unknown)
            (cont : umap -> cmap -> range -> b) = function
    | Ctr (c,rs) ->
       (* We need to recursively instantiate all the ranges rs, using the function below *)
       instantiate_toplevel_ranges_cont umap cmap rs []
         (fun umap' cmap' rs' -> cont umap' cmap' (Ctr (c, rs')))
    | Undef dt ->
       (* For undefined, we need to instantiate the parrent by processing its checks. *)
         process_checks umap cmap parent false instantiate_existential_method
           (fun umap' cmap' x -> cont umap' cmap' (Unknown x))
    | Unknown u ->
       (* Unknowns just propagate one step further *)
       instantiate_range_cont umap cmap u cont (umfind u umap)
    | FixedInput ->
       (* Just call the continuation on the parent. *)
       cont umap cmap (Unknown parent)

  (* Function that operates on multiple top-level ranges at once, mapping the above over a list *)
  and instantiate_toplevel_ranges_cont umap cmap (rs : range list) (acc : range list)
            (cont : umap -> cmap -> range list -> b) : b =
    match rs with
    | r ::rs' ->
       (* For each range r, we need to recursively call instantiate_range with the 
          current umap and cmap, and no defined parent. *)
       instantiate_range_cont umap cmap Unknown.undefined
         (* The continuation receives an updated umap', cmap' and a new range res,
            representing the (potentially instantiated) range.
            We then add res to an accumulator list and continue the traversal. *)
         (fun umap' cmap' res -> instantiate_toplevel_ranges_cont umap' cmap' (res::acc) rs' cont) r
    | [] ->
       (* When we are done traversing the rs, we reverse the accumulator and call the continuation *)
       cont umap cmap (List.rev acc)
  in 

  (* Another helper function that ensures no function calls are left in the representation.
     Traverses the representation of each datatype and whenever it encounters a 
     function call, it evaluates it after potentially instantiating its arguments, 
     binds the result to a fresh unknown, and creates a new dep_type.

     Assumes: 
     The input datatypes are range-convertible apart from any function calls.
   *)
  (* For your sanity, ask someone to explain this function before tweaking anything. *)
  let rec instantiate_function_calls_cont umap cmap dts (acc : dep_type list)
            (cont : umap -> cmap -> dep_type list -> b) : b =
    match dts with 
    | [] -> cont umap cmap (List.rev acc)
    | dt::dts' -> 
       begin match dt with
       | DCtr (c, inner_dts) ->
          (* Call the instantiate function to first instantiate the inner datatypes *)
          instantiate_function_calls_cont umap cmap inner_dts []
            (fun umap' cmap' inner_dts' ->
              (* Call the instantiate function as its continuation after repacking DCtr *)
              instantiate_function_calls_cont umap' cmap' dts' (DCtr (c, inner_dts') :: acc) cont)
       | DTyVar x ->
          (* Just continue along instantiating the rest of the function calls *)
          instantiate_function_calls_cont umap cmap dts' (DTyVar x :: acc) cont
       | DApp (DTyVar f, argdts) ->
          (* Again, instantiate the inner dts' function calls if necessary first *)
          instantiate_function_calls_cont umap cmap argdts []
            (fun umap' cmap' argdts' ->
              (* Convert the datatypes to ranges *)
              let ranges =
                match sequenceM convert_to_range argdts' with
                (* TODO Message *)
                | None -> qcfail "Could not convert datatypes to ranges in function call" 
                | Some ranges -> ranges
              in 
                 
              (* Then actually instantiate the ranges *)
              instantiate_toplevel_ranges_cont umap' cmap' ranges []
                (fun umap'' cmap'' ranges' ->
                  (* Create a fresh unknown u *)
                  let u = unk_provider.next_unknown () in
                  (* Convert the ranges to coq_exprs *)
                  let coq_expr_args = List.map (range_to_coq_expr umap'') ranges' in

                  (* Bind the result of the application f args to u *)
                  let_in_expr (Unknown.to_string u)
                    (gApp (gVar f) coq_expr_args)
                    (fun uvar ->
                      (* Given the variable representation of u, proceed to instantiate 
                         the rest of the dts' *)
                      instantiate_function_calls_cont
                        (UM.add uvar FixedInput umap'') cmap'' dts' (DTyVar uvar :: acc) cont)))
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
  let rec handle_TyCtr (ctr_index : int) (is_pos : bool) (c : ty_ctr) (dts : dep_type list)
            (dt' : dep_type) =

    (*
      (* Construct the checker for the current type constructor *)
      let checker args = 
        gApp ~explicit:true (gInject "dec") 
          (* P : Prop := c dts*)
          [ gApp ~explicit:true (gTyCtr c) args

          (* Instance *)
          ; hole 

          ] 
      in
     *)
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
            (rec_method m args)
            (fun k' cmap' x -> recurse_type (m + 1) k' cmap' dt2)
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

    (* Dispatcher for constraints *)
    and handle_dt (n : int) pos dt1 dt2 k cmap = 
      match dt1 with 
      | DTyCtr (c,dts) -> 
        handle_TyCtr n pos c dts k cmap dt2
      | DNot dt -> 
        handle_dt n (not pos) dt dt2 k cmap
      | DApp (dt, dts) -> 
        handle_app n pos dt dts k cmap dt2
      | _ -> failwith "Constraints should be type constructors/negations"

    (* Iterate through constraints *)
    and recurse_type (n : int) k cmap = function
      | DProd (_, dt) -> (* Only introduces variables, doesn't constrain them *)
        recurse_type n k cmap dt
      | DArrow (dt1, dt2) ->
        msg_debug (str ("Darrowing: " ^ range_to_string (umfind forGen k)) ++ fnl ());
        handle_dt n true dt1 dt2 k cmap
      | DTyCtr _ -> (* result *) 
         (* Instantiate forGen *)
         instantiate_range_cont k cmap Unknown.undefined (fun k' cmap' c -> 
         (* Search if there is anything that is not fixed that requires instantiation *)
         let allUnknowns = List.filter (fun u -> not (is_fixed k' (DTyVar u))) (List.map fst (UM.bindings k')) in
         match allUnknowns with 
         | [] -> ret_exp c 
         | _ -> begin 
             msg_warning (str ("After proccessing all constraints, there are still uninstantiated variables: " ^ 
                            String.concat " , " (List.map var_to_string allUnknowns) ^ ". Proceeding with caution...") ++ fnl ());
             let rec inst_unknowns k cmap = function
               | [] -> ret_exp c
               | h::t -> 
                  instantiate_range_cont k cmap Unknown.undefined 
                                         (fun k' cmap' _ ->
                                          inst_unknowns k' cmap' t
                                         ) (Unknown h)
             in inst_unknowns k' cmap' allUnknowns
           end
         ) (Unknown forGen)
      | _ -> failwith "Wrong type" in

    let branch_gen =
      let rec walk_matches = function
        | [] -> handle_equalities eqs (check_expr (-1)) (recurse_type 0 map CMap.empty typ) (fail_exp)
        | (u,m)::ms -> begin
            msg_debug (str (Printf.sprintf "Processing Match: %s @ %s" (Unknown.to_string u) (matcher_pat_to_string m)) ++ fnl ());
            match_inp u m (walk_matches ms) fail_exp
          end in
      (* matches are the matches returned by unification with the result type *)
      walk_matches matches
    in 

    (* Debugging resulting match *)
    (* UM.iter (fun x r -> msg_debug (str ("Bound: " ^ var_to_string x ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) map; *)
    (* EqSet.iter (fun (u,u') -> msg_debug (str (Printf.sprintf "Eq: %s = %s\n" (Unknown.to_string u) (Unknown.to_string u')) ++ fnl())) eqs; *)
    (* List.iter (fun (u,m) -> msg_debug (str ((Unknown.to_string u) ^ (matcher_pat_to_string m)) ++ fnl ())) matches; *)

    (* msg_debug (str "Generated..." ++ fnl ()); *)
    (* debug_coq_expr branch_gen; *)
    (* End debugging *)

    (branch_gen ,!b)
