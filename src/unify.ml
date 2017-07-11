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
     if u1 == u2 then Some (k, Unknown u1, eqs, []) else
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
        if c1 == c2 then 
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
      if c1 == c2 then 
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
        if c == c' then 
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

let rec fixRange u r k = 
    match r with 
    | FixedInput -> k
    | Undef _ -> UM.add u FixedInput k 
    | Unknown u' -> fixRange u' (umfind u' k) k
    | Ctr (_, rs) -> List.fold_left (fun k r -> fixRange Unknown.undefined r k) k rs 

let fixVariable x k = fixRange x (umfind x k) k

let rec convert_to_range dt = 
  match dt with 
  | DTyVar x -> Unknown x
  | DCtr (c,dts) -> Ctr (c, List.map convert_to_range dts)
  | DTyCtr (c, dts) -> Ctr (injectCtr (ty_ctr_to_string c), List.map convert_to_range dts)
(*   | DTyParam tp -> Ctr (injectCtr (ty_param_to_string tp), []) *)
  | _ -> failwith ("Unsupported range: " ^ (dep_type_to_string dt))

let is_fixed k dt = 
  let rec aux = function
    | Undef _ -> false
    | FixedInput -> true
    | Unknown u' -> aux (umfind u' k)
    | Ctr (_, rs) -> List.for_all aux rs
  in aux (convert_to_range dt)

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

let rec dt_to_coq_expr k dt = 
  range_to_coq_expr k (convert_to_range dt)

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

let forGen = Unknown.from_string "_forGen"

let rec inputWithGen i l = 
  if i <= 1 then forGen :: l
  else let (h::t) = l in h :: (inputWithGen (i-1) t)

let need_dec = ref false

(* Handles a single branch of the inductive predicate. *)
(* fail_exp = (returnGen gNone) *)
(* ret_exp = \x. returnGen (gSome x) *)
(* class_method = (gInject "arbitrary") *)
(* class_methodST =
     App ~explicit:true (gInject "arbitrarySizeST")
              [ hole (* Implicit argument - type A *)
              ; pred
              ; hole (* Implicit instance *)
              ; gVar size ]
*)
(* rec_method = \l. gApp (gVar rec_name) l *)
(* stMaybe =
   \opt.\g.\bool_pred.
     (gApp (gInject (if opt then "suchThatMaybeOpt" else "suchThatMaybe"))
           [ g (* Use the generator provided for base generator *)
           ; bool_pred
           ])
*)

let isTyParam = function
  | DTyParam _ -> true
  | _ -> false 

let handle_branch
      (type a) (type b) (* I've started to love ocaml again because of this *)
      (n : int)
      (dep_type : dep_type)
      (input_names : var list)
      (fail_exp : b)
      (ret_exp : coq_expr -> b)
      (class_method : a)
      (class_methodST : int -> coq_expr (* pred *) -> a)
      (rec_method : int -> coq_expr list -> a)
      (bind : bool (* opt *) -> a -> string -> (var -> b) -> b)
      (stMaybe : bool (* opt *) -> a -> string -> ((coq_expr -> coq_expr) * int) list -> a)
      (check_expr : int -> coq_expr -> b -> b -> b)
      (match_inp : var -> matcher_pat -> b -> b -> b)
      (gen_ctr : ty_ctr)
      register_arbitrary
      (c : dep_ctr) : (b * bool) =
  let (ctr, typ) = c in
  let b = ref true in
  let gen = mk_name_provider "gen" in
  let dec = mk_name_provider "dec" in
  let arb = mk_name_provider "arb" in

  msg_debug (str "Debug branch" ++ fnl ());

  (* add unknowns in environment *)
  let register_unknowns map = 
    let rec aux map = function
      | DArrow (dt1, dt2) -> aux map dt2
      | DProd ((x, dt1), dt2) -> aux (UM.add x (Undef dt1) map) dt2
      | _ -> map in
    aux map typ
  in

  (* Initialize unknown map with fixed inputs, unknowns and forGen *)
  let init_map = UM.add forGen (Undef (nthType n dep_type))
                   (List.fold_left (fun m n -> UM.add n FixedInput m) 
                      (register_unknowns UM.empty) input_names) 
  in

  msg_debug (str ("Calculating ranges: " ^ dep_type_to_string (dep_result_type typ)) ++ fnl ());

  let ranges = match dep_result_type typ with
    | DTyCtr (_, dts) -> List.map convert_to_range (List.filter (fun dt -> not (isTyParam dt)) dts)
    | _ -> failwith "Not the expected result type" in

  let inputsWithGen = inputWithGen n input_names in

  (* Debugging init map *)
  msg_debug (str ("Handling branch: " ^ dep_type_to_string typ) ++ fnl ());
  UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) init_map;
  dep_fold_ty (fun _ dt1 -> msg_debug (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
    (fun _ _ dt1 -> msg_debug (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
    (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) typ;
  (* End debugging *)

  (* unify with result type *)
  match foldM (fun (k, eqs, ms) (r, n) -> unify k (Unknown n) r eqs >>= fun (k', _, eqs', ms') ->
                Some (k', eqs', ms @ ms')
              ) (Some (init_map, EqSet.empty, [])) (List.combine ranges inputsWithGen) with
  | None -> failwith "Matching result type error" 
  | Some (map, eqs, matches) -> 

    (* Process check map. XXX generator specific *)
    let process_checks k cmap x opt g (cont : umap -> cmap -> var -> b) : b = 
      match lookup_checks (DTyVar x) cmap with
      | Some checks -> 
        (* Remove checks from cmap *)
        let cmap' = CMap.remove (DTyVar x) cmap in
        bind true
          (stMaybe opt g (var_to_string x) checks)
          (var_to_string x)
          (fun x -> cont (fixVariable x k) cmap' x)
      | None -> 
        bind opt g (var_to_string x)
          (fun x -> cont (fixVariable x k) cmap x)
    in
    
    (* Function to instantiate a single range *)
    (* It also uses any checks present in the check-map *)
    let rec instantiate_range_cont (k : umap) (cmap : cmap) (parent : unknown) (cont : umap -> cmap -> coq_expr -> b) = function
      | Ctr (c,rs) -> 
        (* aux2 goes through the dts, enhancing the continuation to include the result of the head to the acc *)
        let rec traverse_ranges k cmap acc = function 
          | [] -> cont k cmap (gApp ~explicit:true (gCtr c) (List.rev acc)) (* Something about type parameters? *)
          | r::rest -> instantiate_range_cont k cmap Unknown.undefined (fun k cmap hg -> traverse_ranges k cmap (hg::acc) rest) r
        in traverse_ranges k cmap [] rs
      | Undef dt -> begin
          register_arbitrary dt; 
          process_checks k cmap parent false class_method
            (fun k' cmap' x -> cont k' cmap' (gVar x))
        end
      | Unknown u -> instantiate_range_cont k cmap u cont (umfind u k)
      | FixedInput -> cont k cmap (gVar parent)
    in 

    (* Only used as a finalizer - discards k/cmap XXX *)
    let instantiate_range k cmap r = 
      instantiate_range_cont k cmap Unknown.undefined (fun k cmap c -> ret_exp c) r
    in

    let rec combine_inductives k num_dts args = 
      match num_dts, args with 
      | [], _ -> []
      | (_,dt)::dts', arg::args' -> 
        if is_inductive_dt dt then dt_to_coq_expr k dt :: combine_inductives k dts' args
        else gVar arg :: combine_inductives k dts' args'
    in 

    (* Begin multiple mutually recursive functions *)

    (* Handle a single type constructor and recurse in dt2 *)
    (* Handle only *updates* the check map. The checks are implemented at the beginning of recurse *)
    let rec handle_TyCtr (m : int) (pos : bool) (c : ty_ctr) (dts : dep_type list)
              (k : umap) (cmap : cmap) (dt2 : dep_type) =
      let numbered_dts = List.mapi (fun i dt -> (i+1, dt)) dts in (* +1 because of nth being 1-indexed *)

      (* Construct the checker for the current type constructor *)
      let checker args = 
        gApp ~explicit:true (gInject "dec") 
          (* P : Prop := c dts*)
          [ gApp ~explicit:true (gTyCtr c) args

          (* Instance *)
          ; hole 

          ] 
      in
      match List.filter (fun (i, dt) -> not (is_fixed k dt)) numbered_dts with
      | [] -> (* Every argument to the constructor is fixed - perform a check *)

        (* Check if we are handling the current constructor. If yes, mark the need for decidability of current constructor *)
        (* need_dec is a ref in scope *)
        if c == gen_ctr then (need_dec := true; b := false) else ();

        (* Continuation handling dt2 : recurse one dt2 / None based on positivity *)
        let body_cont = recurse_type (m + 1) k cmap dt2 in
        let body_fail = fail_exp in

        if pos then check_expr m (checker (List.map (fun dt -> dt_to_coq_expr k dt) dts)) body_cont body_fail
        else check_expr m (checker (List.map (fun dt -> dt_to_coq_expr k dt) dts)) body_fail body_cont

      | [(i, DTyVar x)] -> (* Single variable to be generated for *)
        if i == n && c == gen_ctr && pos then begin (* Recursive call *)
          b := false;
          let args = List.map snd (List.filter (fun (i, _) -> not (i == n)) (List.mapi (fun i dt -> (i+1, dt_to_coq_expr k dt)) dts)) in
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
                                             if i == j then gVar x else dt_to_coq_expr k dt
                                           ) numbered_dts))
          in
          process_checks k cmap x true (class_methodST m pred) 
            (fun k' cmap' x' -> recurse_type (m + 1) k' cmap' dt2)
        end
        else (* Negation. Since we expect the *positive* versions to be sparse, we can use suchThatMaybe for negative *)
          (* TODO: something about size for backtracking? *)
          let new_check = fun x -> checker (List.map (fun (j,dt) -> if i == j then x else dt_to_coq_expr k dt) numbered_dts) in
          let cmap' = match lookup_checks (DTyVar x) cmap with 
            | Some checks -> CMap.add (DTyVar x) ((new_check, m) :: checks) cmap
            | _ -> CMap.add (DTyVar x) [(new_check, m)] cmap in
          recurse_type (m + 1) k cmap' dt2
      | [(i, dt) ] -> failwith ("Internal error: not a variable to be generated for" ^ (dep_type_to_string dt)) 

      (* Multiple arguments to be generated for. Generalized arbitrarySizeST? *)
      | filtered -> if pos then begin
          (* For now, check if n is in the filtered list *)
          if c = gen_ctr then begin 
            match List.filter (fun (i,dt) -> i == n) filtered with 
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
                    if i == n then build_arbs k cmap acc rest (* Recursive argument - handle at the end *)
                    else if is_fixed k dt then (* Fixed argument - do nothing *)
                      build_arbs k cmap (dt_to_coq_expr k dt :: acc) rest 
                    else (* Call arbitrary and bind it to a new name *)
                      let arb = arb.next_name () in
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
                                                         if i == j then gVar x else dt_to_coq_expr k dt
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
                    let arb = arb.next_name () in
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
                                                         if i == j then gVar x else dt_to_coq_expr k dt
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
                    let arb = arb.next_name () in
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
