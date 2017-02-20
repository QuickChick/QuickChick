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

(* TODO : move to utils or smth *)
type name_provider = { next_name : unit -> string }

let mk_name_provider s = 
  let cnt = ref 0 in
  { next_name = fun () -> 
      let res = s ^ string_of_int !cnt in
      incr cnt;
      res 
  }

(* Advanced Generators *)

(* Ranges are undefined, unknowns or constructors applied to ranges *)
type unknown = string

type range = Ctr of constructor * range list | Unknown of unknown | Undef of dep_type | FixedInput

let rec range_to_string = function
  | Ctr (c, rs) -> constructor_to_string c ^ " " ^ str_lst_to_string " " (List.map range_to_string rs)
  | Unknown u -> u
  | Undef dt -> Printf.sprintf "Undef (%s)" (dep_type_to_string dt)
  | FixedInput -> "FixedInput"
  
module UM = Map.Make(String)

type umap = range UM.t

let lookup k m = try Some (UM.find k m) with Not_found -> None

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

type matcher_pat = 
  | MatchCtr of constructor * matcher_pat list
  | MatchU of unknown

let rec matcher_pat_to_string = function
  | MatchU u -> u
  | MatchCtr (c, ms) -> constructor_to_string c ^ " " ^ str_lst_to_string " " (List.map matcher_pat_to_string ms)

type matcher = unknown * matcher_pat

let rec matcher_to_string = function
  | (u, m) -> Printf.sprintf "Match %s With %s\n" u (matcher_pat_to_string m)

let unk_provider = mk_name_provider "unkn"

(* Match a constructor/ranges list to a fixed input *)
(* Range list is toplevel, so it's mostly unifications.
   If any of the unknowns in rs is "FixedInput", then 
   we need to create a fresh unknown, bind it to the other unknown and 
   raise an equality check *)
let rec raiseMatch (k : umap) (c : constructor) (rs : range list) (eqs: EqSet.t) 
        : (umap * matcher_pat * EqSet.t) option = 
  foldM (fun (k, l, eqs) r ->
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
               let u' = unk_provider.next_name () in
               Some (UM.add u' (Unknown u) k, (MatchU u')::l, eq_set_add u' u eqs)
            | _ -> failwith "Not supported yet"
            end
        ) (Some (k, [], eqs)) rs >>= fun (k', l, eqs') ->
  Some (k', MatchCtr (c, List.rev l), eqs')

(* Invariants: 
   -- Everything has a binding, even if just Undef 
   -- r1, r2 are never FixedInput, Undef (handled inline)
   -- TopLevel ranges can be unknowns or constructors applied to toplevel ranges
   -- Constructor bindings in umaps are also toplevel. 
   -- Only unknowns can be bound to Undef/FixedInput
*)
let rec unify (k : umap) (r1 : range) (r2 : range) (eqs : EqSet.t)
        : (umap * range * EqSet.t * matcher list) option =
  msgerr (str (Printf.sprintf "Calling unify with %s %s" (range_to_string r1) (range_to_string r2)) ++ fnl ());
  match r1, r2 with
  | Unknown u1, Unknown u2 ->
     if u1 == u2 then Some (k, Unknown u1, eqs, []) else
     lookup u1 k >>= fun r1 -> 
     lookup u2 k >>= fun r2 ->
     begin match r1, r2 with 
     (* "Delay" cases - unknowns call unify again *)
     (* TODO: rething return value *)
     | Unknown u1', _ -> 
        unify k (Unknown u1') r2 eqs >>= fun (k', r', eqs', ms') ->
        Some (k', Unknown u1, eqs', ms')
     | _, Unknown u2' ->
        unify k r1 (Unknown u2') eqs >>= fun (k', r', eqs', ms') ->
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

let fixVariable x k = 
  let rec fixRange u r k = 
    match r with 
    | FixedInput -> k
    | Undef _ -> UM.add u FixedInput k 
    | Unknown u' -> fixRange u' (UM.find u' k) k
    | Ctr (_, rs) -> List.fold_left (fun k r -> fixRange "internalerror" r k) k rs 
  in fixRange x (UM.find x k) k

let rec convert_to_range dt = 
  match dt with 
  | DTyVar x -> Unknown (ty_var_to_string x)
  | DCtr (c,dts) -> Ctr (c, List.map convert_to_range dts)
  | _ -> failwith ("Unsupported range: " ^ (dep_type_to_string dt))

let is_fixed k dt = 
  let rec aux = function
    | Undef _ -> false
    | FixedInput -> true
    | Unknown u' -> aux (UM.find u' k)
    | Ctr (_, rs) -> List.for_all aux rs
  in aux (convert_to_range dt)

let rec dt_to_coq_expr dt = 
  match dt with 
  | DTyVar x -> gTyVar x
  | DCtr (c,dts) -> gApp (gCtr c) (List.map dt_to_coq_expr dts)
  | _ -> failwith ("Unsupported dt to coq_expr: " ^ (dep_type_to_string dt)) 


let rec is_dep_type = function
  | DArrow (dt1, dt2) -> is_dep_type dt1 || is_dep_type dt2 
  | DProd ((_, dt1), dt2) -> is_dep_type dt1 || is_dep_type dt2 
  | DTyParam _ -> false
  | DTyVar _ -> true
  | DCtr _ -> true
  | DTyCtr (_, dts) -> List.exists is_dep_type dts

let need_dec = ref false

let arbitrarySizedST gen_ctr dep_type gen_type ctrs input_names inputs n register_arbitrary =
  let gen = mk_name_provider "gen" in
  let dec = mk_name_provider "dec" in
  let arb = mk_name_provider "arb" in

  let rec_dec_name = gInject (Printf.sprintf "depDec%n" (dep_type_len dep_type)) in

  let forGen = "_forGen" in

  let rec inputWithGen i l = 
    if i <= 1 then forGen :: l
    else let (h::t) = l in h :: (inputWithGen (i-1) t) in

  (* Handling a branch: returns the generator and a boolean (true if base branch) *)
  let handle_branch size rec_name (c : dep_ctr) : (coq_expr * bool) = 
    let (ctr, typ) = c in
    let b = ref true in 

    msgerr (str "Debug branch" ++ fnl ());

    let register_unknowns map = 
      let rec aux map = function
        | DArrow (dt1, dt2) -> aux map dt2
        | DProd ((x, dt1), dt2) -> aux (UM.add (ty_var_to_string x) (Undef dt1) map) dt2
        | _ -> map in
      aux map typ
    in

    let init_map = UM.add forGen (Undef (nthType n dep_type)) (List.fold_left (fun m n -> UM.add n FixedInput m) (register_unknowns UM.empty) input_names) in

    let ranges = match dep_result_type typ with
      | DTyCtr (_, dts) -> List.map convert_to_range dts
      | _ -> failwith "Not the expected result type" in

    let inputsWithGen = inputWithGen n input_names in

    (* Debugging init map *)
    msgerr (str ("Handling branch: " ^ dep_type_to_string typ) ++ fnl ());
    UM.iter (fun x r -> msgerr (str ("Bound: " ^ x ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) init_map;
    dep_fold_ty (fun _ dt1 -> msgerr (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
                (fun _ _ dt1 -> msgerr (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
                (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) typ;
    (* End debugging *)

    match foldM (fun (k, eqs, ms) (r, n) -> unify k (Unknown n) r eqs >>= fun (k', _, eqs', ms') ->
                                      Some (k', eqs', ms @ ms')
          ) (Some (init_map, EqSet.empty, [])) (List.combine ranges inputsWithGen) with
    | None -> failwith "Matching result type error" 
    | Some (map, eqs, matches) -> 

    (* Construct matches - TODO: move to generic lib *)
    let construct_match (u, m) body = 
      let rec aux = function 
        | MatchU u' -> CPatAtom (dummy_loc, Some (Ident (dummy_loc, Id.of_string u')))
        | MatchCtr (c, ms) -> 
           CPatCstr (dummy_loc, 
                     Ident (dummy_loc, Id.of_string (constructor_to_string c)),
                     [],
                     List.map (fun m -> aux m) ms) in
      CCases (dummy_loc,
              Term.RegularStyle,
              None (* return *), 
              [(CRef (Ident (dummy_loc, Id.of_string u),None), (None, None))], (* single discriminee, no as/in *)
              [ (dummy_loc, [dummy_loc, [aux m]], body)
              ; (dummy_loc, [dummy_loc, [CPatAtom (dummy_loc, None)]], returnGen gNone)
              ]
             )
    in

    (* Construct equalities *)

    (* Function to instantiate a single unknown *)
    let instantiate_unknown k u = 
      match lookup u k with
      | None -> failwith ("Internal error: No binding for " ^ u)
      | Some r -> 
         (* Aux applies the continuation to the "return value" of the current dt *)
         let rec aux u (cont : coq_expr -> coq_expr) = function
           | Ctr (c,dts) -> 
              (* aux2 goes through the dts, enhancing the continuation to include the result of the head to the acc *)
              let rec aux2 acc = function 
                | [] -> cont (gApp ~explicit:true (gCtr c) (List.rev acc)) (* Something about type parameters? *)
                | h::t -> aux "" (fun hg -> aux2 (hg::acc) t) h 
              in aux2 [] dts
           | Undef dt -> 
              register_arbitrary dt;
              let arb = arb.next_name () in
              bindGen (gInject "arbitrary") arb (fun arb -> cont (gVar arb))
           | Unknown u' -> 
              aux u' cont (UM.find u' k)
           | FixedInput -> cont (gVar (fresh_name u))
         in aux u (fun c -> returnGen (gSome c)) r
    in

    (* Iterate through constraints *)
    let rec recurse_type k = function
      | DProd (_, dt) -> recurse_type k dt (* Only introduces variables, doesn't constrain them *)
      | DArrow (dt1, dt2) -> 
         msgerr (str ("Darrowing: " ^ range_to_string (UM.find forGen k)) ++ fnl ());
         begin match dt1 with 
         | DTyCtr (c, dts) -> 
            if c == gen_ctr then 
            begin (* Recursively called constructor *)
              b := false;
              match List.filter (fun (i, dt) -> not (is_fixed k dt)) (List.mapi (fun i dt -> (i+1, dt)) dts) with (* +1 because of nth being 1-indexed *)
              | [] -> 
                 need_dec := true;
                 gMatch (gApp rec_dec_name (List.map (fun dt -> dt_to_coq_expr dt) dts))
                        [ (injectCtr "left", ["eq" ], fun _ -> recurse_type k dt2) 
                        ; (injectCtr "right", ["neq"], fun _ -> returnGen gNone) ]
              | [(i,DTyVar x)] -> 
                 if i == n then (* Recursive call *) begin
                   msgerr (str ("Variable is: " ^ ty_var_to_string x) ++ fnl ());
                   let args = List.map snd (List.filter (fun (i, _) -> not (i == n)) (List.mapi (fun i dt -> (i+1, dt_to_coq_expr dt)) dts)) in
                   bindGenOpt (gApp (gVar rec_name) (gVar size :: args)) (ty_var_to_string x) 
                           (fun _ -> recurse_type (fixVariable (ty_var_to_string x) k) dt2)
                             end
                 else failwith "Implement other generator modes for recursive call"
              | [(i, dt) ] -> failwith ("Internal error: not a variable to be generated for" ^ (dep_type_to_string dt)) 
              | _ -> failwith "Mode analysis failure: More than one arguments need generation"    
            end 
            else (* Random constructor *)
              failwith ("Do me!: " ^ (dep_type_to_string dt1) ^ " vs " ^ (ty_ctr_to_string gen_ctr))
         | _ -> failwith ("Constraints should only be type constructors. Found: " ^ (dep_type_to_string dt1))
         end
      | DTyCtr _ -> instantiate_unknown k forGen (* result *)
      | _ -> failwith "Wrong type" in

    let branch_gen = 
      let rec walk_matches = function
        | [] -> recurse_type map typ
        | m::ms -> construct_match m (walk_matches ms) in
      walk_matches matches
    in 
    
    (* Debugging resulting match *)
    UM.iter (fun x r -> msgerr (str ("Bound: " ^ x ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) map;
    EqSet.iter (fun (u,u') -> msgerr (str (Printf.sprintf "Eq: %s = %s\n" u u') ++ fnl())) eqs;
    List.iter (fun m -> msgerr (str (matcher_to_string m) ++ fnl ())) matches;

    msgerr (str "Generated..." ++ fnl ());
    debug_coq_expr branch_gen;
    (* End debugging *)

    (branch_gen ,!b)
  in

  (*  List.iter (fun x -> ignore (handle_branch x)) ctrs;  *)

  let aux_arb rec_name size vars = 
    gMatch (gVar size) 
           [ (injectCtr "O", [], 
              fun _ -> (* Base cases *) 
              let base_branches = List.map fst (List.filter (fun (_, b) -> b) (List.map (handle_branch size rec_name) ctrs)) in
              uniform_backtracking base_branches
             )
           ; (injectCtr "S", ["size'"], 
              fun [size'] -> 
              let all_branches = List.map (fun x -> fst (handle_branch size' rec_name x)) ctrs in
              uniform_backtracking all_branches
             )
           ] in

  let generator_body = gRecFunInWithArgs
                    ~assumType:(gen_type)
                    "aux_arb" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
                    (fun (rec_name, size::vars) -> aux_arb rec_name size vars) 
                    (fun rec_name -> gFun ["size"] 
                                    (fun [size] -> gApp (gVar rec_name) 
                                                        (gVar size :: List.map (fun n -> gVar (fresh_name n)) input_names)
                                    ))
  in
  gRecord [("arbitrarySizeST", generator_body)]
