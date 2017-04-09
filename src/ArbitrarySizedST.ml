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
open Feedback
open Unify

let need_dec = ref false

(* Advanced Generators *)
let arbitrarySizedST gen_ctr dep_type gen_type ctrs input_names inputs n register_arbitrary =
  let gen = mk_name_provider "gen" in
  let dec = mk_name_provider "dec" in
  let arb = mk_name_provider "arb" in
  let input_names = List.map fresh_name input_names in

  let forGen = Unknown.from_string "_forGen" in

  let rec inputWithGen i l = 
    if i <= 1 then forGen :: l
    else let (h::t) = l in h :: (inputWithGen (i-1) t) in

  (* Handling a branch: returns the generator and a boolean (true if base branch) *)
  let handle_branch size rec_name (c : dep_ctr) : (coq_expr * bool) = 
    let (ctr, typ) = c in
    let b = ref true in 

    msg_debug (str "Debug branch" ++ fnl ());

    (* add unknowns in environment *)
    let register_unknowns map = 
      let rec aux map = function
        | DArrow (dt1, dt2) -> aux map dt2
        | DProd ((x, dt1), dt2) -> aux (UM.add x (Undef dt1) map) dt2
        | _ -> map in
      aux map typ
    in

    let init_map = UM.add forGen (Undef (nthType n dep_type)) 
                                 (List.fold_left (fun m n -> UM.add n FixedInput m) 
                                    (register_unknowns UM.empty) input_names) 
    in

    msg_debug (str ("Calculating ranges: " ^ dep_type_to_string (dep_result_type typ)) ++ fnl ());
    
    let ranges = match dep_result_type typ with
      | DTyCtr (_, dts) -> List.map convert_to_range dts
      | _ -> failwith "Not the expected result type" in
    let inputsWithGen = inputWithGen n input_names in

    (* Debugging init map *)
    msg_debug (str ("Handling branch: " ^ dep_type_to_string typ) ++ fnl ());
    UM.iter (fun x r -> msg_debug (str ("Bound: " ^ (var_to_string x) ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) init_map;
    dep_fold_ty (fun _ dt1 -> msg_debug (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
                (fun _ _ dt1 -> msg_debug (str (Printf.sprintf "%s : %b\n" (dep_type_to_string dt1) (is_dep_type dt1)) ++ fnl()))
                (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) typ;
    (* End debugging *)

    (* unify inputs and gen with result type *)
    match foldM (fun (k, eqs, ms) (r, n) -> unify k (Unknown n) r eqs >>= fun (k', _, eqs', ms') ->
                  Some (k', eqs', ms @ ms')
                ) (Some (init_map, EqSet.empty, [])) (List.combine ranges inputsWithGen) with
    | None -> failwith "Matching result type error" 
    | Some (map, eqs, matches) -> 

      (* Process check map *)
      let process_checks k cmap x opt g cont = 
        match lookup_checks (DTyVar x) cmap with
        | Some checks -> 
          (* Remove checks from cmap *)
          let cmap' = CMap.remove (DTyVar x) cmap in
          bindGenOpt (gApp (gInject (if opt then "suchThatMaybeOpt" else "suchThatMaybe"))
                        [ g (* Use the generator provided for base generator *)
                        ; gFun [var_to_string x] (fun [x] -> 
                              gApp (gInject ("List.forallb"))
                                [ gFun ["b"] (fun [b] -> gNot (decToBool (gVar b)))
                                ; gList (List.map (fun chk -> chk (gVar x)) checks)
                                ]
                            )
                        ])
            (var_to_string x)
            (fun x -> cont (fixVariable x k) cmap' x)
        | None -> 
          (if opt then bindGenOpt else bindGen) g (var_to_string x) 
            (fun x -> cont (fixVariable x k) cmap x)
      in

      (* Function to instantiate a single range *)
      (* It also uses any checks present in the check-map *)
      let rec instantiate_range_cont (k : umap) (cmap : cmap) (parent : unknown) (cont : umap -> cmap -> coq_expr -> coq_expr) = function
        | Ctr (c,rs) -> 
          (* aux2 goes through the dts, enhancing the continuation to include the result of the head to the acc *)
          let rec traverse_ranges k cmap acc = function 
            | [] -> cont k cmap (gApp ~explicit:true (gCtr c) (List.rev acc)) (* Something about type parameters? *)
            | r::rest -> instantiate_range_cont k cmap Unknown.undefined (fun k cmap hg -> traverse_ranges k cmap (hg::acc) rest) r
          in traverse_ranges k cmap [] rs
        | Undef dt -> begin
            register_arbitrary dt; 
            process_checks k cmap parent false (gInject "arbitrary")
              (fun k' cmap' x -> cont k' cmap' (gVar x))
          end
        | Unknown u -> instantiate_range_cont k cmap u cont (UM.find u k)
        | FixedInput -> cont k cmap (gVar parent)
      in 

      (* Only used as a finalizer - discards k/cmap *)
      let instantiate_range k cmap r = 
        instantiate_range_cont k cmap Unknown.undefined (fun k cmap c -> returnGen (gSome c)) r
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
      let rec handle_TyCtr (pos : bool) (c : ty_ctr) (dts : dep_type list)
                (k : umap) (cmap : cmap) (dt2 : dep_type) (rec_name : var) =
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
          let body_cont = recurse_type k cmap dt2 in
          let body_fail = returnGen gNone in

          (* Perform the check - rec_dec_name is in scope *)
          gMatch (checker (List.map (fun dt -> dt_to_coq_expr k dt) dts))
            [ (injectCtr "left", ["eq" ] , fun _ -> if pos then body_cont else body_fail)
            ; (injectCtr "right", ["neq"], fun _ -> if pos then body_fail else body_cont) 
            ]

        | [(i, DTyVar x)] -> (* Single variable to be generated for *)
          if i == n && c == gen_ctr && pos then begin (* Recursive call *)
            b := false;
            let args = List.map snd (List.filter (fun (i, _) -> not (i == n)) (List.mapi (fun i dt -> (i+1, dt_to_coq_expr k dt)) dts)) in
            process_checks k cmap x 
              (* Generate using recursive function *)
              true
              (gApp (gVar rec_name) (gVar size :: args))
              (fun k' cmap' x -> recurse_type k' cmap' dt2)
          end
          else if pos then begin (* Generate using "arbitrarySizeST" and annotations for type *)
            if c = gen_ctr then b := false;
            (* @arbitrarySizeST {A} (P : A -> Prop) {Instance} (size : nat) -> G (option A) *)
            let generator = 
              gApp ~explicit:true (gInject "arbitrarySizeST")
                [ hole (* Implicit argument - type A *)
                ; gFun [var_to_string x] (fun [x] -> 
                      gApp (gTyCtr c) (List.map (fun (j, dt) -> 
                          (* Replace the i-th variable with x - we're creating fun x => c dt_1 dt_2 ... x dt_{i+1} ... *)
                          if i == j then gVar x else dt_to_coq_expr k dt
                        ) numbered_dts))
                ; hole (* Implicit instance *)
                ; gVar size ]
            in 
            process_checks k cmap x true generator 
              (fun k' cmap' x' -> recurse_type k' cmap' dt2)
          end
          else (* Negation. Since we expect the *positive* versions to be sparse, we can use suchThatMaybe for negative *)
            (* TODO: something about size for backtracking? *)
            let new_check = fun x -> checker (List.map (fun (j,dt) -> if i == j then x else dt_to_coq_expr k dt) numbered_dts) in
            let cmap' = match lookup_checks (DTyVar x) cmap with 
              | Some checks -> CMap.add (DTyVar x) (new_check :: checks) cmap
              | _ -> CMap.add (DTyVar x) [new_check] cmap in
            recurse_type k cmap' dt2
        | [(i, dt) ] -> failwith ("Internal error: not a variable to be generated for" ^ (dep_type_to_string dt)) 

        (* Multiple arguments to be generated for. Generalized arbitrarySizeST? *)
        | filtered -> if pos then begin
            (* For now, check if n is in the filtered list *)
            match List.filter (fun (i,dt) -> i == n) filtered with 
            | [(_, DTyVar x)] -> 
              b := false; 
              (* Every other variable generated using "arbitrary" *)
              let rec build_arbs k cmap acc = function 
                | [] -> 
                  (* base case - recursive call *)
                  if pos then 
                    let generator = gApp (gVar rec_name) (gVar size :: List.rev acc) in
                    process_checks k cmap x true generator 
                      (fun k' cmap' x' -> recurse_type k' cmap' dt2)
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
            | _ -> failwith "Mode analysis failure"
          end
          else failwith "TODO: Negation with many things to be generated"

      (* Dispatcher for constraints *)
      and handle_dt pos dt1 dt2 k cmap rec_name = 
        match dt1 with 
        | DTyCtr (c,dts) -> 
          handle_TyCtr pos c dts k cmap dt2 rec_name 
        | DNot dt -> 
          handle_dt (not pos) dt dt2 k cmap rec_name
        | _ -> failwith "Constraints should be type constructors/negations"

      (* Iterate through constraints *)
      and recurse_type k cmap = function
        | DProd (_, dt) -> (* Only introduces variables, doesn't constrain them *)
          recurse_type k cmap dt 
        | DArrow (dt1, dt2) -> 
          msg_debug (str ("Darrowing: " ^ range_to_string (UM.find forGen k)) ++ fnl ());
          handle_dt true dt1 dt2 k cmap rec_name
        | DTyCtr _ -> (* result *) 
          instantiate_range k cmap (Unknown forGen) (* result *)
        | _ -> failwith "Wrong type" in

      (* TODO: Whenn handling parameters, this might need to add additional arguments *)
      let handle_equalities eqs (c : coq_expr) = 
        EqSet.fold (fun (u1,u2) c -> 
            let check = gApp ~explicit:true (gInject "dec") [ gApp (gInject "eq") [gVar u1; gVar u2] 
                                                            ; hole ] in
            gMatch check 
              [ (injectCtr "left" , ["eq" ], fun _ -> c)
              ; (injectCtr "right", ["neq"], fun _ -> returnGen gNone) ]
          ) eqs c in

      let branch_gen = 
        let rec walk_matches = function
          | [] -> handle_equalities eqs (recurse_type map CMap.empty typ)
          | (u,m)::ms -> begin 
              msg_debug (str (Printf.sprintf "Processing Match: %s @ %s" (Unknown.to_string u) (matcher_pat_to_string m)) ++ fnl ());
              construct_match (gVar u) ~catch_all:(Some (returnGen gNone)) [(m,walk_matches ms)]
            end in
        (* matches are the matches returned by unification with the result type *)
        walk_matches matches
      in 

      (* Debugging resulting match *)
      UM.iter (fun x r -> msg_debug (str ("Bound: " ^ var_to_string x ^ " to Range: " ^ (range_to_string r)) ++ fnl ())) map;
      EqSet.iter (fun (u,u') -> msg_debug (str (Printf.sprintf "Eq: %s = %s\n" (Unknown.to_string u) (Unknown.to_string u')) ++ fnl())) eqs;
      List.iter (fun (u,m) -> msg_debug (str ((Unknown.to_string u) ^ (matcher_pat_to_string m)) ++ fnl ())) matches;

      msg_debug (str "Generated..." ++ fnl ());
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

  let generator_body : coq_expr =
    gRecFunInWithArgs
      ~assumType:(gen_type)
      "aux_arb" (gArg ~assumName:(gVar (fresh_name "size")) () :: inputs) 
      (fun (rec_name, size::vars) -> aux_arb rec_name size vars)
      (fun rec_name -> gFun ["size"] 
          (fun [size] -> gApp (gVar rec_name) 
              (gVar size :: List.map gVar input_names)
          ))
  in

  msg_debug (fnl () ++ fnl () ++ str "`Final body produced:" ++ fnl ());
  debug_coq_expr generator_body;                       
  msg_debug (fnl ());
  gRecord [("arbitrarySizeST", generator_body)]
