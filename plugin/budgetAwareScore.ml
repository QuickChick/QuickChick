(* Completed BudgetAware scoring, following Specimen 121cf234/Scoring.lean.
   Search bounds are deliberately separate from this exact leaf scorer. *)

open GenericLib

type density = Total | Partial | Backtracking | Checking
type locality = Internal | External | SameIndExt

type score = {
  selectivity : int;
  density : density;
  fabrication : int;
  locality : locality;
  input_check_deps : int;
  var_deps : int;
}

type key = { relation : ty_ctr; output_indices : int list; derive_sort : derive_sort }
type dependency_request = { key : key; applied_args : rocq_constr list }

type context = {
  input_vars : var list;
  finite_pins : ty_ctr -> int list;
  completed_dependency : dependency_request -> score option;
}

let empty = {
  selectivity = 0; density = Total; fabrication = 0;
  locality = Internal; input_check_deps = 0; var_deps = 0;
}

let density_rank = function
  | Total -> 0 | Partial -> 1 | Backtracking -> 2 | Checking -> 3

let locality_rank = function
  | Internal -> 0 | External -> 1 | SameIndExt -> 2

let to_string score =
  let density = match score.density with
    | Total -> "Total" | Partial -> "Partial"
    | Backtracking -> "Backtracking" | Checking -> "Checking" in
  let locality = match score.locality with
    | Internal -> "Internal" | External -> "External"
    | SameIndExt -> "SameIndExt" in
  Printf.sprintf
    "selectivity=%d density=%s fabrication=%d locality=%s inputCheckDeps=%d varDeps=%d"
    score.selectivity density score.fabrication locality
    score.input_check_deps score.var_deps

let max_density a b = if density_rank a >= density_rank b then a else b
let max_locality a b = if locality_rank a >= locality_rank b then a else b

let combine a b = {
  selectivity = a.selectivity + b.selectivity;
  density = max_density a.density b.density;
  fabrication = a.fabrication + b.fabrication;
  locality = max_locality a.locality b.locality;
  input_check_deps = a.input_check_deps + b.input_check_deps;
  var_deps = a.var_deps + b.var_deps;
}

let compare a b = Stdlib.compare
  (a.selectivity, density_rank a.density, a.fabrication,
   locality_rank a.locality, a.input_check_deps, a.var_deps)
  (b.selectivity, density_rank b.density, b.fabrication,
   locality_rank b.locality, b.input_check_deps, b.var_deps)

let best_of = function
  | [] -> { empty with density = Partial }
  | first :: rest -> List.fold_left (fun best score ->
      if compare score best < 0 then score else best) first rest

let inductive_score leaves = List.fold_left (fun total alternatives ->
  combine total (best_of alternatives)) empty leaves

(* Specimen's varsInConstructorExpr preserves repeated occurrences. The
   existing variables_in_hypothesis helper removes duplicates, so it cannot
   be used for either dependency count. *)
let rec vars = function
  | DTyVar name -> [name]
  | DTyParam name -> [name]
  | DTyCtr (_, args) | DCtr (_, args) ->
    List.concat_map vars args
  | DApp (head, args) -> vars head @ List.concat_map vars args
  | _ -> []

(* Specimen intersects ground conclusion positions across all constructors.
   A missing or untranslatable constructor conservatively disables pinning. *)
let finite_pins_of_relation ((_, _, ctors, _) : rocq_relation) =
  let rec ground = function
    | DTyVar _ | DTyParam _ -> false
    | DTyCtr (_, args) | DCtr (_, args) ->
      List.for_all ground args
    | DApp ((DTyCtr _ | DCtr _) as head, args) ->
      ground head && List.for_all ground args
    | DApp _ -> false
    | DHole -> true
    | _ -> false in
  let rec conclusion = function
    | DProd (_, rest) | DArrow (_, rest) -> conclusion rest
    | DTyCtr (_, args) -> Some args
    | _ -> None in
  let rec intersect current = function
    | [] -> current
    | (_, typ) :: rest ->
      (match conclusion typ with
       | None -> None
       | Some args ->
         let flags = List.map ground args in
         let current = match current with
           | None -> flags
           | Some previous ->
             List.mapi (fun i flag -> flag &&
               (match List.nth_opt previous i with Some was -> was | None -> false))
               flags
             |> List.filteri (fun i _ -> i < List.length previous) in
         intersect (Some current) rest) in
  match intersect None ctors with
  | None -> []
  | Some flags -> List.filter_map (fun (i, flag) ->
      if flag then Some i else None) (List.mapi (fun i flag -> i, flag) flags)

(* Cache only for the lifetime of one derivation. A process-wide cache could
   retain declarations across Rocq undo/backtracking. Missing or unsupported
   relations have no pins, as in Specimen's analysis-failure fallback. *)
let finite_pins_with_lookup find_relation =
  let cache = Hashtbl.create 16 in
  fun name -> match Hashtbl.find_opt cache name with
    | Some pins -> pins
    | None ->
      let pins = try match find_relation name with
        | Some relation -> finite_pins_of_relation relation
        | None -> []
      with _ -> [] in
      Hashtbl.add cache name pins;
      pins

let finite_pins_from_environment () =
  finite_pins_with_lookup (fun name ->
    match ty_ctr_to_rocq_relations name with
    | None -> None
    | Some (index, relations) -> List.nth_opt relations index)

let source_args = function
  | SrcNonrec (DTyCtr (_, args)) -> Ok args
  | SrcNonrec (DTyParam _) -> Ok []
  | SrcNonrec _ -> Error "BudgetAware: unsupported nonrelation source"
  | SrcRec (_, args) | SrcMutrec (_, args) -> Ok args
  | SrcDef _ -> Error "BudgetAware: defined sources have no Specimen counterpart"

let source_relation = function
  | SrcNonrec (DTyCtr (name, args)) -> Some (name, args)
  | _ -> None

let source_locality key = function
  | SrcRec _ | SrcMutrec _ -> Internal
  | SrcNonrec (DTyCtr (name, _)) ->
    if ty_ctr_eq name key.relation then SameIndExt else External
  | SrcNonrec _ -> External
  | SrcDef _ -> External

let count_var_deps inputs src =
  match source_args src with
  | Error _ as error -> error
  | Ok args -> Ok (List.concat_map vars args |> List.fold_left (fun n v ->
      if List.mem v inputs then n else n + 1) 0)

let count_input_deps inputs src =
  match source_args src with
  | Error _ as error -> error
  | Ok args -> Ok (List.concat_map vars args |> List.fold_left (fun n v ->
      if List.mem v inputs then n + 1 else n) 0)

let output_indices args outputs =
  List.filter_map (fun output ->
    let rec find i = function
      | [] -> None
      | DTyVar v :: _ when v = output -> Some i
      | _ :: rest -> find (i + 1) rest in
    find 0 args) outputs

let is_checker key = key.derive_sort = D_Check || key.derive_sort = D_Enum

let step_dependencies key = function
  | S_ST (outputs, src, _) ->
    (match source_relation src with
     | None -> []
     | Some (name, args) ->
       let dep_key = { relation = name;
         output_indices = output_indices args (List.map fst outputs);
         derive_sort = key.derive_sort } in
       let primary = if dep_key = key then [] else
         [{ key = dep_key; applied_args = args }] in
       if is_checker key then
         let enum = { key = { dep_key with derive_sort = D_Enum };
           applied_args = args } in
         if List.mem enum primary then primary else primary @ [enum]
       else primary)
  | _ -> []

let required_dependencies key steps =
  List.concat_map (step_dependencies key) steps |> List.sort_uniq Stdlib.compare

(* Match and equality checks are stored alongside the scheduler's steps and
   prepended by the compiler. Score that same completed schedule. *)
let candidate_steps ((steps, _), matches, equalities) =
  let equality (left, right) =
    S_Check (SrcNonrec (DTyCtr (constructor_of_string "Coq.Init.Logic.eq",
      [DHole; DTyVar left; DTyVar right])), true) in
  List.map (fun (name, pattern) -> S_Match (name, pattern)) matches @
  List.map equality equalities @ steps

let required_candidate_dependencies key candidate =
  required_dependencies key (candidate_steps candidate)

let step_score context key = function
  | S_UC (_, src, _) ->
    (match source_args src with
     | Error _ as error -> error
     | Ok _ -> Ok { empty with density = Total;
         locality = source_locality key src;
         fabrication = if is_checker key then 1 else 0 })
  | S_Match _ -> Ok { empty with density = Backtracking }
  | S_Check (src, _) ->
    (match count_var_deps context.input_vars src,
      count_input_deps context.input_vars src with
     | Ok var_deps, Ok inputs -> Ok { empty with
         density = Checking; locality = source_locality key src;
         var_deps; input_check_deps = if var_deps > 0 then inputs else 0 }
     | Error message, _ | _, Error message -> Error message)
  | S_ST (outputs, src, _) ->
    let names = List.map fst outputs in
    (match count_var_deps (context.input_vars @ names) src with
     | Error _ as error -> error
     | Ok var_deps ->
       let locality = source_locality key src in
       let density, fabrication = match source_relation src with
         | None -> Partial, 0
         | Some (name, args) ->
           let indices = output_indices args names in
           let dep_key = { relation = name; output_indices = indices;
             derive_sort = key.derive_sort } in
           let request key = { key; applied_args = args } in
           let density = if dep_key = key then Partial else
             match context.completed_dependency (request dep_key) with
             | Some score -> score.density | None -> Partial in
           let fabrication = if is_checker key then
             match context.completed_dependency
               (request { dep_key with derive_sort = D_Enum }) with
             | Some score -> score.fabrication | None -> 0
             else 0 in
           density, fabrication in
       Ok { empty with density; fabrication; locality; var_deps })
  | S_Let _ -> Error "BudgetAware: let steps have no Specimen counterpart"

let score_schedule context key steps =
  let rec fold total = function
    | [] -> Ok total
    | step :: rest ->
      (match step_score context key step with
       | Error _ as error -> error
       | Ok score -> fold (combine total score) rest) in
  match fold empty steps with
  | Error _ as error -> error
  | Ok base ->
    let all_produced = ref [] in
    let produced_finitely = ref [] in
    let finitely_pinnable = ref [] in
    let add set name = if not (List.mem name !set) then set := name :: !set in
    List.iter (function
      | S_UC (name, _, _) -> add all_produced name
      | S_ST (outputs, src, _) ->
        List.iter (fun (name, _) -> add all_produced name) outputs;
        (match source_relation src with
         | None -> ()
         | Some (relation, args) ->
           let pins = context.finite_pins relation in
           List.iter (fun (name, _) ->
             if List.exists (fun i -> List.nth_opt args i = Some (DTyVar name)) pins
             then add produced_finitely name) outputs)
      | _ -> ()) steps;
    List.iter (function
      | S_ST (_, src, _) | S_Check (src, _) ->
        (match source_relation src with
         | None -> ()
         | Some (relation, args) ->
           List.iter (fun i -> match List.nth_opt args i with
             | Some (DTyVar name) -> add finitely_pinnable name
             | _ -> ()) (context.finite_pins relation))
      | _ -> ()) steps;
    let selectivity = List.fold_left (fun n name ->
      if List.mem name !all_produced &&
         not (List.mem name !produced_finitely)
      then n + 1 else n) 0 !finitely_pinnable in
    Ok { base with selectivity }

let score_candidate context key candidate =
  score_schedule context key (candidate_steps candidate)

(* Grouped search: selectivity, fabrication and both dependency counts add;
   density and locality take the worse value. Scoring footprint-disjoint
   groups separately is separable because every step naming a variable lies
   in that variable's group, so selectivity's per-variable sets do not
   overlap; shared match and equality steps produce or pin no group variable. *)
let group_policy : score GroupedScore.policy =
  let open GroupedScore in
  let field kind project = kind, (fun a b -> Stdlib.compare (project a) (project b)) in
  { unit = empty; combine;
    fields = [
      field Additive (fun s -> s.selectivity);
      field Extremal (fun s -> density_rank s.density);
      field Additive (fun s -> s.fabrication);
      field Extremal (fun s -> locality_rank s.locality);
      field Additive (fun s -> s.input_check_deps);
      field Additive (fun s -> s.var_deps) ] }
