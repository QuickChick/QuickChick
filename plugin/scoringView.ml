(* Quote scheduler terms to QuickChick.SchedulingPolicy views. The views are
   PolicyViews values: a compiled policy receives them directly, and the
   renderers below turn them into Rocq terms for a policy evaluated in Rocq.
   Unknown local types remain opaque; names and binder identities are
   preserved. *)
open GenericLib
open PolicyViews

(* Views hold strings as character lists, as Rocq extracts them. *)
let chars s = List.init (String.length s) (String.get s)
let string_of_chars cs = String.init (List.length cs) (List.nth cs)

type scope = { names : (var * int) list; next : int }

let scope names =
  if List.length names <> List.length (List.sort_uniq Stdlib.compare names) then
    invalid_arg "SchedulingPolicy: duplicate locals in initial scope";
  { names = List.mapi (fun id name -> name, id) names;
    next = List.length names }

let bind scope name =
  let id = scope.next in
  id, { names = (name, id) :: scope.names; next = id + 1 }

let lookup scope name =
  match List.assoc_opt name scope.names with
  | Some id -> Ok (TLocal id)
  | None -> Error ("SchedulingPolicy: unbound local " ^ var_to_string name)

(* Resolve at quotation time, so a later import or shadowing does not change
   the identity presented to a policy. *)
let global_name name =
  let reference = try Nametab.locate name with Not_found ->
    failwith ("SchedulingPolicy: unresolved global " ^ Libnames.string_of_qualid name) in
  Libnames.string_of_qualid
    (Libnames.qualid_of_path (Nametab.path_of_global reference))

let ( let* ) = Result.bind

let rec map_result f = function
  | [] -> Ok []
  | x :: rest -> let* y = f x in let* ys = map_result f rest in Ok (y :: ys)

let rec quote_pattern ~global scope (pattern : GenericLib.pat) =
  match pattern with
  | GenericLib.PWild -> Ok (PWild, scope)
  | GenericLib.PParam -> Ok (PParameter, scope)
  | GenericLib.PVar name ->
    let id, scope = bind scope name in
    Ok (PLocal id, scope)
  | GenericLib.PCtr (name, arguments) ->
    let rec loop scope acc = function
      | [] -> Ok (PConstructor (chars (global name), List.rev acc), scope)
      | pattern :: rest ->
        let* view, scope = quote_pattern ~global scope pattern in
        loop scope (view :: acc) rest in
    loop scope [] arguments

(* A completed schedule already gives every local a unique name. Pattern
   variables refer to those ids, including in steps following a match. *)
let rec quote_existing_pattern ~global scope = function
  | GenericLib.PWild -> Ok PWild
  | GenericLib.PParam -> Ok PParameter
  | GenericLib.PVar name ->
    (match lookup scope name with
     | Ok (TLocal id) -> Ok (PLocal id)
     | Ok _ -> assert false
     | Error _ as error -> error)
  | GenericLib.PCtr (name, arguments) ->
    let* args = map_result (quote_existing_pattern ~global scope) arguments in
    Ok (PConstructor (chars (global name), args))

let rec quote_term ~global scope term =
  let rec quote_list scope acc = function
    | [] -> Ok (List.rev acc, scope)
    | term :: rest ->
      let* view, scope = quote_term ~global scope term in
      quote_list scope (view :: acc) rest in
  match term with
  | DTyVar name | DTyParam name ->
    let* view = lookup scope name in Ok (view, scope)
  | DTyCtr (name, args) | DCtr (name, args) ->
    (match quote_list scope [] args with
     | Error _ as error -> error
     | Ok ([], scope) when List.mem (Libnames.string_of_qualid name)
           ["Type"; "Prop"; "Set"] ->
       Ok (TSort (chars (Libnames.string_of_qualid name)), scope)
     | Ok ([], scope) -> Ok (TGlobal (chars (global name)), scope)
     | Ok (args, scope) -> Ok (TApply (TGlobal (chars (global name)), args), scope))
  | DApp (head, args) ->
    let* head, scope = quote_term ~global scope head in
    let* args, scope = quote_list scope [] args in
    Ok (TApply (head, args), scope)
  | DArrow (domain, codomain) ->
    let* domain, scope = quote_term ~global scope domain in
    let* codomain, scope = quote_term ~global scope codomain in
    Ok (TArrow (domain, codomain), scope)
  | DProd ((name, domain), body) ->
    let* domain, outer_scope = quote_term ~global scope domain in
    let id, inner_scope = bind outer_scope name in
    let* body, body_scope = quote_term ~global inner_scope body in
    Ok (TProduct (id, domain, body), { outer_scope with next = body_scope.next })
  | DLambda (name, domain, body) ->
    let* domain, outer_scope = quote_term ~global scope domain in
    let id, inner_scope = bind outer_scope name in
    let* body, body_scope = quote_term ~global inner_scope body in
    Ok (TLambda (id, domain, body), { outer_scope with next = body_scope.next })
  | DMatch (scrutinee, branches) ->
    let* scrutinee, scope = quote_term ~global scope scrutinee in
    let rec loop next acc = function
      | [] -> Ok (TMatch (scrutinee, List.rev acc), { scope with next })
      | (pattern, body) :: rest ->
        let* pattern, branch_scope = quote_pattern ~global { scope with next } pattern in
        let* body, branch_scope = quote_term ~global branch_scope body in
        loop branch_scope.next ((pattern, body) :: acc) rest in
    loop scope.next [] branches
  | DNot body ->
    let* body, scope = quote_term ~global scope body in
    Ok (TNot body, scope)
  | DHole -> Ok (TImplicitHole, scope)

let quote_closed ~global scope term =
  let* view, _ = quote_term ~global scope term in Ok view

let local_id scope name =
  match lookup scope name with
  | Ok (TLocal id) -> Ok id
  | Ok _ -> assert false
  | Error _ as error -> error

let collect_ids scope names = map_result (local_id scope) names

let source_kind = function
  | SrcNonrec _ -> External
  | SrcRec _ -> SelfRecursive
  | SrcMutrec _ -> MutualRecursive
  | SrcDef _ -> DefinedSource

let rec free_vars_term = function
  | DTyVar name | DTyParam name -> [name]
  | DTyCtr (_, args) | DCtr (_, args) -> List.concat_map free_vars_term args
  | DApp (head, args) ->
    free_vars_term head @ List.concat_map free_vars_term args
  | DArrow (domain, body) -> free_vars_term domain @ free_vars_term body
  | DProd ((name, domain), body) | DLambda (name, domain, body) ->
    free_vars_term domain @ List.filter ((<>) name) (free_vars_term body)
  | DMatch (head, branches) ->
    free_vars_term head @ List.concat_map (fun (pattern, body) ->
      List.filter (fun name -> not (List.mem name (pat_vars pattern)))
        (free_vars_term body)) branches
  | DNot body -> free_vars_term body
  | DHole -> []

let source_variables = function
  | SrcNonrec term -> free_vars_term term
  | SrcRec (_, args) | SrcMutrec (_, args) | SrcDef (_, args) ->
    List.concat_map free_vars_term args

let step_variables = function
  | S_Check (source, _) -> source_variables source
  | S_UC (name, source, _) -> name :: source_variables source
  | S_ST (outputs, source, _) ->
    List.map fst outputs @ List.concat_map (fun (_, typ) -> free_vars_term typ) outputs
    @ source_variables source
  | S_Match (name, pattern) -> name :: pat_vars pattern
  | S_Let (name, value) -> name :: free_vars_term value

(* `inputs` is the set of variables already bound when the source runs.
   A producer's output variables are excluded by the caller. *)
let quote_source ~global ~finite_pins scope ~outputs source =
  let args = match source with
    | SrcNonrec term -> [term]
    | SrcRec (_, args) | SrcMutrec (_, args) | SrcDef (_, args) -> args in
  let inputs = List.concat_map free_vars_term args
    |> List.sort_uniq Stdlib.compare
    |> List.filter (fun name -> not (List.mem name outputs)) in
  let pins = match source with
    | SrcNonrec (DTyCtr (relation, args)) ->
      List.filteri (fun index _ -> List.mem index (finite_pins relation)) args
      |> List.concat_map free_vars_term
      |> List.sort_uniq Stdlib.compare
    | _ -> [] in
  let* application = match source with
    | SrcRec (name, args) | SrcMutrec (name, args) | SrcDef (name, args) ->
      let* args = map_result (quote_closed ~global scope) args in
      Ok (TApply (TGenerated (chars (var_to_string name)), args))
    | SrcNonrec term -> quote_closed ~global scope term in
  let* inputs = collect_ids scope inputs in
  let* pins = collect_ids scope pins in
  Ok { source_category = source_kind source; source_application = application;
       source_inputs = inputs; source_finite_pins = pins }

let producer_mode = function
  | PS_G -> Generator
  | PS_E -> Enumerator

let quote_step ~global ~finite_pins scope step =
  let source ~outputs src = quote_source ~global ~finite_pins scope ~outputs src in
  match step with
  | S_Check (src, positive) ->
    let* src = source ~outputs:[] src in Ok (CheckStep (src, positive))
  | S_UC (name, src, mode) ->
    let* id = local_id scope name in
    let* src_view = source ~outputs:[name] src in
    let* typ = match src with
      | SrcNonrec typ -> quote_closed ~global scope typ
      | _ -> Ok (TOpaque id) in
    Ok (Unconstrained ({ local_id = id; local_type = typ }, src_view, producer_mode mode))
  | S_ST (outputs, src, mode) ->
    let* src_view = source ~outputs:(List.map fst outputs) src in
    let* outputs = map_result (fun (name, typ) ->
      let* id = local_id scope name in
      let* typ = match typ with
        | DHole -> Ok (TOpaque id)
        | _ -> quote_closed ~global scope typ in
      Ok { local_id = id; local_type = typ }) outputs in
    Ok (SuchThat (outputs, src_view, producer_mode mode))
  | S_Match (name, pattern) ->
    let* id = local_id scope name in
    let* pattern = quote_existing_pattern ~global scope pattern in
    Ok (MatchStep (id, pattern))
  | S_Let (name, value) ->
    let* id = local_id scope name in
    let* value = quote_closed ~global scope value in
    Ok (LetStep ({ local_id = id; local_type = TOpaque id }, value))

let quote_schedule ~global ~finite_pins ~grade scope steps result =
  let* steps = map_result (fun (step, g) ->
    let* view = quote_step ~global ~finite_pins scope step in
    Ok (view, grade g)) steps in
  let* result = match result with
    | None -> Ok None
    | Some term -> let* view = quote_closed ~global scope term in Ok (Some view) in
  Ok { schedule_steps = steps; schedule_result = result }

let derive_mode = function
  | D_Gen -> Generate
  | D_Enum -> Enumerate
  | D_Check -> Check
  | D_Thm -> TestTheorem

let quote_spec ~global scope application outputs mode constrained =
  let* application = quote_closed ~global scope application in
  Ok { spec_application = application; spec_outputs = outputs;
       spec_mode = derive_mode mode; spec_constrained = constrained }

type dependency_status = Supplied | Pending | InProgress | Completed of Obj.t

(* The score context of a constructor of [relation], whose result arguments
   are [result_vars] and outputs [outputs]. *)
let quote_context ~global scope relation result_vars local_types
    outputs mode constrained dependencies =
  let application = DTyCtr (relation,
    List.map (fun (name, _) -> DTyVar name) result_vars) in
  let inputs = List.map fst result_vars
    |> List.filter (fun name -> not (List.mem name outputs)) in
  let root_output_indices = List.filter_map (fun (index, (name, _)) ->
    if List.mem name outputs then Some index else None)
    (List.mapi (fun index entry -> index, entry) result_vars) in
  if List.length root_output_indices <> List.length outputs then
    Error "SchedulingPolicy: an output is missing from the root telescope"
  else
    let* spec = quote_spec ~global scope application root_output_indices mode constrained in
    let* inputs = collect_ids scope inputs in
    let* locals = map_result (fun (name, typ) ->
      let* id = local_id scope name in
      let* typ = quote_closed ~global scope typ in
      Ok { local_id = id; local_type = typ }) local_types in
    let* dependencies = map_result
      (fun ((application, outputs, mode, constrained), status) ->
        let* spec = quote_spec ~global scope application outputs mode constrained in
        Ok (spec, match status with
          | Supplied -> PolicyViews.SuppliedInstance
          | Pending -> PolicyViews.Pending
          | InProgress -> PolicyViews.InProgress
          | Completed score -> PolicyViews.Completed score)) dependencies in
    (* A step's dependency is the request with its source application, in
       the step's mode. A step that calls nothing has a static state. *)
    let step_dependency step =
      let call = match step with
        | Unconstrained (_, source, Generator) | SuchThat (_, source, Generator) ->
          Some (source.source_application, Generate)
        | Unconstrained (_, source, Enumerator) | SuchThat (_, source, Enumerator) ->
          Some (source.source_application, Enumerate)
        | CheckStep (source, _) -> Some (source.source_application, Check)
        | MatchStep _ | LetStep _ -> None in
      match call with
      | None -> PolicyViews.SuppliedInstance
      | Some (application, mode) ->
        match List.find_opt (fun (spec, _) ->
            spec.spec_application = application && spec.spec_mode = mode) dependencies with
        | Some (_, state) -> state
        | None -> PolicyViews.Pending in
    Ok { current_spec = spec; locals; original_inputs = inputs; dependencies; step_dependency }

(* Render views as Rocq expressions, for a policy evaluated in Rocq.
   Constructor applications are elaborated and checked in the current proof
   environment by the caller. *)
let constructor name args =
  CoqExpr.gApp
    (CoqExpr.gInject ("QuickChick.SchedulingPolicy." ^ name)) args

let str cs = CoqExpr.gStr (string_of_chars cs)
let int_list ids = CoqExpr.gList (List.map CoqExpr.gInt ids)
let bool b = if b then CoqExpr.g_true else CoqExpr.g_false

let rec pattern_expression = function
  | PWild -> constructor "PWild" []
  | PParameter -> constructor "PParameter" []
  | PLocal id -> constructor "PLocal" [CoqExpr.gInt id]
  | PConstructor (name, args) ->
    constructor "PConstructor"
      [str name; CoqExpr.gList (List.map pattern_expression args)]

let rec term_expression = function
  | TLocal id -> constructor "TLocal" [CoqExpr.gInt id]
  | TGlobal name -> constructor "TGlobal" [str name]
  | TSort name -> constructor "TSort" [str name]
  | TGenerated name -> constructor "TGenerated" [str name]
  | TImplicitHole -> constructor "TImplicitHole" []
  | TApply (head, args) ->
    constructor "TApply"
      [term_expression head; CoqExpr.gList (List.map term_expression args)]
  | TArrow (domain, codomain) ->
    constructor "TArrow" [term_expression domain; term_expression codomain]
  | TProduct (id, domain, body) ->
    constructor "TProduct"
      [CoqExpr.gInt id; term_expression domain; term_expression body]
  | TLambda (id, domain, body) ->
    constructor "TLambda"
      [CoqExpr.gInt id; term_expression domain; term_expression body]
  | TMatch (scrutinee, branches) ->
    constructor "TMatch"
      [term_expression scrutinee;
       CoqExpr.gList (List.map (fun (pattern, body) ->
         CoqExpr.gPair (pattern_expression pattern, term_expression body))
         branches)]
  | TNot body -> constructor "TNot" [term_expression body]
  | TOpaque handle -> constructor "TOpaque" [CoqExpr.gInt handle]

let source_kind_expression = function
  | External -> constructor "External" []
  | SelfRecursive -> constructor "SelfRecursive" []
  | MutualRecursive -> constructor "MutualRecursive" []
  | DefinedSource -> constructor "DefinedSource" []

let source_view_expression s =
  constructor "Build_source_view"
    [source_kind_expression s.source_category; term_expression s.source_application;
     int_list s.source_inputs; int_list s.source_finite_pins]

let local_expression l =
  constructor "Build_local_view" [CoqExpr.gInt l.local_id; term_expression l.local_type]

let producer_expression = function
  | Generator -> constructor "Generator" []
  | Enumerator -> constructor "Enumerator" []

let step_view_expression = function
  | CheckStep (src, positive) -> constructor "CheckStep" [source_view_expression src; bool positive]
  | Unconstrained (l, src, mode) ->
    constructor "Unconstrained" [local_expression l; source_view_expression src; producer_expression mode]
  | SuchThat (ls, src, mode) ->
    constructor "SuchThat"
      [CoqExpr.gList (List.map local_expression ls); source_view_expression src;
       producer_expression mode]
  | MatchStep (id, pattern) -> constructor "MatchStep" [CoqExpr.gInt id; pattern_expression pattern]
  | LetStep (l, value) -> constructor "LetStep" [local_expression l; term_expression value]

let density_expression = function
  | Checking -> constructor "Checking" []
  | Backtracking -> constructor "Backtracking" []
  | Neutral -> constructor "Neutral" []
  | Partial -> constructor "Partial" []
  | Total -> constructor "Total" []

let schedule_view_expression s =
  constructor "Build_schedule_view"
    [CoqExpr.gList (List.map (fun (step, grade) ->
       CoqExpr.gPair (step_view_expression step, density_expression grade)) s.schedule_steps);
     (match s.schedule_result with
      | None -> CoqExpr.gNone'
      | Some term -> CoqExpr.gSome' (term_expression term))]

let derive_mode_expression = function
  | Generate -> constructor "Generate" []
  | Enumerate -> constructor "Enumerate" []
  | Check -> constructor "Check" []
  | TestTheorem -> constructor "TestTheorem" []

let spec_view_expression s =
  constructor "Build_spec_view"
    [term_expression s.spec_application; int_list s.spec_outputs;
     derive_mode_expression s.spec_mode; bool s.spec_constrained]

(* The expression-producing interface used by the Rocq-evaluated probes. *)
let step_expression ~global ~finite_pins scope step =
  Result.map step_view_expression (quote_step ~global ~finite_pins scope step)

let schedule_expression ~global ~finite_pins ~grade scope steps result =
  Result.map schedule_view_expression
    (quote_schedule ~global ~finite_pins ~grade scope steps result)

let dependency_context_expression ~global scope relation result_vars local_types
    outputs mode constrained dependencies =
  let* context = quote_context ~global scope relation result_vars local_types
    outputs mode constrained dependencies in
  Ok (spec_view_expression context.current_spec,
      CoqExpr.gList (List.map local_expression context.locals),
      int_list context.original_inputs,
      CoqExpr.gList (List.map (fun (spec, state) ->
        CoqExpr.gPair (spec_view_expression spec, match state with
          | PolicyViews.SuppliedInstance -> constructor "SuppliedInstance" []
          | _ -> constructor "Pending" [])) context.dependencies))

let score_one_schedule_expression scorer (spec, locals, inputs, dependencies)
    schedule =
  CoqExpr.gApp
    (CoqExpr.gInject "QuickChick.SchedulingPolicy.score_with_dependency_states")
    [CoqExpr.gInject scorer; spec; locals; inputs; dependencies; schedule]

(* The result remains a typed Rocq term: the plugin need not know a user's
   score representation. The returned sigma carries elaboration constraints. *)
let evaluate_term_in env sigma expression =
  let sigma, term = CoqExpr.interp_coq_expr_evars env sigma expression in
  if Evd.has_undefined sigma then
    Error "SchedulingPolicy: the selected scorer left unresolved evars"
  else
    let sigma, typ = Typing.type_of env sigma term in
    Ok (sigma, Vnorm.cbv_vm env sigma term typ, typ)

let evaluate_expression_in env sigma function_name argument =
  let expression = CoqExpr.gApp
    (CoqExpr.gInject function_name) [argument] in
  evaluate_term_in env sigma expression

let evaluate_expression env function_name argument =
  evaluate_expression_in env (Evd.from_env env) function_name argument

let compare_values_expression env sigma comparator_expression left right =
  let sigma, comparator = CoqExpr.interp_coq_expr_evars env sigma
    comparator_expression in
  let application = EConstr.mkApp (comparator, [|left; right|]) in
  let sigma, typ = Typing.type_of env sigma application in
  if Evd.has_undefined sigma then
    Error "SchedulingPolicy: the selected comparator left unresolved evars"
  else
    let comparison = match Nametab.locate
      (Libnames.qualid_of_string "Coq.Init.Datatypes.comparison") with
      | Names.GlobRef.IndRef ind -> ind
      | _ -> failwith "SchedulingPolicy: comparison is not an inductive" in
    match EConstr.kind sigma typ with
    | Constr.Ind (ind, _) when Environ.QInd.equal env ind comparison ->
      let value = Vnorm.cbv_vm env sigma application typ in
      let constructor name = match Nametab.locate
        (Libnames.qualid_of_string ("Coq.Init.Datatypes." ^ name)) with
        | Names.GlobRef.ConstructRef constructor -> constructor
        | _ -> failwith ("SchedulingPolicy: " ^ name ^ " is not a constructor") in
      (match EConstr.kind sigma value with
       | Constr.Construct (actual, _) ->
         if Environ.QConstruct.equal env actual (constructor "Lt") then
           Ok (sigma, -1)
         else if Environ.QConstruct.equal env actual (constructor "Eq") then
           Ok (sigma, 0)
         else if Environ.QConstruct.equal env actual (constructor "Gt") then
           Ok (sigma, 1)
         else Error "SchedulingPolicy: comparator returned another constructor"
       | _ -> Error "SchedulingPolicy: comparator did not reduce to a result")
    | _ -> Error "SchedulingPolicy: comparator must return comparison"

let compare_values env sigma function_name left right =
  compare_values_expression env sigma (CoqExpr.gInject function_name)
    left right

let compare_record_scores env sigma scorer left right =
  let comparator = CoqExpr.gApp
    (CoqExpr.gInject "QuickChick.SchedulingPolicy.compare_scores")
    [CoqExpr.gInject scorer] in
  compare_values_expression env sigma comparator left right

let evaluate env function_name view =
  evaluate_expression env function_name (term_expression view)

let nat_of_value env sigma typ term =
  let nat = match Nametab.locate
      (Libnames.qualid_of_string "Coq.Init.Datatypes.nat") with
    | Names.GlobRef.IndRef ind -> ind
    | _ -> failwith "SchedulingPolicy: nat does not resolve to an inductive" in
  let same_nat ind = Environ.QInd.equal env ind nat in
  let rec decode term = match EConstr.kind sigma term with
    | Constr.Construct ((ind, 1), _) when same_nat ind -> Some 0
    | Constr.App (head, [|argument|]) ->
      (match EConstr.kind sigma head, decode argument with
       | Constr.Construct ((ind, 2), _), Some n
           when same_nat ind && n < max_int -> Some (n + 1)
       | _ -> None)
    | _ -> None in
  match EConstr.kind sigma typ with
  | Constr.Ind (ind, _) when same_nat ind -> decode term
  | _ -> None
