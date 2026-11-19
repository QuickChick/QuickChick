(* Quote scheduler terms to QuickChick.SchedulingPolicy views. The views are
   PolicyViews values: a compiled policy receives them directly, and the
   renderers below turn them into Rocq terms for a policy evaluated in Rocq.
   Unknown local types remain opaque; names and binder identities are
   preserved. *)
open GenericLib
open PolicyViews

(* Views hold strings as character lists, as Rocq extracts them. *)
let chars s = List.init (String.length s) (String.get s)
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
  RocqExpr.gApp
    (RocqExpr.gInject ("QuickChick.SchedulingPolicy." ^ name)) args

