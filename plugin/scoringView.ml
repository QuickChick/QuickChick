(* First stage of quoting scheduler terms to QuickChick.SchedulingPolicy.
   This representation is lossless for the supported symbolic fragment. *)
open NewGenericLib

type pattern_view =
  | PWild
  | PParameter
  | PLocal of int
  | PConstructor of string * pattern_view list

type term_view =
  | TLocal of int
  | TGlobal of string
  | TSort of string
  | TGenerated of string
  | TApply of term_view * term_view list
  | TArrow of term_view * term_view
  | TProduct of int * term_view * term_view
  | TLambda of int * term_view * term_view
  | TMatch of term_view * (pattern_view * term_view) list
  | TNot of term_view
  | TOpaque of int

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

let rec quote_pattern ~global scope (pattern : NewGenericLib.pat) =
  match pattern with
  | NewGenericLib.PWild -> Ok (PWild, scope)
  | NewGenericLib.PParam -> Ok (PParameter, scope)
  | NewGenericLib.PVar name ->
    let id, scope = bind scope name in
    Ok (PLocal id, scope)
  | NewGenericLib.PCtr (name, arguments) ->
    let rec loop scope acc = function
      | [] -> Ok (PConstructor (global name, List.rev acc), scope)
      | pattern :: rest ->
        (match quote_pattern ~global scope pattern with
         | Error _ as error -> error
         | Ok (view, scope) -> loop scope (view :: acc) rest) in
    loop scope [] arguments

let rec quote_term ~global scope term =
  let rec quote_list scope acc = function
    | [] -> Ok (List.rev acc, scope)
    | term :: rest ->
      (match quote_term ~global scope term with
       | Error _ as error -> error
       | Ok (view, scope) -> quote_list scope (view :: acc) rest) in
  match term with
  | DTyVar name | DTyParam name ->
    (match lookup scope name with
     | Ok view -> Ok (view, scope)
     | Error _ as error -> error)
  | DTyCtr (name, args) | DCtr (name, args) ->
    (match quote_list scope [] args with
     | Error _ as error -> error
     | Ok ([], scope) when List.mem (Libnames.string_of_qualid name)
           ["Type"; "Prop"; "Set"] ->
       Ok (TSort (Libnames.string_of_qualid name), scope)
     | Ok ([], scope) -> Ok (TGlobal (global name), scope)
     | Ok (args, scope) -> Ok (TApply (TGlobal (global name), args), scope))
  | DApp (head, args) ->
    (match quote_term ~global scope head with
     | Error _ as error -> error
     | Ok (head, scope) ->
       match quote_list scope [] args with
       | Error _ as error -> error
       | Ok (args, scope) -> Ok (TApply (head, args), scope))
  | DArrow (domain, codomain) ->
    (match quote_term ~global scope domain with
     | Error _ as error -> error
     | Ok (domain, scope) ->
       match quote_term ~global scope codomain with
       | Error _ as error -> error
       | Ok (codomain, scope) -> Ok (TArrow (domain, codomain), scope))
  | DProd ((name, domain), body) ->
    (match quote_term ~global scope domain with
     | Error _ as error -> error
     | Ok (domain, outer_scope) ->
       let id, inner_scope = bind outer_scope name in
       match quote_term ~global inner_scope body with
       | Error _ as error -> error
       | Ok (body, body_scope) ->
         Ok (TProduct (id, domain, body),
           { outer_scope with next = body_scope.next }))
  | DLambda (name, domain, body) ->
    (match quote_term ~global scope domain with
     | Error _ as error -> error
     | Ok (domain, outer_scope) ->
       let id, inner_scope = bind outer_scope name in
       match quote_term ~global inner_scope body with
       | Error _ as error -> error
       | Ok (body, body_scope) ->
         Ok (TLambda (id, domain, body),
           { outer_scope with next = body_scope.next }))
  | DMatch (scrutinee, branches) ->
    (match quote_term ~global scope scrutinee with
     | Error _ as error -> error
     | Ok (scrutinee, scope) ->
       let rec loop next acc = function
         | [] -> Ok (TMatch (scrutinee, List.rev acc), { scope with next })
         | (pattern, body) :: rest ->
           (match quote_pattern ~global { scope with next } pattern with
            | Error _ as error -> error
            | Ok (pattern, branch_scope) ->
              match quote_term ~global branch_scope body with
              | Error _ as error -> error
              | Ok (body, branch_scope) ->
                loop branch_scope.next ((pattern, body) :: acc) rest) in
       loop scope.next [] branches)
  | DNot body ->
    (match quote_term ~global scope body with
     | Error _ as error -> error
     | Ok (body, scope) -> Ok (TNot body, scope))
  | DHole -> Error "SchedulingPolicy: cannot quote an unresolved hole"

(* Build a Rocq expression for the symbolic view. Constructor applications
   are elaborated and checked in the current proof environment by the caller. *)
let constructor name args =
  GenericLib.gApp
    (GenericLib.gInject ("QuickChick.SchedulingPolicy." ^ name)) args

let rec pattern_expression = function
  | PWild -> constructor "PWild" []
  | PParameter -> constructor "PParameter" []
  | PLocal id -> constructor "PLocal" [GenericLib.gInt id]
  | PConstructor (name, args) ->
    constructor "PConstructor"
      [GenericLib.gStr name;
       GenericLib.gList (List.map pattern_expression args)]

let rec term_expression = function
  | TLocal id -> constructor "TLocal" [GenericLib.gInt id]
  | TGlobal name -> constructor "TGlobal" [GenericLib.gStr name]
  | TSort name -> constructor "TSort" [GenericLib.gStr name]
  | TGenerated name -> constructor "TGenerated" [GenericLib.gStr name]
  | TApply (head, args) ->
    constructor "TApply"
      [term_expression head; GenericLib.gList (List.map term_expression args)]
  | TArrow (domain, codomain) ->
    constructor "TArrow" [term_expression domain; term_expression codomain]
  | TProduct (id, domain, body) ->
    constructor "TProduct"
      [GenericLib.gInt id; term_expression domain; term_expression body]
  | TLambda (id, domain, body) ->
    constructor "TLambda"
      [GenericLib.gInt id; term_expression domain; term_expression body]
  | TMatch (scrutinee, branches) ->
    constructor "TMatch"
      [term_expression scrutinee;
       GenericLib.gList (List.map (fun (pattern, body) ->
         GenericLib.gPair (pattern_expression pattern, term_expression body))
         branches)]
  | TNot body -> constructor "TNot" [term_expression body]
  | TOpaque handle -> constructor "TOpaque" [GenericLib.gInt handle]

let local_id scope name =
  match lookup scope name with
  | Ok (TLocal id) -> Ok id
  | Ok _ -> assert false
  | Error _ as error -> error

let rec collect_ids scope = function
  | [] -> Ok []
  | name :: rest ->
    (match local_id scope name, collect_ids scope rest with
     | Ok id, Ok ids -> Ok (id :: ids)
     | Error _ as error, _ | _, (Error _ as error) -> error)

let int_list ids = GenericLib.gList (List.map GenericLib.gInt ids)

let source_kind_expression = function
  | SrcNonrec _ -> constructor "External" []
  | SrcRec _ -> constructor "SelfRecursive" []
  | SrcMutrec _ -> constructor "MutualRecursive" []
  | SrcDef _ -> constructor "DefinedSource" []

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
let source_expression ~global ~finite_pins scope ~outputs source =
  let name_args = function
    | SrcRec (name, args) | SrcMutrec (name, args) | SrcDef (name, args) ->
      Some (name, args)
    | SrcNonrec _ -> None in
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
  let application = match name_args source with
    | Some (name, args) ->
      let rec loop acc = function
        | [] -> Ok (TApply (TGenerated (var_to_string name), List.rev acc))
        | arg :: rest ->
          (match quote_term ~global scope arg with
           | Ok (view, _) -> loop (view :: acc) rest
           | Error _ as error -> error) in
      loop [] args
    | None ->
      let term = match source with SrcNonrec term -> term | _ -> assert false in
      (match quote_term ~global scope term with
       | Ok (view, _) -> Ok view
       | Error _ as error -> error) in
  match application, collect_ids scope inputs, collect_ids scope pins with
  | Ok application, Ok inputs, Ok pins ->
    Ok (constructor "Build_source_view"
      [source_kind_expression source; term_expression application;
       int_list inputs; int_list pins])
  | Error _ as error, _, _ | _, (Error _ as error), _
  | _, _, (Error _ as error) -> error

let local_expression id typ =
  constructor "Build_local_view" [GenericLib.gInt id; term_expression typ]

let producer_expression = function
  | PS_G -> constructor "Generator" []
  | PS_E -> constructor "Enumerator" []

let step_expression ~global ~finite_pins scope step =
  let source ~outputs src = source_expression ~global ~finite_pins scope
    ~outputs src in
  match step with
  | S_Check (src, positive) ->
    (match source ~outputs:[] src with
     | Ok src -> Ok (constructor "CheckStep"
         [src; if positive then GenericLib.g_true else GenericLib.g_false])
     | Error _ as error -> error)
  | S_UC (name, src, mode) ->
    (match local_id scope name, source ~outputs:[name] src with
     | Ok id, Ok src_view ->
       let typ = match src with
         | SrcNonrec typ ->
           (match quote_term ~global scope typ with
            | Ok (view, _) -> Ok view
            | Error _ as error -> error)
         | _ -> Ok (TOpaque id) in
       (match typ with
        | Ok typ -> Ok (constructor "Unconstrained"
            [local_expression id typ; src_view; producer_expression mode])
        | Error _ as error -> error)
     | Error _ as error, _ | _, (Error _ as error) -> error)
  | S_ST (outputs, src, mode) ->
    (match source ~outputs:(List.map fst outputs) src with
     | Error _ as error -> error
     | Ok src_view ->
       let rec quote_outputs acc = function
         | [] -> Ok (List.rev acc)
         | (name, typ) :: rest ->
           (match local_id scope name, quote_term ~global scope typ with
            | Ok id, Ok (typ, _) ->
              quote_outputs (local_expression id typ :: acc) rest
            | Error _ as error, _ | _, (Error _ as error) -> error) in
       (match quote_outputs [] outputs with
        | Ok outputs -> Ok (constructor "SuchThat"
            [GenericLib.gList outputs; src_view; producer_expression mode])
        | Error _ as error -> error))
  | S_Match _ | S_Let _ ->
    Error "SchedulingPolicy: match and let steps need binder-aware quotation"

(* The result remains a typed Rocq term: the plugin need not know a user's
   score representation. The returned sigma carries elaboration constraints. *)
let evaluate_expression env function_name argument =
  let expression = GenericLib.gApp
    (GenericLib.gInject function_name) [argument] in
  let sigma, term = GenericLib.interp_coq_expr_evars env (Evd.from_env env)
    expression in
  if Evd.has_undefined sigma then
    Error "SchedulingPolicy: the selected scorer left unresolved evars"
  else
    let typ = Retyping.get_type_of env sigma term in
    Ok (sigma, Vnorm.cbv_vm env sigma term typ, typ)

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
