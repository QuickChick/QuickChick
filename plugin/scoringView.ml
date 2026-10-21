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
