module N = Quickchick_plugin.NewGenericLib
module V = Quickchick_plugin.ScoringView
module P = Quickchick_plugin.PolicyViews
module U = Quickchick_plugin.NewUnifyQC

let v = N.var_of_string
let global = N.ty_ctr_to_string
let variable name = N.DTyVar (v name)
let relation name args = N.DTyCtr (N.ty_ctr_of_string name, args)

let quoted scope term = match V.quote_term ~global scope term with
  | Ok result -> result
  | Error message -> failwith message

let () =
  let nat = relation "nat" [] in
  let a = v "A" in
  let scope = V.scope [a] in
  let list_a = relation "Coq.Init.Datatypes.list" [N.DTyParam a] in
  assert (fst (quoted scope list_a) =
    P.TApply (P.TGlobal (V.chars (N.rocq_path "Coq.Init.Datatypes.list")), [P.TLocal 0]));
  let x = v "x" in
  (try ignore (V.scope [x; x]);
       failwith "duplicate free locals were accepted"
   with Invalid_argument _ -> ());
  let shadowed = N.DProd ((x, nat),
    N.DProd ((x, nat), variable "x")) in
  assert (fst (quoted (V.scope []) shadowed) =
    P.TProduct (0, P.TGlobal (V.chars "nat"),
      P.TProduct (1, P.TGlobal (V.chars "nat"), P.TLocal 1)));
  let sibling = N.DApp (relation "Pair" [],
    [N.DProd ((x, nat), variable "x"); variable "x"]) in
  (match V.quote_term ~global (V.scope []) sibling with
   | Error _ -> ()
   | Ok _ -> failwith "a binder leaked into a sibling argument");
  let branches = N.DMatch (variable "x", [
    N.PCtr (N.constructor_of_string "Some", [N.PVar (v "y")]), variable "y";
    N.PWild, variable "x"]) in
  assert (fst (quoted (V.scope [x]) branches) =
    P.TMatch (P.TLocal 0, [
      P.PConstructor (V.chars "Some", [P.PLocal 1]), P.TLocal 1;
      P.PWild, P.TLocal 0]));
  assert (V.free_vars_term branches = [x; x]);
  assert (V.free_vars_term (N.DMatch (variable "x", [
    N.PVar (v "y"), variable "y"])) = [x]);
  assert (fst (quoted scope N.DHole) = P.TImplicitHole);
  let output = v "out" in
  let result_x = v "result_x" and result_y = v "result_y" in
  let root = N.ty_ctr_of_string "ViewRoot" in
  let typ = N.DProd ((x, nat), N.DProd ((output, nat),
    N.DArrow (relation "ViewRel" [variable "x"; variable "out"],
      N.DTyCtr (root, [variable "x"; variable "out"])))) in
  let candidates = U.type_to_schedules typ (Some root)
    (Some (N.ty_ctr_of_string "ViewCtor"))
    [result_x, nat; result_y, nat]
    [result_y] N.D_Gen true in
  assert (candidates <> []);
  let saw_relation = ref false in
  List.iter (fun ((steps, _), _, _) ->
    List.iter (function
      | N.S_ST (_, N.SrcNonrec term, _) | N.S_Check (N.SrcNonrec term, _) ->
        (match V.quote_term ~global (V.scope [result_x; result_y]) term with
         | Ok (P.TApply (P.TGlobal name, [P.TLocal 0; P.TLocal 1]), _)
           when name = V.chars "ViewRel" ->
           saw_relation := true
         | Ok _ | Error _ -> ())
      | _ -> ()) steps) candidates;
  assert !saw_relation
