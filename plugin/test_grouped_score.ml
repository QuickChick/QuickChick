module G = Quickchick_plugin.GroupedScore
module N = Quickchick_plugin.GenericLib
module B = Quickchick_plugin.BudgetAwareScore

let state = ref 271828
let next bound =
  state := (!state * 1103515245 + 12345) land 0x3fffffff;
  !state mod bound

let rec product = function
  | [] -> [[]]
  | xs :: rest -> List.concat_map (fun x ->
      List.map (fun tail -> x :: tail) (product rest)) xs

(* Brute force: the selection must contain a combination whose complete
   score, with a shared context, equals the best over every combination. *)
let exact policy groups shared =
  let usable = List.map (fun group ->
    List.mapi (fun i x -> i, x) group
    |> List.filter_map (fun (i, x) -> Option.map (fun x -> i, x) x)) groups in
  let total choice = List.fold_left2 (fun acc group i ->
    policy.G.combine acc (List.assoc i group)) shared usable choice in
  let chosen = G.select_combinations policy groups in
  match product (List.map (List.map fst) usable) with
  | [] -> chosen = []
  | all ->
    let best = List.fold_left (fun best c ->
      if G.compare policy (total c) (total best) < 0 then c else best)
      (List.hd all) all in
    chosen <> [] && List.for_all (fun c -> List.mem c all) chosen &&
    List.exists (fun c -> G.compare policy (total c) (total best) = 0) chosen

(* Random lexicographic policies over int vectors. Additive fields add;
   extremal fields take max or min. [declared] may misstate a kind. *)
let random_policy () =
  let width = 1 + next 4 in
  let fields = List.init width (fun i ->
    let extremal = next 2 = 0 in
    let ascending = next 2 = 0 in
    let take_max = next 2 = 0 in
    i, extremal, ascending, take_max) in
  let combine a b = Array.of_list (List.map (fun (i, extremal, _, take_max) ->
    if extremal then (if take_max then max else min) a.(i) b.(i)
    else a.(i) + b.(i)) fields) in
  let unit = Array.of_list (List.map (fun (_, extremal, _, take_max) ->
    if extremal then (if take_max then 0 else 4) else 0) fields) in
  let field (i, extremal, ascending, _) =
    (if extremal then G.Extremal else G.Additive),
    (fun a b -> if ascending then Stdlib.compare a.(i) b.(i)
      else Stdlib.compare b.(i) a.(i)) in
  { G.unit; combine; fields = List.map field fields }, width

let random_score width = Array.init width (fun _ -> next 5)

let random_groups score =
  List.init (1 + next 3) (fun _ ->
    List.init (1 + next 4) (fun _ ->
      if next 6 = 0 then None else Some (score ())))

let () =
  let checked = ref 0 in
  for _ = 1 to 6000 do
    let policy, width = random_policy () in
    let samples = List.init 6 (fun _ -> random_score width) in
    (match G.check_laws policy (policy.G.unit :: samples) with
     | Ok () -> ()
     | Error message -> failwith message);
    assert (exact policy (random_groups (fun () -> random_score width))
      (random_score width));
    incr checked
  done;
  (* Declaring a max field additive is unsound: dominance then treats an
     absorbable lead as decisive. Both the law check and brute force see it. *)
  let max_first = { G.unit = [|0; 0|];
    combine = (fun a b -> [|max a.(0) b.(0); a.(1) + b.(1)|]);
    fields = [G.Additive, (fun a b -> Stdlib.compare a.(0) b.(0));
              G.Additive, (fun a b -> Stdlib.compare a.(1) b.(1))] } in
  assert (Result.is_error (G.check_laws max_first [[|0; 0|]; [|1; 0|]; [|2; 0|]]));
  assert (not (exact max_first [[Some [|1; 10|]; Some [|2; 0|]]] [|2; 0|]));
  Printf.printf "grouped score: %d random policies\n" !checked

(* BudgetAware laws, and exactness on random six-field scores. *)
let densities = [B.Total; B.Partial; B.Backtracking; B.Checking]
let localities = [B.Internal; B.External; B.SameIndExt]
let random_budget () = {
  B.selectivity = next 3; density = List.nth densities (next 4);
  fabrication = next 3; locality = List.nth localities (next 3);
  input_check_deps = next 3; var_deps = next 3 }

let () =
  (match G.check_laws B.group_policy
     (B.empty :: List.init 12 (fun _ -> random_budget ())) with
   | Ok () -> ()
   | Error message -> failwith message);
  for _ = 1 to 3000 do
    assert (exact B.group_policy (random_groups random_budget) (random_budget ()))
  done

(* BudgetAware separability on step fixtures: groups with disjoint variables,
   using a finitely pinned relation so selectivity is exercised. *)
let v = N.var_of_string
let rel name args = N.DTyCtr (N.ty_ctr_of_string name, args)
let var name = N.DTyVar (v name)
let nat = rel "nat" []
let pinned = N.ty_ctr_of_string "Pinned"
let key = { B.relation = N.ty_ctr_of_string "Root"; output_indices = [0];
            derive_sort = N.D_Gen }
let dep_key = { B.relation = N.ty_ctr_of_string "Dep"; output_indices = [0];
                derive_sort = N.D_Gen }
let context = {
  B.input_vars = [v "input"];
  finite_pins = (fun name -> if N.ty_ctr_eq name pinned then [0] else []);
  completed_dependency = (fun request ->
    if request.B.key = dep_key then Some { B.empty with density = B.Backtracking }
    else None) }

(* One group's steps over its own variables x<tag>, y<tag>. *)
let group_steps tag shape =
  let x = "x" ^ tag and y = "y" ^ tag in
  match shape with
  | 0 -> [N.S_UC (v x, N.SrcNonrec nat, N.PS_G);
          N.S_Check (N.SrcNonrec (rel "Pinned" [var x]), true)]
  | 1 -> [N.S_ST ([v x, nat], N.SrcNonrec (rel "Pinned" [var x]), N.PS_G)]
  | 2 -> [N.S_ST ([v x, nat], N.SrcNonrec (rel "Dep" [var x; var "input"]), N.PS_G);
          N.S_Check (N.SrcNonrec (rel "Other" [var x; var "input"]), true)]
  | 3 -> [N.S_UC (v y, N.SrcNonrec nat, N.PS_G);
          N.S_ST ([v x, nat], N.SrcNonrec (rel "Dep" [var x; var y]), N.PS_G);
          N.S_Check (N.SrcNonrec (rel "Pinned" [var y]), true)]
  | _ -> [N.S_ST ([v x, nat], N.SrcRec (v "rec", [var x]), N.PS_G);
          N.S_Check (N.SrcNonrec (rel "Pinned" [var x]), true)]

let score steps = match B.score_schedule context key steps with
  | Ok s -> s | Error message -> failwith message

let () =
  let shared = [N.S_Check (N.SrcNonrec (rel "Coq.Init.Logic.eq"
    [N.DHole; var "input"; var "input"]), true)] in
  let cases = ref 0 in
  List.iter (fun a -> List.iter (fun b -> List.iter (fun c ->
    let ga = group_steps "a" a and gb = group_steps "b" b and gc = group_steps "c" c in
    let parts = [shared; ga; gb; gc] in
    let expected = List.fold_left (fun acc p -> B.combine acc (score p)) B.empty parts in
    List.iter (fun order ->
      let whole = score (List.concat order) in
      if B.compare whole expected <> 0 then
        failwith (Printf.sprintf "BudgetAware not separable for shapes %d %d %d: %s vs %s"
          a b c (B.to_string whole) (B.to_string expected));
      incr cases)
      [parts; [gc; shared; ga; gb]; [gb; gc; ga; shared]])
    [0;1;2;3;4]) [0;1;2;3;4]) [0;1;2;3;4];
  (* Selectivity really counts across groups: two loose pinned producers. *)
  assert ((score (group_steps "a" 0 @ group_steps "b" 0)).B.selectivity = 2);
  Printf.printf "BudgetAware separability: %d ordered schedules\n" !cases
