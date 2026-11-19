(* Combining scores of independent hypothesis groups.

   A policy describes its score as a lexicographic sequence of fields over one
   score type. Group scores combine fieldwise with [combine]. An [Additive]
   field preserves its strict order under combination (sums). An [Extremal]
   field is only monotone (max or min): combining can turn a strict
   difference into a tie, which then falls through to later fields. *)

type kind = Additive | Extremal

type 's policy = {
  unit : 's;
  combine : 's -> 's -> 's;
  fields : (kind * ('s -> 's -> int)) list;
}

let compare policy a b =
  let rec go = function
    | [] -> 0
    | (_, cmp) :: rest -> let c = cmp a b in if c <> 0 then c else go rest in
  go policy.fields

(* [dominates p a b]: for every context [c], [combine a c] ranks no worse
   than [combine b c]. An additive field decides when strict; an extremal
   field must be no worse, and the remaining fields must also dominate. *)
let dominates policy a b =
  let rec go = function
    | [] -> true
    | (Additive, cmp) :: rest ->
      let c = cmp a b in c < 0 || (c = 0 && go rest)
    | (Extremal, cmp) :: rest -> cmp a b <= 0 && go rest in
  go policy.fields

let same_extremal policy a b =
  List.for_all (fun (kind, cmp) -> kind = Additive || cmp a b = 0) policy.fields

(* Per group, keep the first candidate of each score not strictly dominated.
   Combine by dynamic programming: states with equal extremal fields receive
   the same future combinations, under which additive fields keep their order,
   so the best state of each extremal class suffices. Candidate index lists
   break ties. The result contains a combination with the best complete
   score; equal-scoring combinations may differ from a joint search's choice. *)
let select_combinations policy (groups : 's option list list) : int list list =
  let front candidates =
    let usable = List.mapi (fun i score -> i, score) candidates
      |> List.filter_map (fun (i, score) -> Option.map (fun s -> i, s) score) in
    let distinct = List.fold_left (fun kept (i, s) ->
      if List.exists (fun (_, t) -> compare policy s t = 0) kept
      then kept else kept @ [i, s]) [] usable in
    List.filter (fun (_, s) ->
      not (List.exists (fun (_, t) ->
        dominates policy t s && not (dominates policy s t)) distinct)) distinct in
  let fronts = List.map front groups in
  if List.exists (fun f -> f = []) fronts then [] else
  let better (s, choice) (t, other) =
    let c = compare policy s t in
    c < 0 || (c = 0 && Stdlib.compare choice other < 0) in
  let step states front =
    List.fold_left (fun next (s, choice) ->
      List.fold_left (fun next (i, g) ->
        let candidate = (policy.combine s g, choice @ [i]) in
        let rec insert = function
          | [] -> [candidate]
          | current :: rest when same_extremal policy (fst current) (fst candidate) ->
            (if better candidate current then candidate else current) :: rest
          | current :: rest -> current :: insert rest in
        insert next) next front) [] states in
  List.fold_left step [policy.unit, []] fronts
  |> List.map snd |> List.sort_uniq Stdlib.compare

(* Field laws on sample scores: fieldwise combination, the declared kind's
   order law, and a commutative, associative combination with a unit. These
   are checked properties of the samples only, not a proof. *)
let check_laws policy samples =
  let fail what = Error ("grouped score law failed: " ^ what) in
  let eq a b = List.for_all (fun (_, cmp) -> cmp a b = 0) policy.fields in
  let rec first = function
    | [] -> Ok ()
    | (ok, what) :: rest -> if ok () then first rest else fail what in
  let all f = List.for_all (fun a -> List.for_all (f a) samples) samples in
  first [
    (fun () -> List.for_all (fun a -> eq (policy.combine policy.unit a) a) samples),
      "unit";
    (fun () -> all (fun a b -> eq (policy.combine a b) (policy.combine b a))),
      "commutativity";
    (fun () -> all (fun a b -> List.for_all (fun c ->
      eq (policy.combine (policy.combine a b) c)
         (policy.combine a (policy.combine b c))) samples)), "associativity";
    (fun () -> all (fun a b -> List.for_all (fun c ->
      List.for_all (fun (kind, cmp) ->
        let before = cmp a b and after = cmp (policy.combine a c) (policy.combine b c) in
        match kind with
        | Additive -> Int.compare before 0 = Int.compare after 0
        | Extremal -> before > 0 || after <= 0) policy.fields) samples)),
      "field order under combination";
  ]
