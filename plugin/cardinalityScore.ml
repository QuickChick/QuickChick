(* Cardinality scoring. A schedule is read as a query plan: producers
   enumerate the solutions of a relation mode, and matches and checks filter
   them. Counts are growth classes in the size bound. A filter's acceptance is
   the class of what it admits over the class of what reaches it; the score
   counts filters by acceptance class. See
   audit/3.0-scoring/cardinality/README.md for the rules and their limits. *)

open NewGenericLib

type cls = One | Fin | Poly | Exp

let rank = function One -> 0 | Fin -> 1 | Poly -> 2 | Exp -> 3

let cls_to_string = function
  | One -> "1" | Fin -> "fin" | Poly -> "poly" | Exp -> "exp"

let max_cls a b = if rank a >= rank b then a else b

(* Product of two counts, and the count of two disjoint alternatives. *)
let times a b = match a, b with
  | One, c | c, One -> c
  | _ -> max_cls (max_cls a b) Fin

let plus a b = match a, b with
  | One, One -> Fin
  | _ -> max_cls a b

let times_opt a b = match a, b with
  | Some a, Some b -> Some (times a b)
  | _ -> None

type score = {
  exp_filters : int;
  poly_filters : int;
  unknown_filters : int;
  const_filters : int;
}

let empty = { exp_filters = 0; poly_filters = 0; unknown_filters = 0; const_filters = 0 }

let add a b = {
  exp_filters = a.exp_filters + b.exp_filters;
  poly_filters = a.poly_filters + b.poly_filters;
  unknown_filters = a.unknown_filters + b.unknown_filters;
  const_filters = a.const_filters + b.const_filters;
}

let compare a b = Stdlib.compare
  (a.exp_filters, a.poly_filters, a.unknown_filters, a.const_filters)
  (b.exp_filters, b.poly_filters, b.unknown_filters, b.const_filters)

let to_string s = Printf.sprintf "1/exp=%d 1/poly=%d unknown=%d const=%d"
  s.exp_filters s.poly_filters s.unknown_filters s.const_filters

(* Every field adds across footprint-disjoint groups. *)
let group_policy = {
  GroupedScore.unit = empty;
  combine = add;
  fields = [
    GroupedScore.Additive, (fun a b -> Stdlib.compare a.exp_filters b.exp_filters);
    GroupedScore.Additive, (fun a b -> Stdlib.compare a.poly_filters b.poly_filters);
    GroupedScore.Additive, (fun a b -> Stdlib.compare a.unknown_filters b.unknown_filters);
    GroupedScore.Additive, (fun a b -> Stdlib.compare a.const_filters b.const_filters);
  ];
}

type constructor_info = {
  params : int;
  arg_classes : cls option list;  (* None where the type mentions a parameter *)
  single : bool;                  (* the only constructor of its type *)
}

type context = {
  type_class : rocq_constr -> cls option;
  (* Solution count of a relation mode, for given inputs; checks look up the
     producing mode for their generated arguments. *)
  mode_count : ty_ctr -> int list -> derive_sort -> cls option;
  recursive_count : cls option;
  constructor : constructor -> constructor_info option;
  (* Each constructor of a completed mode: its conclusion arguments and its
     solution count. *)
  mode_shapes : ty_ctr -> int list -> derive_sort -> (rocq_constr list * cls) list option;
  (* How many values the variable at argument [i], under constructor path
     [path], can take when everything else in the relation is fixed. *)
  conditional : ty_ctr -> int -> (constructor * int) list -> cls option;
}

(* Paths to the occurrences of [v] in a term, through constructor arguments. *)
let rec occurrences v = function
  | DTyVar w when w = v -> [[]]
  | DCtr (c, args) ->
    List.concat (List.mapi (fun k a ->
      List.map (fun path -> (c, k) :: path) (occurrences v a)) args)
  | _ -> []


let derive_sort_of = function PS_G -> D_Gen | PS_E -> D_Enum

let rec term_vars = function
  | DTyVar v -> [v]
  | DTyCtr (_, args) | DCtr (_, args) -> List.concat_map term_vars args
  | DApp (f, args) -> List.concat_map term_vars (f :: args)
  | DNot t -> term_vars t
  | _ -> []

(* Constructor patterns may or may not list type-parameter positions. *)
let pattern_args info pats =
  let nargs = List.length info.arg_classes in
  if List.length pats = info.params + nargs then
    List.filteri (fun i _ -> i >= info.params) pats
  else pats

let rec irrefutable ctx = function
  | PVar _ | PWild | PParam -> true
  | PCtr (c, pats) ->
    (match ctx.constructor c with
     | Some info when info.single ->
       List.for_all (irrefutable ctx) (pattern_args info pats)
     | _ -> false)

let rec pattern_count ctx = function
  | PCtr (c, pats) ->
    (match ctx.constructor c with
     | None -> None
     | Some info ->
       let pats = pattern_args info pats in
       if List.length pats <> List.length info.arg_classes then None else
       List.fold_left2 (fun acc cls pat -> match pat with
         | PVar _ | PWild -> times_opt acc cls
         | PParam -> acc
         | PCtr _ -> times_opt acc (pattern_count ctx pat))
         (Some One) info.arg_classes pats)
  | _ -> None

let rec pattern_variables = function
  | PVar v -> [v]
  | PCtr (_, pats) -> List.concat_map pattern_variables pats
  | _ -> []

type acceptance = Const | Inverse_poly | Inverse_exp | Unknown

(* The worse of two known acceptances; Unknown only when both are. *)
let worst a b = match a, b with
  | Inverse_exp, _ | _, Inverse_exp -> Inverse_exp
  | Inverse_poly, _ | _, Inverse_poly -> Inverse_poly
  | Const, _ | _, Const -> Const
  | Unknown, Unknown -> Unknown

let acceptance admitted reaching = match admitted, reaching with
  | None, _ | _, None -> Unknown
  | Some a, Some r ->
    if rank r <= rank Fin || rank a >= rank r then Const
    else if r = Poly then Inverse_poly else Inverse_exp

let record score = function
  | Const -> { score with const_filters = score.const_filters + 1 }
  | Inverse_poly -> { score with poly_filters = score.poly_filters + 1 }
  | Inverse_exp -> { score with exp_filters = score.exp_filters + 1 }
  | Unknown -> { score with unknown_filters = score.unknown_filters + 1 }

let relation_args = function
  | SrcNonrec (DTyCtr (rel, args)) -> Some (Some rel, args)
  | SrcNonrec (DNot (DTyCtr (rel, args))) -> Some (Some rel, args)
  | SrcRec (_, args) | SrcMutrec (_, args) -> Some (None, args)
  | _ -> None

let score_schedule ctx (steps : schedule_step list) =
  (* Fan-out class of each variable bound by a step; inputs are absent. A
     variable bound through a count-1 step is fixed, not generated. *)
  let produced = Hashtbl.create 16 in
  let generated v = match Hashtbl.find_opt produced v with
    | Some (Some One) | None -> false
    | Some _ -> true in
  let reaching vars = List.fold_left (fun acc v ->
    if generated v then times_opt acc (Hashtbl.find produced v) else acc)
    (Some One) vars in
  let check_mode rel positions =
    match ctx.mode_count rel positions D_Gen with
    | Some c -> Some c
    | None -> ctx.mode_count rel positions D_Enum in
  List.fold_left (fun score step -> match step with
    | S_UC (v, SrcNonrec ty, _) ->
      Hashtbl.replace produced v (ctx.type_class ty); score
    | S_UC (v, _, _) -> Hashtbl.replace produced v ctx.recursive_count; score
    | S_Let (v, _) -> Hashtbl.replace produced v (Some One); score
    | S_ST (outputs, src, ps) ->
      let outs = List.map fst outputs in
      let typed = List.fold_left (fun acc (_, ty) -> times_opt acc (ctx.type_class ty))
        (Some One) outputs in
      let score, fan = match relation_args src with
        | Some (Some rel, args) ->
          let out_idx = List.concat (List.mapi (fun i a -> match a with
            | DTyVar v when List.mem v outs -> [i]
            | _ -> []) args) in
          let fan = match ctx.mode_count rel out_idx (derive_sort_of ps) with
            | Some c -> Some c
            | None -> typed in
          (* Generated inputs: the producer filters them like a check. *)
          let gen_inputs = List.concat (List.mapi (fun i a ->
            if List.mem i out_idx then []
            else if List.exists generated (term_vars a) then [i] else []) args) in
          let score = if gen_inputs = [] then score else
            let joint = ctx.mode_count rel (List.sort Stdlib.compare (gen_inputs @ out_idx))
              (derive_sort_of ps) in
            let reach = reaching (List.concat_map (fun i -> term_vars (List.nth args i)) gen_inputs) in
            record score (acceptance joint (times_opt reach fan)) in
          score, fan
        | Some (None, _) -> score, ctx.recursive_count
        | None -> score, typed in
      List.iter (fun v -> Hashtbl.replace produced v fan) outs;
      score
    | S_Match (v, pat) ->
      if not (generated v) then score else begin
        let fan = Hashtbl.find produced v in
        List.iter (fun w -> Hashtbl.replace produced w fan) (pattern_variables pat);
        if irrefutable ctx pat then record score Const
        else record score (acceptance (pattern_count ctx pat) fan)
      end
    | S_Check (src, polarity) ->
      (match relation_args src with
       | None -> record score Unknown
       | Some (rel, args) ->
         let gen = List.concat (List.mapi (fun i a ->
           if List.exists generated (term_vars a) then [i] else []) args) in
         if gen = [] then record score Const else
         let reach = reaching (List.concat_map term_vars args) in
         (* A generated variable nested under a constructor in the checked
            argument is admitted only by the relation's constructors whose
            conclusion has that head there; a constructor head itself is
            chosen with constant probability by a generator. *)
         let nested = List.exists (fun i -> match List.nth args i with
           | DCtr _ -> true | _ -> false) gen in
         let shapes rel = match ctx.mode_shapes rel gen D_Gen with
           | Some s -> Some s
           | None -> ctx.mode_shapes rel gen D_Enum in
         let admitted = match rel with
           | Some rel when nested ->
             (match shapes rel with
              | None -> None
              | Some shapes ->
                let compatible = List.filter (fun (conclusion, _) ->
                  List.for_all (fun i -> match List.nth args i, List.nth_opt conclusion i with
                    | DCtr (c, _), Some (DCtr (c', _)) -> c = c'
                    | _ -> true) gen) shapes in
                (match compatible with
                 | [] -> Some One
                 | (_, c) :: rest -> Some (List.fold_left (fun acc (_, c) -> plus acc c) c rest)))
           | Some rel -> check_mode rel gen
           | None -> None in
         let acc = acceptance admitted reach in
         (* Each generated variable must be one of the values the relation
            allows it given everything else; the scarcest one bounds the
            check's acceptance. *)
         let conditional = match rel with
           | None -> Unknown
           | Some rel ->
             List.fold_left (fun acc v ->
               if not (generated v) then acc else
               let per_occurrence = List.concat (List.mapi (fun i a ->
                 List.map (fun path -> i, path) (occurrences v a)) args) in
               match per_occurrence with
               | (i, path) :: _ ->
                 worst acc (acceptance (ctx.conditional rel i path) (Hashtbl.find produced v))
               | [] -> acc) Unknown (List.sort_uniq Stdlib.compare (List.concat_map term_vars args)) in
         let acc = if conditional = Unknown then acc else worst acc conditional in
         let acc = if polarity then acc else (match acc with Unknown -> Unknown | _ -> Const) in
         record score acc))
    empty steps

(* Solution count of a mode for given inputs, from its constructors' chosen
   schedules. A constructor starting with a match on an input is guarded: its
   recursion runs on smaller inputs, and guarded constructors with different
   head constructors are alternatives for different inputs (max). Guarded
   recursion with a nontrivial factor per level, or unguarded recursion beside
   growing work or a second recursive call, is exponential; unguarded linear
   recursion is polynomial. Check modes have at most one solution. *)
let constructor_count ctx (steps : schedule_step list) =
  let is_rec = function
    | S_ST (_, (SrcRec _ | SrcMutrec _), _) | S_UC (_, (SrcRec _ | SrcMutrec _), _) -> true
    | _ -> false in
  let fanout steps = List.fold_left (fun acc step -> match step with
    | S_UC (_, SrcNonrec ty, _) -> times_opt acc (ctx.type_class ty)
    | S_ST (outputs, SrcNonrec (DTyCtr (rel, args)), ps) ->
      let outs = List.map fst outputs in
      let idx = List.concat (List.mapi (fun i a -> match a with
        | DTyVar v when List.mem v outs -> [i] | _ -> []) args) in
      times_opt acc (ctx.mode_count rel idx (derive_sort_of ps))
    | _ -> acc) (Some One) steps in
  let head = match steps with
    | S_Match (_, PCtr (c, _)) :: _ -> Some (constructor_to_string c)
    | _ -> None in
  let recs = List.length (List.filter is_rec steps) in
  let others = fanout (List.filter (fun s -> not (is_rec s)) steps) in
  let count = match head, recs, others with
    | _, 0, Some c -> c
    | _, 0, None -> Exp
    | Some _, _, Some One -> One
    | Some _, _, _ -> Exp
    | None, 1, Some One -> Poly
    | None, _, _ -> Exp in
  head, count

let mode_count_of ctx ds (schedules : schedule_step list list) =
  if ds = D_Check then One else
  let unguarded, guarded = List.fold_left (fun (unguarded, guarded) steps ->
    let head, fan = constructor_count ctx steps in
    match head with
    | None -> (Some (match unguarded with None -> fan | Some u -> plus u fan), guarded)
    | Some h ->
      let fan = match List.assoc_opt h guarded with None -> fan | Some p -> plus p fan in
      (unguarded, (h, fan) :: List.remove_assoc h guarded)) (None, []) schedules in
  let guarded = List.fold_left (fun acc (_, c) -> match acc with
    | None -> Some c | Some a -> Some (max_cls a c)) None guarded in
  match unguarded, guarded with
  | None, None -> One
  | Some c, None | None, Some c -> c
  | Some a, Some b -> plus a b
