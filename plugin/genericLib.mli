(* option type helpers *)
val option_map : ('a -> 'b) -> 'a option -> 'b option
val (>>=) : 'a option -> ('a -> 'b option) -> 'b option                                   
val isSome : 'a option -> bool
val foldM : ('b -> 'a -> 'b option) -> 'b option -> 'a list -> 'b option
val sequenceM : ('a -> 'b option) -> 'a list -> 'b list option
val remove_duplicates : 'a list -> 'a list
val filter_mapi : (int -> 'a -> 'b option) -> 'a list -> 'b list

(* vars and type parameters will always be "local", constructors should be global *)
type var = Names.Id.t
type ty_param = Names.Id.t
type ty_ctr = Libnames.qualid
type constructor = Libnames.qualid

val var_to_string : var -> string
val ty_param_to_string : ty_param -> string
val ty_ctr_to_string : ty_ctr -> string
val ty_ctr_basename : ty_ctr -> var
val ty_ctr_to_ctr : ty_ctr -> constructor
val constructor_to_string : constructor -> string

val var_of_string : string -> var
(* Standard library paths written with the Coq prefix, as the current
   Rocq names them; [is_rocq_path s path] compares under that renaming. *)
val rocq_path : string -> string
val is_rocq_path : string -> string -> bool
val ty_ctr_of_string : string -> ty_ctr
val constructor_of_string : string -> constructor

(* Patterns in language that derivations target *)
type pat =
  | PCtr of constructor * pat list
  | PVar of var
  | PParam (* Type parameter *)
  | PWild

val pat_vars : pat -> var list

val pat_to_string : pat -> string

(* Wrapper around constr that we use to represent the types of
   inductives and theorems that we plan to derive for or quickcheck *)
type rocq_constr = 
  | DArrow of rocq_constr * rocq_constr (* Unnamed arrows *)
  | DLambda of ty_param * rocq_constr * rocq_constr
  | DProd  of (var * rocq_constr) * rocq_constr (* Binding arrows *)
  | DTyParam of ty_param (* Type parameters - for simplicity *)
  | DTyCtr of ty_ctr * rocq_constr list (* Type Constructor *)
  | DCtr of constructor * rocq_constr list (* Type Constructor *)
  | DTyVar of var (* Use of a previously captured type variable *)
  | DApp of rocq_constr * rocq_constr list (* Type-level function applications *)
  | DMatch of rocq_constr * (pat * rocq_constr) list
  | DNot of rocq_constr (* Negation as a toplevel *)
  | DHole (* For adding holes *)
val rocq_constr_to_string : rocq_constr -> string
val rocq_constr_tuple_of_list : rocq_constr list -> rocq_constr

type rocq_type = rocq_constr

val type_info : rocq_type -> (ty_param * rocq_type) list * rocq_type list * rocq_type
                              (*typed vars                    hyps             concl*)

val variables_in_hypothesis : rocq_type -> var list

val ty_ctr_eq : ty_ctr -> ty_ctr -> bool

val (>>=:) : 'a list -> ('a -> 'b list) -> 'b list


type rocq_ctr = constructor * rocq_constr
val rocq_ctr_to_string : rocq_ctr -> string

(* This represents an inductive relation in coq, e.g. "Inductive IsSorted (t : Type) : list t -> Prop := ...".
   This tuple is a wrapper around coq internals. *)
type rocq_relation
  = ty_ctr        (* The name of the relation (e.g. IsSorted) *)
  * ty_param list (* The list of type parameters (e.g. "t" in IsSorted) *)
  * rocq_ctr list (* A list of constructors. Each constructor is a pair (name, type) *)
  * rocq_constr   (* The type of the overall relation (e.g. "list t -> Prop") *)
val rocq_relation_to_string : rocq_relation -> string

(* Given the name of an inductive, lookup its definition and 
   any other relations mutually defined with it. *)

val qualid_to_rocq_relations : Libnames.qualid -> (int * rocq_relation list) option
val ty_ctr_to_rocq_relations : ty_ctr -> (int * rocq_relation list) option
val oib_to_rocq_relation :  Declarations.one_inductive_body -> rocq_relation option
val ind_reference_to_unparameterized_relation : Constrexpr.constr_expr -> rocq_relation option
val define_new_inductive : rocq_relation -> unit
val ind_reference_to_rocq_relations : Constrexpr.constr_expr -> (int * rocq_relation list) option

val parse_dependent_type : Constr.constr -> rocq_constr option

type producer_sort = PS_E | PS_G

val rocq_constr_var_relation_uses' : rocq_constr -> (var * (int * int list list) list) list

type source = 
  | SrcNonrec of rocq_type
  | SrcRec of var * rocq_constr list
  | SrcMutrec of var * rocq_constr list
  | SrcDef of var * rocq_constr list

type schedule_step =
  | S_UC of var * source * producer_sort
  | S_ST of (var * rocq_type (*** (int list) list*)) list * source * producer_sort (* the (int list) list for each var means the list of all occurences of the same variable
                                                                                        that we wish to produce, any other instance of the var is an input *)
  | S_Check of source * bool
  | S_Match of var * pat
  | S_Let of var * rocq_constr

type schedule_sort = ProducerSchedule of bool * producer_sort * rocq_constr (* tuple of produced outputs from conclusion of constructor *)
                   | CheckerSchedule (* checkers need not bother with conclusion of constructor, only hypotheses need be checked and conclusion of constructor follows *)
                   | TheoremSchedule of rocq_constr * bool (* conclusion of theorem to be checked *)

type schedule = schedule_step list * schedule_sort

type derive_sort = D_Gen | D_Enum | D_Check | D_Thm

val debug_mode : bool ref

(** The full applied relation of a self-recursive step, whose source keeps
    only input arguments, given the derivation's relation and output positions. *)
val recursive_request : constructor * int list -> schedule_step -> rocq_constr option

(** With [select_groups], a constructor whose hypotheses split into two or
    more footprint-disjoint groups is searched group by group. The callback
    receives each group's completed local schedules and returns index
    combinations, one per group; only those combinations become candidates.
    [canon] maps a variable to its unification representative. *)
val possible_schedules : ?canon:(var -> var) ->
  ?select_groups:(schedule_step list list list -> int list list) ->
  (var * rocq_type) list ->
  rocq_type list ->
  var list -> constructor * int list ->
  derive_sort -> schedule_step list list

  (* val possible_schedules_lazy : (var * rocq_type) list ->
    rocq_type list ->
    var list -> constructor * int list ->
    derive_sort -> schedule_step list Seq.t *)

(* val possible_schedules_pruned : ?max_schedules:int -> (var * rocq_type) list ->
  rocq_type list ->
  var list -> constructor * int list ->
  derive_sort -> schedule_step list list *)

type prefix_floor = {
  forced_checks : int;
  bound_argument_occurrences : var list;
  future_variable_uses : int;
  (* The hypotheses not yet scheduled, with their polarity. *)
  remaining_hypotheses : (rocq_constr * bool) list;
}

type prefix_search_stats = {
  mutable visited_nodes : int;
  mutable completed_prefixes : int;
  mutable processed_mode_choices : int;
}

val empty_prefix_search_stats : unit -> prefix_search_stats

(* Internal search probes. should_prune_prefix is for certified policy bounds;
   callers must establish that it holds for every descendant of the prefix.
   The floor variants also pass the number of remaining positive hypotheses
   whose arguments are already bound and therefore must become checks. *)
val unpruned_candidate_cap : unit -> int

val possible_schedules_with_advanced_pruning : ?max_schedules:int -> ?reduce_orderings:bool ->
  ?maximal_outputs:bool ->
  ?stats:prefix_search_stats ->
  ?canon:(var -> var) ->
  ?select_groups:(schedule_step list list list -> int list list) ->
  ?on_prefix:((int * var list list) list -> bool -> schedule_step list -> unit) ->
  ?on_prefix_with_floor:((int * var list list) list -> bool -> prefix_floor ->
    schedule_step list -> unit) ->
  ?should_prune_prefix:((int * var list list) list -> schedule_step list -> bool) ->
  ?should_prune_prefix_with_floor:((int * var list list) list -> prefix_floor ->
    schedule_step list -> bool) ->
  (var * rocq_type) list ->
  rocq_type list ->
  var list -> constructor * int list ->
  derive_sort -> schedule_step list list

(* Regression oracle for the former chunk-insertion search. *)
val possible_schedules_with_legacy_pruning : ?max_schedules:int -> (var * rocq_type) list ->
  rocq_type list ->
  var list -> constructor * int list ->
  derive_sort -> schedule_step list list

val schedule_step_to_string : schedule_step -> string
val schedule_sort_to_string : schedule_sort -> string
val schedule_to_string : schedule -> string

type monad_sort =
  | MG 
  | MGOpt
  | MGShrink
  | MGOptShrink
  | ME
  | MEOpt
  | MC
  | MId

(* TODO: Weights? *)
(* Deep AST of Language that derivations target *)
(* Continuation of mexp is always going to be of a particular monad sort.*)
type mexp =
  | MBind of monad_sort * mexp * var list * mexp
    (* bind m1 (fun id => m2) *)
  | MRet  of mexp
    (* ret m *)
  | MFail      (* Signifies failure *) 
  | MOutOfFuel (* Signifies failure due to fuel *)
  | MId of var
  | MApp of mexp * mexp list
  | MCtr of constructor * mexp list
  | MTyCtr of ty_ctr * mexp list
  | MConst of string
  | MEscape of Constrexpr.constr_expr
  | MMatch of mexp * (pat * mexp) list 
  | MHole 
  | MLet of var * mexp * mexp 
  | MBacktrack of mexp * mexp list * bool * derive_sort
  | MFun of (pat * mexp option) list * mexp (*var list is a tuple, if you want multiple args do nested MFuns.*)
  | MFix of var * (var * mexp) list * mexp * derive_sort
  | MMutFix of (var * (var * mexp) list * mexp * derive_sort) list * var
  | MArrow of mexp * mexp
  | MProd of (ty_param * mexp) list * mexp

val product_free_rocq_type_to_mexp : rocq_type -> mexp

val schedule_to_mexp : schedule -> mexp -> mexp -> mexp -> mexp

val mexp_to_constr_expr : mexp -> derive_sort -> Constrexpr.constr_expr

val mexp_to_string : mexp -> string

val c_app : ?explicit:bool -> Constrexpr.constr_expr -> Constrexpr.constr_expr list -> Constrexpr.constr_expr

val c_show : Constrexpr.constr_expr -> Constrexpr.constr_expr

val c_quickCheck : Constrexpr.constr_expr -> Constrexpr.constr_expr

val c_sized : Constrexpr.constr_expr -> Constrexpr.constr_expr

val c_zero : Constrexpr.constr_expr

val c_succ : Constrexpr.constr_expr -> Constrexpr.constr_expr

val c_theorem : Constrexpr.constr_expr

(* Schedule, input matches, and constructor-local binder types. *)
(* A constructor's weight in a generator's choice: the QuickChickWeights
   entry for it, if any, else 1 for a base and size + 1 for a recursive
   constructor. *)
type rule_weight = WDefault | WNum of int | WSize
type rule_schedule = schedule * (var * pat) list * (var * mexp) list * rule_weight
type inductive_schedule = string * (var * mexp) list * (var * mexp list) list * rule_schedule list * rule_schedule list



(* val inductive_schedules_to_constr_expr : (inductive_schedule * derive_sort * bool) list list -> string -> Constrexpr.constr_expr *)

val inductive_schedules_to_def_mexps : (inductive_schedule * derive_sort * bool) list list -> string -> (var * mexp * derive_sort) list list 

val inductive_schedules_to_def_constr_exprs : (inductive_schedule * derive_sort * bool) list list -> string -> (var * Constrexpr.constr_expr) list list

val inductive_schedule_to_string : inductive_schedule -> string

val schedule_step_dependence : schedule_step ->
  (rocq_constr * int list * derive_sort * bool) option
val schedule_dependents : schedule -> (rocq_constr * int list * derive_sort * bool) list
val inductive_schedule_dependents : inductive_schedule -> (rocq_constr * int list * derive_sort * bool) list

val schedule_with_dependents : schedule ->
  (schedule_step * (rocq_type * int list * derive_sort * bool) option) list *
  (schedule_sort * (rocq_type * int list * derive_sort * bool) option)

val compile_and_pp_schedule : schedule -> derive_sort -> Pp.t

type parsed_classes = {gen : rocq_constr list; 
                        enum : rocq_constr list;
                        genST : (var list * rocq_constr) list; 
                        enumST : (var list * rocq_constr) list;
                        checker : rocq_constr list;
                        decEq : rocq_constr list}

val find_typeclass_bindings : Libnames.qualid -> parsed_classes

val constr_expr_to_string : Constrexpr.constr_expr -> string


val fresh_name : string -> var 
val make_up_name : unit -> var
(* Clears the shared match variables of handle_constrained_outputs_advanced. *)
val clear_constrained_output_cache : unit -> unit
val make_up_name_str : string -> var
val var_of_id : Names.Id.t -> var 
val str_lst_to_string : string -> string list -> string

