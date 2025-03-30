(* option type helpers *)
val option_map : ('a -> 'b) -> 'a option -> 'b option
val (>>=) : 'a option -> ('a -> 'b option) -> 'b option                                   
val isSome : 'a option -> bool
val cat_maybes : 'a option list -> 'a list
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

module OrdRocqConstr : sig
    type t = rocq_constr
    val compare : t -> t -> int
end

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
val constr_to_rocq_constr : Constr.constr -> rocq_constr option

val qualid_to_rocq_relations : Libnames.qualid -> (int * rocq_relation list) option
val ty_ctr_to_rocq_relations : ty_ctr -> (int * rocq_relation list) option
val oib_to_rocq_relation :  Declarations.one_inductive_body -> rocq_relation option
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

type schedule_sort = ProducerSchedule of bool * producer_sort * rocq_constr (* tuple of produced outputs from conclusion of constructor *)
                   | CheckerSchedule (* checkers need not bother with conclusion of constructor, only hypotheses need be checked and conclusion of constructor follows *)
                   | TheoremSchedule of rocq_constr * bool (* conclusion of theorem to be checked *)

type schedule = schedule_step list * schedule_sort

type derive_sort = D_Gen | D_Enum | D_Check | D_Thm

val possible_schedules : (ty_param * rocq_type) list ->
  rocq_type list ->
  ty_param list -> constructor * int list ->
  derive_sort -> schedule_step list list

val schedule_step_to_string : schedule_step -> string
val schedule_sort_to_string : schedule_sort -> string
val schedule_to_string : schedule -> string

type monad_sort =
  | MG 
  | MGOpt
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

val product_free_rocq_type_to_mexp : rocq_type -> mexp

val schedule_to_mexp : schedule -> mexp -> mexp -> mexp

val mexp_to_constr_expr : mexp -> derive_sort -> Constrexpr.constr_expr

type inductive_schedule = string * (var * mexp) list * (schedule * (var * pat) list) list * (schedule * (var * pat) list) list 

val inductive_schedule_to_constr_expr : inductive_schedule -> derive_sort -> bool -> Constrexpr.constr_expr

val inductive_schedule_with_dependencies_to_constr_expr : 
  (inductive_schedule * derive_sort * bool) list ->
  (inductive_schedule * derive_sort * bool) list ->
  string -> 
  Constrexpr.constr_expr

val inductive_schedules_to_constr_expr : (inductive_schedule * derive_sort * bool) list list -> string -> Constrexpr.constr_expr

val inductive_schedules_to_def_mexps : (inductive_schedule * derive_sort * bool) list list -> string -> (var * mexp * derive_sort) list list 

val inductive_schedules_to_def_constr_exprs : (inductive_schedule * derive_sort * bool) list list -> string -> (var * Constrexpr.constr_expr) list list

val inductive_schedule_to_string : inductive_schedule -> string

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

val debug_constr_expr : Constrexpr.constr_expr -> unit
val constr_expr_to_string : Constrexpr.constr_expr -> string

module ScheduleExamples : sig
  val thm_schedule : schedule
  val check_typing_inductive_schedule : inductive_schedule
  val ind_schd_bind_gen_ioo : inductive_schedule
  val gen_term_inductive_schedule : inductive_schedule
end

val fresh_name : string -> var 
val make_up_name : unit -> var
val make_up_name_str : string -> var
val var_of_id : Names.Id.t -> var 
val str_lst_to_string : string -> string list -> string

(*
open Names
open Declarations
open Constrexpr

type coq_expr

val interp_open_coq_expr : Environ.env -> Evd.evar_map -> 
  coq_expr -> EConstr.constr

val hole : coq_expr

val debug_coq_expr : coq_expr -> unit

type var
  
val id_of_var : var -> Id.t
val var_to_string : var -> string
val inject_var : string -> var 
val gVar : var -> coq_expr

val gInject : string -> coq_expr

val gType0 : coq_expr   

type ty_param 
val ty_param_to_string : ty_param -> string
val inject_ty_param : string -> ty_param
val gTyParam : ty_param -> coq_expr

type ty_ctr
val ty_ctr_to_string : ty_ctr -> string
val gInjectTyCtr : string -> ty_ctr
val gTyCtr : ty_ctr -> coq_expr
val tyCtrToQualid : ty_ctr -> Libnames.qualid

type arg
val gArg : ?assumName:coq_expr ->
           ?assumType:coq_expr ->
           ?assumImplicit:bool ->
           ?assumGeneralized:bool ->
           unit -> arg

val arg_to_var : arg -> var
  


type coq_type = 
  | Arrow of coq_type * coq_type
  | TyCtr of ty_ctr * coq_type list
  | TyParam of ty_param

val coq_type_size : coq_type -> int
val coq_type_to_string : coq_type -> string

type constructor 
val constructor_to_string : constructor -> string
val gCtr : constructor -> coq_expr
val injectCtr : string -> constructor
val ty_ctr_to_ctr : ty_ctr -> constructor
val ctr_to_ty_ctr : constructor -> ty_ctr 

module type Ord_ty_ctr_type = sig
  type t = ty_ctr 
  val compare : t -> t -> int
  end
module Ord_ty_ctr : Ord_ty_ctr_type

module type Ord_ctr_type = sig
  type t = constructor
  val compare : t -> t -> int
  end
module Ord_ctr : Ord_ctr_type

val num_of_ctrs : constructor -> int
val belongs_to_inductive : constructor -> bool

type ctr_rep = constructor * coq_type 
val ctr_rep_to_string : ctr_rep -> string

type dt_rep = ty_ctr * ty_param list * ctr_rep list
val dt_rep_to_string : dt_rep -> string


val rocq_constr_to_string : rocq_constr -> string

type dep_ctr = constructor * rocq_constr
val dep_ctr_to_string : dep_ctr -> string

type dep_dt = ty_ctr * ty_param list * dep_ctr list * rocq_constr
val dep_dt_to_string : dep_dt -> string

val constr_of_type : string -> ty_param list -> rocq_constr -> Constr.t
val gType : ty_param list -> rocq_constr -> coq_expr
val gType' : ty_param list -> rocq_constr -> coq_expr
val get_type : Id.t -> unit
val is_inductive : constructor -> bool
val is_inductive_dt : rocq_constr -> bool

val nthType : int -> rocq_constr -> rocq_constr

val rocq_constr_len : rocq_constr -> int

val dep_result_type : rocq_constr -> rocq_constr

(* option type helpers *)
val option_map : ('a -> 'b) -> 'a option -> 'b option
val (>>=) : 'a option -> ('a -> 'b option) -> 'b option                                   
val isSome : 'a option -> bool
val cat_maybes : 'a option list -> 'a list
val foldM : ('b -> 'a -> 'b option) -> 'b option -> 'a list -> 'b option
val sequenceM : ('a -> 'b option) -> 'a list -> 'b list option

val qualid_to_mib : Libnames.qualid -> mutual_inductive_body
val dt_rep_from_mib : mutual_inductive_body -> dt_rep option
val coerce_reference_to_dt_rep : constr_expr -> dt_rep option

val parse_dependent_type : Constr.constr -> rocq_constr option

val dep_dt_from_mib : mutual_inductive_body -> dep_dt option
val coerce_reference_to_dep_dt : constr_expr -> dep_dt option



(* Generic Combinators *)
val gApp : ?explicit:bool -> coq_expr -> coq_expr list -> coq_expr 
val gFun : string list -> (var list -> coq_expr) -> coq_expr
val gRecFunIn : ?structRec:(var option) -> ?assumType:coq_expr -> string -> string list -> ((var * var list) -> coq_expr) -> (var -> coq_expr) -> coq_expr

val gLetIn : string -> coq_expr -> (var -> coq_expr) -> coq_expr
(* TODO: HOAS-ify *)
val gLetTupleIn : var -> var list -> coq_expr -> coq_expr
  
val gMatch : coq_expr -> ?catchAll:(coq_expr option) -> ?params:(int) -> ((constructor * string list * (var list -> coq_expr)) list) -> coq_expr
val gMatchReturn : coq_expr -> ?catchAll:(coq_expr option) -> string -> (var -> coq_expr) ->
  ((constructor * string list * (var list -> coq_expr)) list) -> coq_expr

val gRecord : (string * coq_expr) list -> coq_expr 

val gAnnot : coq_expr -> coq_expr -> coq_expr
val gFunTyped : (string * coq_expr) list -> (var list -> coq_expr) -> coq_expr
val gFunWithArgs : arg list -> ((var list) -> coq_expr) -> coq_expr
val gRecFunInWithArgs : ?structRec:(var option) -> ?assumType:coq_expr -> string -> arg list -> ((var * var list) -> coq_expr) -> (var -> coq_expr) -> coq_expr

val gProdWithArgs : arg list -> ((var list) -> coq_expr) -> coq_expr

(* Specialized Pattern Matching *)

type matcher_pat = 
  | MatchCtr of constructor * matcher_pat list
  | MatchU of var
  | MatchParameter of ty_param (* Should become hole in pattern, so no binding *)
                    
val matcher_pat_to_string : matcher_pat -> string 

val construct_match : coq_expr -> ?catch_all:(coq_expr option) -> (matcher_pat * coq_expr) list -> coq_expr 
val construct_match_with_return : coq_expr -> ?catch_all:(coq_expr option) ->
  string -> (var -> coq_expr) -> (matcher_pat * coq_expr) list -> coq_expr

(* Generic List Manipulations *)
val list_nil : coq_expr
val lst_append : coq_expr -> coq_expr -> coq_expr
val lst_appends : coq_expr list -> coq_expr
val gCons : coq_expr -> coq_expr -> coq_expr 
val gList : coq_expr list -> coq_expr

(* Generic String Manipulations *)
val gStr : string -> coq_expr
val emptyString : coq_expr 
val str_append  : coq_expr -> coq_expr -> coq_expr 
val str_appends : coq_expr list -> coq_expr
val smart_paren : coq_expr -> coq_expr

(* Pair *)
val gPair : coq_expr * coq_expr -> coq_expr
val gProd : coq_expr * coq_expr -> coq_expr
val listToPairAux : (('a *'a) -> 'a) -> ('a list) -> 'a
val gTuple      : coq_expr list -> coq_expr
val gTupleType  : coq_expr list -> coq_expr
val dtTupleType : rocq_constr list -> rocq_constr

(* Int *)
val gInt : int -> coq_expr
val gSucc : coq_expr -> coq_expr
val maximum : coq_expr list -> coq_expr
val glt : coq_expr -> coq_expr -> coq_expr
val gle : coq_expr -> coq_expr -> coq_expr

(* Eq *)
val gEq : coq_expr -> coq_expr -> coq_expr

(* Maybe *)
val gOption : coq_expr -> coq_expr
val gNone : coq_expr -> coq_expr
val gSome : coq_expr -> coq_expr -> coq_expr
val gNone' : coq_expr
val gSome' : coq_expr -> coq_expr


(* boolean *)
val gNot   : coq_expr -> coq_expr
val g_true  : coq_expr
val g_false : coq_expr               
val decToBool : coq_expr -> coq_expr
val decOptToBool : coq_expr -> coq_expr
val gBool  : coq_expr
val gIf : coq_expr -> coq_expr -> coq_expr -> coq_expr

(* list *)

(* unit *)
val gUnit : coq_expr
val gTT   : coq_expr

(* dec *)
val g_dec : coq_expr -> coq_expr
val g_decOpt : coq_expr -> coq_expr -> coq_expr
val g_dec_decOpt : coq_expr

(* checker *)

val g_checker : coq_expr -> coq_expr


(* (\* Gen combinators *\) *)
val g_forAll : coq_expr -> coq_expr -> coq_expr
val g_arbitrary : coq_expr
val g_quickCheck : coq_expr -> coq_expr
val g_show : coq_expr -> coq_expr

(* val gGen : coq_expr -> coq_expr *)
(* val returnGen  : coq_expr -> coq_expr  *)
(* val bindGen    : coq_expr -> string -> (var -> coq_expr) -> coq_expr  *)
(* val bindGenOpt : coq_expr -> string -> (var -> coq_expr) -> coq_expr  *)

(* val oneof : coq_expr list -> coq_expr *)
(* val frequency : (coq_expr * coq_expr) list -> coq_expr *)
(* val backtracking : (coq_expr * coq_expr) list -> coq_expr *)
(* val uniform_backtracking : coq_expr list -> coq_expr *)

(* Recursion combinators / fold *)
val fold_ty  : ('a -> coq_type -> 'a) -> (ty_ctr * coq_type list -> 'a) -> (ty_param -> 'a) -> coq_type -> 'a
val fold_ty' : ('a -> coq_type -> 'a) -> 'a -> coq_type -> 'a 

val dep_fold_ty  : ('a -> rocq_constr -> 'a) -> ('a -> var -> rocq_constr -> 'a) ->
                   (ty_ctr * rocq_constr list -> 'a) -> (constructor * rocq_constr list -> 'a) -> 
                   (ty_param -> 'a) -> (var -> 'a) -> rocq_constr -> 'a

(* Generate Type Names *)
val generate_names_from_type : string -> coq_type -> string list 
val fold_ty_vars : (var list -> var -> coq_type -> 'a) -> ('a -> 'a -> 'a) -> 'a -> coq_type -> var list -> 'a

(* val defineConstant : string -> coq_expr -> var
   val defineTypedConstant : string -> coq_expr -> coq_expr -> var *)
val declare_class_instance
  : ?global:bool -> ?priority:int
  -> arg list -> string -> (var list -> coq_expr) -> (var list -> coq_expr)
  -> unit

val define_new_inductive : dep_dt -> unit

(* List utils *)
val list_last : 'a list -> 'a 
val list_init : 'a list -> 'a list 
val list_drop_every : int -> 'a list -> 'a list
val take_last : 'a list -> 'a list -> ('a list * 'a)
val list_insert_nth : 'a -> 'a list -> int -> 'a list

val sameTypeCtr  : ty_ctr -> coq_type -> bool
val isBaseBranch : ty_ctr -> coq_type -> bool
                                                
val find_typeclass_bindings : string -> ty_ctr -> (bool list) list

 *)
