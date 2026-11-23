open Names
open Declarations
open Constrexpr

type rocq_expr

val interp_open_rocq_expr : Environ.env -> Evd.evar_map -> 
  rocq_expr -> EConstr.constr

val interp_rocq_expr_evars : Environ.env -> Evd.evar_map ->
  rocq_expr -> Evd.evar_map * EConstr.constr

val hole : rocq_expr

val debug_rocq_expr : rocq_expr -> unit

type var
val var_to_string : var -> string
val gVar : var -> rocq_expr

val gInject : string -> rocq_expr


type ty_param 
val ty_param_to_string : ty_param -> string
val gTyParam : ty_param -> rocq_expr

type ty_ctr
val ty_ctr_to_string : ty_ctr -> string
val gTyCtr : ty_ctr -> rocq_expr
val tyCtrToQualid : ty_ctr -> Libnames.qualid

type arg
val gArg : ?assumName:rocq_expr ->
           ?assumType:rocq_expr ->
           ?assumImplicit:bool ->
           ?assumGeneralized:bool ->
           unit -> arg

  
val str_lst_to_string : string -> string list -> string

type rocq_type = 
  | Arrow of rocq_type * rocq_type
  | TyCtr of ty_ctr * rocq_type list
  | TyParam of ty_param

val rocq_type_size : rocq_type -> int

type constructor 
val constructor_to_string : constructor -> string
(* The constructor's own name, without the qualification that denotes it. *)
val constructor_basename : constructor -> string
val gCtr : constructor -> rocq_expr
val injectCtr : string -> constructor

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


type ctr_rep = constructor * rocq_type 

(* single dt_rep *)
type sdt_rep = ty_ctr * ty_param list * ctr_rep list   
type dt_rep = sdt_rep list
 

(* Supertype of rocq_type that may be dependent. *)





val get_type : Id.t -> unit
val is_inductive : constructor -> bool




(* option type helpers *)
val isSome : 'a option -> bool
val foldM : ('b -> 'a -> 'b option) -> 'b option -> 'a list -> 'b option
val sequenceM : ('a -> 'b option) -> 'a list -> 'b list option
(* legacy function which fails on mutually inductive definitions *)
val sdt_rep_from_mib : mutual_inductive_body -> sdt_rep option

val qualid_to_mib : Libnames.qualid -> mutual_inductive_body
val dt_rep_from_mib : ?mind:Names.MutInd.t -> mutual_inductive_body -> dt_rep option
val coerce_reference_to_dt_rep : constr_expr -> dt_rep option



val fresh_name : string -> var 
val make_up_name : unit -> var

(* Generic Combinators *)
val gApp : ?explicit:bool -> rocq_expr -> rocq_expr list -> rocq_expr 
val gFun : string list -> (var list -> rocq_expr) -> rocq_expr
val gRecFunIn : ?structRec:(var option) -> ?assumType:rocq_expr -> string -> string list -> ((var * var list) -> rocq_expr) -> (var -> rocq_expr) -> rocq_expr

  
val gMatch : rocq_expr -> ?catchAll:(rocq_expr option) -> ?params:(int) -> ?explicit_params:int -> ((constructor * string list * (var list -> rocq_expr)) list) -> rocq_expr
val gMatchReturn : rocq_expr -> ?catchAll:(rocq_expr option) -> string -> (var -> rocq_expr) ->
  ((constructor * string list * (var list -> rocq_expr)) list) -> rocq_expr

val gRecord : (string * rocq_expr) list -> rocq_expr 

val gFunTyped : (string * rocq_expr) list -> (var list -> rocq_expr) -> rocq_expr
val gFunWithArgs : arg list -> ((var list) -> rocq_expr) -> rocq_expr
val gRecFunInWithArgs : ?structRec:(var option) -> ?assumType:rocq_expr -> string -> arg list -> ((var * var list) -> rocq_expr) -> (var -> rocq_expr) -> rocq_expr

val gProdWithArgs : arg list -> ((var list) -> rocq_expr) -> rocq_expr

(* Specialized Pattern Matching *)

                    


(* Generic List Manipulations *)
val list_nil : rocq_expr
val lst_append : rocq_expr -> rocq_expr -> rocq_expr
val lst_appends : rocq_expr list -> rocq_expr
val gCons : rocq_expr -> rocq_expr -> rocq_expr 
val gList : rocq_expr list -> rocq_expr

(* Generic String Manipulations *)
val gStr : string -> rocq_expr
val emptyString : rocq_expr 
val str_append  : rocq_expr -> rocq_expr -> rocq_expr 
val str_appends : rocq_expr list -> rocq_expr
val smart_paren : rocq_expr -> rocq_expr

(* Pair *)
val gPair : rocq_expr * rocq_expr -> rocq_expr
val gProd : rocq_expr * rocq_expr -> rocq_expr

(* Int *)
val gInt : int -> rocq_expr
val gSucc : rocq_expr -> rocq_expr
val maximum : rocq_expr list -> rocq_expr
val gle : rocq_expr -> rocq_expr -> rocq_expr

(* Eq *)
val gEq : rocq_expr -> rocq_expr -> rocq_expr

(* Maybe *)
val gNone : rocq_expr -> rocq_expr
val gSome : rocq_expr -> rocq_expr -> rocq_expr
val gNone' : rocq_expr
val gSome' : rocq_expr -> rocq_expr


(* boolean *)
val g_true  : rocq_expr
val g_false : rocq_expr               
val decOptToBool : rocq_expr -> rocq_expr
val gIf : rocq_expr -> rocq_expr -> rocq_expr -> rocq_expr

(* list *)

(* unit *)
val gUnit : rocq_expr
val gTT   : rocq_expr

(* dec *)
val g_decOpt : rocq_expr -> rocq_expr -> rocq_expr

(* checker *)

val g_checker : rocq_expr -> rocq_expr


(* (\* Gen combinators *\) *)
val g_forAll : rocq_expr -> rocq_expr -> rocq_expr
val g_arbitrary : rocq_expr
val g_quickCheck : rocq_expr -> rocq_expr
val g_show : rocq_expr -> rocq_expr

(* val gGen : rocq_expr -> rocq_expr *)
(* val returnGen  : rocq_expr -> rocq_expr  *)
(* val bindGen    : rocq_expr -> string -> (var -> rocq_expr) -> rocq_expr  *)
(* val bindGenOpt : rocq_expr -> string -> (var -> rocq_expr) -> rocq_expr  *)

(* val oneof : rocq_expr list -> rocq_expr *)
(* val frequency : (rocq_expr * rocq_expr) list -> rocq_expr *)
(* val backtracking : (rocq_expr * rocq_expr) list -> rocq_expr *)
(* val uniform_backtracking : rocq_expr list -> rocq_expr *)

(* Recursion combinators / fold *)
val fold_ty  : ('a -> rocq_type -> 'a) -> (ty_ctr * rocq_type list -> 'a) -> (ty_param -> 'a) -> rocq_type -> 'a
val fold_ty' : ('a -> rocq_type -> 'a) -> 'a -> rocq_type -> 'a 


(* Generate Type Names *)
val generate_names_from_type : string -> rocq_type -> string list 
val fold_ty_vars : (var list -> var -> rocq_type -> 'a) -> ('a -> 'a -> 'a) -> 'a -> rocq_type -> var list -> 'a

(* val defineConstant : string -> rocq_expr -> var
   val defineTypedConstant : string -> rocq_expr -> rocq_expr -> var *)
val declare_class_instance
  : ?global:bool -> ?priority:int
  -> arg list -> string -> (var list -> rocq_expr) -> (var list -> rocq_expr)
  -> unit


val mentions : var list -> rocq_expr -> bool
val inline_functions : (var * (arg list * rocq_expr)) list -> rocq_expr -> rocq_expr
val define_new_fixpoint :
  (var * arg list * var * rocq_expr * rocq_expr) list -> unit

(* List utils *)
val list_drop_every : int -> 'a list -> 'a list
val list_keep_every : int -> 'a list -> 'a list  

val sameTypeCtr  : ty_ctr -> rocq_type -> bool
val isBaseBranch : ty_ctr -> rocq_type -> bool
                                                

                                           
