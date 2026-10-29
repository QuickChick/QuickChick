open Names
open Declarations
open Constrexpr

type coq_expr

val interp_open_coq_expr : Environ.env -> Evd.evar_map -> 
  coq_expr -> EConstr.constr

val interp_coq_expr_evars : Environ.env -> Evd.evar_map ->
  coq_expr -> Evd.evar_map * EConstr.constr

val hole : coq_expr

val debug_coq_expr : coq_expr -> unit

type var
val var_to_string : var -> string
val gVar : var -> coq_expr

val gInject : string -> coq_expr


type ty_param 
val ty_param_to_string : ty_param -> string
val gTyParam : ty_param -> coq_expr

type ty_ctr
val ty_ctr_to_string : ty_ctr -> string
val gTyCtr : ty_ctr -> coq_expr
val tyCtrToQualid : ty_ctr -> Libnames.qualid

type arg
val gArg : ?assumName:coq_expr ->
           ?assumType:coq_expr ->
           ?assumImplicit:bool ->
           ?assumGeneralized:bool ->
           unit -> arg

  
val str_lst_to_string : string -> string list -> string

type coq_type = 
  | Arrow of coq_type * coq_type
  | TyCtr of ty_ctr * coq_type list
  | TyParam of ty_param

val coq_type_size : coq_type -> int

type constructor 
val constructor_to_string : constructor -> string
val gCtr : constructor -> coq_expr
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


type ctr_rep = constructor * coq_type 

(* single dt_rep *)
type sdt_rep = ty_ctr * ty_param list * ctr_rep list   
type dt_rep = sdt_rep list
 

(* Supertype of coq_type handling potentially dependent stuff - TODO : merge *)





val get_type : Id.t -> unit
val is_inductive : constructor -> bool




(* option type helpers *)
val isSome : 'a option -> bool
val foldM : ('b -> 'a -> 'b option) -> 'b option -> 'a list -> 'b option
val sequenceM : ('a -> 'b option) -> 'a list -> 'b list option
(* legacy function which fails on mutually inductive definitions *)
val sdt_rep_from_mib : mutual_inductive_body -> sdt_rep option

val qualid_to_mib : Libnames.qualid -> mutual_inductive_body
val dt_rep_from_mib : mutual_inductive_body -> dt_rep option
val coerce_reference_to_dt_rep : constr_expr -> dt_rep option



val fresh_name : string -> var 
val make_up_name : unit -> var

(* Generic Combinators *)
val gApp : ?explicit:bool -> coq_expr -> coq_expr list -> coq_expr 
val gFun : string list -> (var list -> coq_expr) -> coq_expr
val gRecFunIn : ?structRec:(var option) -> ?assumType:coq_expr -> string -> string list -> ((var * var list) -> coq_expr) -> (var -> coq_expr) -> coq_expr

(* TODO: HOAS-ify *)
  
val gMatch : coq_expr -> ?catchAll:(coq_expr option) -> ?params:(int) -> ?explicit_params:int -> ((constructor * string list * (var list -> coq_expr)) list) -> coq_expr
val gMatchReturn : coq_expr -> ?catchAll:(coq_expr option) -> string -> (var -> coq_expr) ->
  ((constructor * string list * (var list -> coq_expr)) list) -> coq_expr

val gRecord : (string * coq_expr) list -> coq_expr 

val gFunTyped : (string * coq_expr) list -> (var list -> coq_expr) -> coq_expr
val gFunWithArgs : arg list -> ((var list) -> coq_expr) -> coq_expr
val gRecFunInWithArgs : ?structRec:(var option) -> ?assumType:coq_expr -> string -> arg list -> ((var * var list) -> coq_expr) -> (var -> coq_expr) -> coq_expr

val gProdWithArgs : arg list -> ((var list) -> coq_expr) -> coq_expr

(* Specialized Pattern Matching *)

                    


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

(* Int *)
val gInt : int -> coq_expr
val gSucc : coq_expr -> coq_expr
val maximum : coq_expr list -> coq_expr
val gle : coq_expr -> coq_expr -> coq_expr

(* Eq *)
val gEq : coq_expr -> coq_expr -> coq_expr

(* Maybe *)
val gNone : coq_expr -> coq_expr
val gSome : coq_expr -> coq_expr -> coq_expr
val gNone' : coq_expr
val gSome' : coq_expr -> coq_expr


(* boolean *)
val g_true  : coq_expr
val g_false : coq_expr               
val decOptToBool : coq_expr -> coq_expr
val gIf : coq_expr -> coq_expr -> coq_expr -> coq_expr

(* list *)

(* unit *)
val gUnit : coq_expr
val gTT   : coq_expr

(* dec *)
val g_decOpt : coq_expr -> coq_expr -> coq_expr

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


(* Generate Type Names *)
val generate_names_from_type : string -> coq_type -> string list 
val fold_ty_vars : (var list -> var -> coq_type -> 'a) -> ('a -> 'a -> 'a) -> 'a -> coq_type -> var list -> 'a

(* val defineConstant : string -> coq_expr -> var
   val defineTypedConstant : string -> coq_expr -> coq_expr -> var *)
val declare_class_instance
  : ?global:bool -> ?priority:int
  -> arg list -> string -> (var list -> coq_expr) -> (var list -> coq_expr)
  -> unit


val define_new_fixpoint :
  (var * arg list * var * coq_expr * coq_expr) list -> unit

(* List utils *)
val list_drop_every : int -> 'a list -> 'a list
val list_keep_every : int -> 'a list -> 'a list  

val sameTypeCtr  : ty_ctr -> coq_type -> bool
val isBaseBranch : ty_ctr -> coq_type -> bool
                                                

                                           
