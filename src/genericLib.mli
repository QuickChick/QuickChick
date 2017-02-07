open Decl_kinds
open Pp
open Term
open Loc
open Names
open Tacmach
open Entries
open Declarations
open Declare
open Libnames
open Util
open Constrintern
open Topconstr
open Constrexpr
open Constrexpr_ops
open Context

type coq_expr

val hole : coq_expr

val debug_coq_expr : coq_expr -> unit

type var 

val gVar : var -> coq_expr

val gInject : string -> coq_expr 

type ty_param 
val ty_param_to_string : ty_param -> string
val gTyParam : ty_param -> coq_expr

type ty_ctr
val ty_ctr_to_string : ty_ctr -> string
val gTyCtr : ty_ctr -> coq_expr

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

val coq_type_to_string : coq_type -> string

type constructor 
val constructor_to_string : constructor -> string
val gCtr : constructor -> coq_expr
val injectCtr : string -> constructor

type ctr_rep = constructor * coq_type 
val ctr_rep_to_string : ctr_rep -> string

type dt_rep = ty_ctr * ty_param list * ctr_rep list
val dt_rep_to_string : dt_rep -> string

type ty_var 
val ty_var_to_string : ty_var -> string
val gTyVar : ty_var -> coq_expr

(* Supertype of coq_type handling potentially dependent stuff - TODO : merge *)
type dep_type = 
  | DArrow of dep_type * dep_type (* Unnamed arrows *)
  | DProd  of (ty_var * dep_type) * dep_type (* Binding arrows *)
  | DTyParam of ty_param (* Type parameters - for simplicity *)
  | DTyCtr of ty_ctr * dep_type list (* Type Constructor *)
  | DCtr of constructor * dep_type list (* Type Constructor *)
  | DTyVar of ty_var (* Use of a previously captured type variable *)

val dep_type_to_string : dep_type -> string

type dep_ctr = constructor * dep_type
val dep_ctr_to_string : dep_ctr -> string

type dep_dt = ty_ctr * ty_param list * dep_ctr list * dep_type
val dep_dt_to_string : dep_dt -> string

val gType : ty_param list -> dep_type -> coq_expr

val nthType : int -> dep_type -> dep_type

val dep_result_type : dep_type -> dep_type

(* option type helpers *)
val (>>=) : 'a option -> ('a -> 'b option) -> 'b option                                   
val isSome : 'a option -> bool
val cat_maybes : 'a option list -> 'a list
val foldM : ('b -> 'a -> 'b option) -> 'b option -> 'a list -> 'b option
val sequenceM : ('a -> 'b option) -> 'a list -> 'b list option

val dt_rep_from_mib : mutual_inductive_body -> dt_rep option
val coerce_reference_to_dt_rep : constr_expr -> dt_rep option

val dep_dt_from_mib : mutual_inductive_body -> dep_dt option
val coerce_reference_to_dep_dt : constr_expr -> dep_dt option

val fresh_name : string -> var 
val make_up_name : unit -> var

(* Generic Combinators *)
val gApp : ?explicit:bool -> coq_expr -> coq_expr list -> coq_expr 
val gFun : string list -> (var list -> coq_expr) -> coq_expr
val gRecFunIn : ?assumType:coq_expr -> string -> string list -> ((var * var list) -> coq_expr) -> (var -> coq_expr) -> coq_expr
val gMatch : coq_expr -> ((constructor * string list * (var list -> coq_expr)) list) -> coq_expr

val gRecord : (string * coq_expr) list -> coq_expr 

val gAnnot : coq_expr -> coq_expr -> coq_expr
val gFunTyped : (string * coq_expr) list -> (var list -> coq_expr) -> coq_expr
val gFunWithArgs : arg list -> ((var list) -> coq_expr) -> coq_expr
val gRecFunInWithArgs : ?assumType:coq_expr -> string -> arg list -> ((var * var list) -> coq_expr) -> (var -> coq_expr) -> coq_expr

val gProdWithArgs : arg list -> ((var list) -> coq_expr) -> coq_expr

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

(* Pair *)
val gPair : coq_expr * coq_expr -> coq_expr 

(* Int *)
val parse_integer : constr_expr -> int

val gInt : int -> coq_expr
val gSucc : coq_expr -> coq_expr
val maximum : coq_expr list -> coq_expr
val glt : coq_expr -> coq_expr -> coq_expr
val gle : coq_expr -> coq_expr -> coq_expr

(* Eq *)
val gEq : coq_expr -> coq_expr -> coq_expr

(* Maybe *)
val gOption : coq_expr -> coq_expr
val gNone : coq_expr
val gSome : coq_expr -> coq_expr              

(* Gen combinators *)
val gGen : coq_expr -> coq_expr
val returnGen  : coq_expr -> coq_expr 
val bindGen    : coq_expr -> string -> (var -> coq_expr) -> coq_expr 
val bindGenOpt : coq_expr -> string -> (var -> coq_expr) -> coq_expr 

val oneof : coq_expr list -> coq_expr
val frequency : (coq_expr * coq_expr) list -> coq_expr

(* Recursion combinators / fold *)
val fold_ty  : ('a -> coq_type -> 'a) -> (ty_ctr * coq_type list -> 'a) -> (ty_param -> 'a) -> coq_type -> 'a
val fold_ty' : ('a -> coq_type -> 'a) -> 'a -> coq_type -> 'a 

val dep_fold_ty  : ('a -> dep_type -> 'a) -> ('a -> ty_var -> dep_type -> 'a) ->
                   (ty_ctr * dep_type list -> 'a) -> (constructor * dep_type list -> 'a) -> 
                   (ty_param -> 'a) -> (ty_var -> 'a) -> dep_type -> 'a

(* Generate Type Names *)
val generate_names_from_type : string -> coq_type -> string list 
val fold_ty_vars : (var list -> var -> coq_type -> 'a) -> ('a -> 'a -> 'a) -> 'a -> coq_type -> var list -> 'a

val defineConstant : string -> coq_expr -> var
val defineTypedConstant : string -> coq_expr -> coq_expr -> var
val declare_class_instance : arg list -> string -> (var list -> coq_expr) -> (var list -> coq_expr) -> unit 
