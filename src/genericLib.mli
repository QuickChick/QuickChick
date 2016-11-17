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

(* option type helpers *)
val (>>=) : 'a option -> ('a -> 'b option) -> 'b option                                   
val isSome : 'a option -> bool
val cat_maybes : 'a option list -> 'a list
val foldM : ('b -> 'a -> 'b option) -> 'b option -> 'a list -> 'b option
val sequenceM : ('a -> 'b option) -> 'a list -> 'b list option

val dt_rep_from_mib : mutual_inductive_body -> dt_rep option
val coerce_reference_to_dt_rep : constr_expr -> dt_rep option

val fresh_name : string -> var 
val make_up_name : unit -> var

(* Generic Combinators *)
val gApp : ?explicit:bool -> coq_expr -> coq_expr list -> coq_expr 
val gFun : string list -> (var list -> coq_expr) -> coq_expr
val gFunTyped : (string * coq_expr) list -> (var list -> coq_expr) -> coq_expr

val gRecFunInWithArgs : string -> arg list -> ((var * var list) -> coq_expr) -> (var -> coq_expr) -> coq_expr
val gRecFunIn : string -> string list -> ((var * var list) -> coq_expr) -> (var -> coq_expr) -> coq_expr

val gMatch : coq_expr -> ((constructor * string list * (var list -> coq_expr)) list) -> coq_expr

val gRecord : (string * coq_expr) list -> coq_expr 

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
val gInt : int -> coq_expr
val gSucc : coq_expr -> coq_expr
val maximum : coq_expr list -> coq_expr
val glt : coq_expr -> coq_expr -> coq_expr
val gle : coq_expr -> coq_expr -> coq_expr
                          
(* Gen combinators *)
val returnGen : coq_expr -> coq_expr 
val bindGen : coq_expr -> string -> (var -> coq_expr) -> coq_expr 

val oneof : coq_expr list -> coq_expr
val frequency : (coq_expr * coq_expr) list -> coq_expr

(* Recursion combinators / fold *)
val fold_ty  : ('a -> coq_type -> 'a) -> (ty_ctr * coq_type list -> 'a) -> (ty_param -> 'a) -> coq_type -> 'a
val fold_ty' : ('a -> coq_type -> 'a) -> 'a -> coq_type -> 'a 

(* Generate Type Names *)
val generate_names_from_type : string -> coq_type -> string list 
val fold_ty_vars : (var list -> var -> coq_type -> 'a) -> ('a -> 'a -> 'a) -> 'a -> coq_type -> var list -> 'a

val defineConstant : string -> coq_expr -> var
val declare_class_instance : arg list -> string -> coq_expr -> (var list -> coq_expr) -> unit 
