(* vars and type parameters will always be "local", constructors should be global *)
type var = Names.Id.t
type ty_param = Names.Id.t
type ty_ctr = Libnames.qualid
type constructor = Libnames.qualid

let var_to_string x = Names.Id.to_string x
let ty_param_to_string x = Names.Id.to_string x
let ty_ctr_to_string x = Libnames.string_of_qualid x
let constructor_to_string x = Libnames.string_of_qualid x

(* Wrapper around constr that we use to represent the types of
   inductives and theorems that we plan to derive for or quickcheck *)
type rocq_constr = 
  | DArrow of rocq_constr * rocq_constr (* Unnamed arrows *)
  | DProd  of (var * rocq_constr) * rocq_constr (* Binding arrows *)
  | DTyParam of ty_param (* Type parameters - for simplicity *)
  | DTyCtr of ty_ctr * rocq_constr list (* Type Constructor *)
  | DCtr of constructor * rocq_constr list (* Type Constructor *)
  | DTyVar of var (* Use of a previously captured type variable *)
  | DApp of rocq_constr * rocq_constr list (* Type-level function applications *)
  | DNot of rocq_constr (* Negation as a toplevel *)
  | DHole (* For adding holes *)

let rec rocq_constr_to_string (rc : rocq_constr) : string =
  match rc with 
  | DArrow (rc1, rc2) ->
     Printf.sprintf "%s -> %s" (rocq_constr_to_string rc1) (rocq_constr_to_string rc2)
  | DProd  ((x,rc1), rc2) ->
     Printf.sprintf "(%s : %s) -> %s" (var_to_string x) (rocq_constr_to_string rc1) (rocq_constr_to_string rc2)
  | DTyCtr (ty_ctr, []) ->
     ty_ctr_to_string ty_ctr
  | DTyCtr (ty_ctr, ds) ->
     "(" ^ ty_ctr_to_string ty_ctr ^ " " ^ String.concat " " (List.map rocq_constr_to_string ds) ^ ")"
  | DCtr (ctr, []) ->
     constructor_to_string ctr 
  | DCtr (ctr, ds) ->
     "(" ^ constructor_to_string ctr ^ " " ^ String.concat " "  (List.map rocq_constr_to_string ds) ^ ")"
  | DTyParam tp ->
     Printf.sprintf "(Param : %s)" (ty_param_to_string tp)
  | DTyVar tv ->
     var_to_string tv
  | DApp (d, ds) ->
     Printf.sprintf "(%s $ %s)" (rocq_constr_to_string d) (String.concat " " (List.map rocq_constr_to_string ds))
  | DNot d ->
     Printf.sprintf "~ ( %s )" (rocq_constr_to_string d)
  | DHole -> "_"

module OrdRocqConstr = struct
    type t = rocq_constr
    let compare = Stdlib.compare
end

type rocq_ctr = constructor * rocq_constr
let rocq_ctr_to_string (ctr,rc) =
  Printf.sprintf "%s : %s" (constructor_to_string ctr) (rocq_constr_to_string rc)

(* This represents an inductive relation in coq, e.g. "Inductive IsSorted (t : Type) : list t -> Prop := ...".
   This tuple is a wrapper around coq internals. *)
type rocq_relation
  = ty_ctr        (* The name of the relation (e.g. IsSorted) *)
  * ty_param list (* The list of type parameters (e.g. "t" in IsSorted) *)
  * rocq_ctr list (* A list of constructors. Each constructor is a pair (name, type) *)
  * rocq_constr   (* The type of the overall relation (e.g. "list t -> Prop") *)

let rocq_relation_to_string (ty_ctr, ty_params, ctrs, rc) = 
  Printf.sprintf "%s %s :=\n%s\n%s" (ty_ctr_to_string ty_ctr) 
                                    (String.concat " "  (List.map ty_param_to_string ty_params))
                                    (String.concat "\n" (List.map rocq_ctr_to_string  ctrs))
                                    (rocq_constr_to_string rc)

(* Given the name of an inductive, lookup its definition and 
   any other relations mutually defined with it. *)
let constr_to_rocq_constr (c : Constr.constr) : rocq_constr option =
  None

let qualid_to_rocq_relations (r : Libnames.qualid) : (int * rocq_relation * rocq_relation list) option =
  (* Locate all returns _all_ definitions with this suffix *)
  let lookup_results = Nametab.locate_all r in
  (* We look for the first one that is an inductive *)

  try begin
    let first_ind = List.find (fun x -> match x with
                                        | Names.GlobRef.IndRef _ -> true
                                        | _ -> false) lookup_results in
    match first_ind with
      | Names.GlobRef.IndRef ind ->
         failwith "Found something" (* Environ.lookup_mind (fst ind) (Global.env ()) *)
      | _ -> failwith ("No Inductives named: " ^ Libnames.string_of_qualid r)
    end
  with
    Not_found -> failwith "BETTER MESG"

let ind_reference_to_rocq_relations (c : Constrexpr.constr_expr) : (int * rocq_relation * rocq_relation list) option =
  let r = match c with
    | { CAst.v = Constrexpr.CRef (r,_);_ } -> r
    | _ -> failwith "Not a reference"
  in
  qualid_to_rocq_relations r

(* Patterns in language that derivations target *)
type pat =
  | PCtr of constructor * pat list
  | PVar of var
  | PParam (* Type parameter *)

(* TODO: Weights? *)
(* Deep AST of Language that derivations target *)
type mexp =
  | MBind    of mexp * var * mexp
    (* bind m1 (fun id => m2) *)
  | MBindOpt of mexp * var * mexp
    (* bindOpt m1 (fun id => m2) *)
  | MRet  of mexp
    (* ret m *)
  | MFail      (* Signifies failure *) 
  | MOutOfFuel (* Signifies failure due to fuel *)
  | MId of var
  | MApp of mexp * mexp list
  | MCtr of constructor * mexp list
  | MConst of string
  | MEscape of Constrexpr.constr_expr
  | MMatch of mexp * (pat * mexp) list 
  | MHole 
  | MLet of var * mexp * mexp 
  | MBacktrack of (mexp * mexp) list
  | MFun of pat list * mexp

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
val var_of_id : Id.t -> var   
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
  
val str_lst_to_string : string -> string list -> string

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


val dep_type_to_string : dep_type -> string

type dep_ctr = constructor * dep_type
val dep_ctr_to_string : dep_ctr -> string

type dep_dt = ty_ctr * ty_param list * dep_ctr list * dep_type
val dep_dt_to_string : dep_dt -> string

val constr_of_type : string -> ty_param list -> dep_type -> Constr.t
val gType : ty_param list -> dep_type -> coq_expr
val gType' : ty_param list -> dep_type -> coq_expr
val get_type : Id.t -> unit
val is_inductive : constructor -> bool
val is_inductive_dt : dep_type -> bool

val nthType : int -> dep_type -> dep_type

val dep_type_len : dep_type -> int

val dep_result_type : dep_type -> dep_type

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

val parse_dependent_type : Constr.constr -> dep_type option

val dep_dt_from_mib : mutual_inductive_body -> dep_dt option
val coerce_reference_to_dep_dt : constr_expr -> dep_dt option

val fresh_name : string -> var 
val make_up_name : unit -> var

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
val dtTupleType : dep_type list -> dep_type

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

val dep_fold_ty  : ('a -> dep_type -> 'a) -> ('a -> var -> dep_type -> 'a) ->
                   (ty_ctr * dep_type list -> 'a) -> (constructor * dep_type list -> 'a) -> 
                   (ty_param -> 'a) -> (var -> 'a) -> dep_type -> 'a

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
