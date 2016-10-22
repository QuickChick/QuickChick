open Pp
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

(* Everything marked "Opaque" should have its implementation be hidden in the .mli *)

(* Non-dependent version *)
type var = reference (* Opaque *)

type coq_expr = constr_expr (* Opaque *)

type ty_param = Id.t (* Opaque *)
let ty_param_to_string (x : Id.t) = Id.to_string x
                  
type ty_ctr   = Id.t (* Opaque *)
let ty_ctr_to_string (x : ty_ctr) = Id.to_string x

type coq_type = 
  | Arrow of coq_type * coq_type
  | TyCtr of ty_ctr * coq_type list
  | TyParam of ty_param

type constructor = string (* Opaque *)

type ctr_rep = constructor * coq_type 

type dt_rep = ty_ctr * ty_param list * ctr_rep list

let (>>=) m f = 
  match m with
  | Some x -> f x 
  | None -> None

let isSome m = 
  match m with 
  | Some _ -> true
  | None   -> false
              
let rec cat_maybes = function 
  | [] -> []
  | (Some x :: mxs) -> x :: cat_maybes mxs
  | None :: mxs -> cat_maybes mxs

let parse_type_params arity_ctxt =
  let param_names =
    List.fold_left (fun accm (n, _, c) ->
                      accm >>= fun acc ->
                      match n with
                      | Name id   -> Some (id  :: acc)
                      | Anonymous -> msgerr (str "Unnamed type parameter?" ++ fnl ()); None
                   ) (Some []) arity_ctxt in
  param_names
(* For /trunk 
    Rel.fold_inside
      (fun accm decl ->
       accm >>= fun acc ->
       match Rel.Declaration.get_name decl with
       | Name id -> Some (id :: acc)
       | Anonymous -> msgerr (str "Unnamed type parameter?" ++ fnl ()); None
      ) [] arity_ctxt in 
  param_names
*)

(* Receives number of type parameters and one_inductive_body.
   -> Possibly ty_param list as well? 
   Returns list of constructor representations 
 *)                               
let parse_constructors nparams oib =
  
  let parse_constructor branch =
    let (ctr_id, ty_ctr) = branch in

    let (_, ty) = Term.decompose_prod_n nparams ty_ctr in
    
    let ctr_pats = if Term.isConst ty then [] else fst (Term.decompose_prod ty) in

    let _, pat_types = List.split (List.rev ctr_pats)
    in 42 
  in Some []
(*        (List.combine (Array.to_list oib.mind_consnames)
                      (Array.to_list oib.mind_nf_lc))) in
 *)                                                     
                            
(* Convert mutual_inductive_body to this representation, if possible *)
let dt_rep_from_mib mib = 
  if Array.length mib.mind_packets > 1 then begin
    msgerr (str "Mutual inductive types not supported yet." ++ fnl());
    None
  end else 
    let oib = mib.mind_packets.(0) in
    let ty_ctr = oib.mind_typename in 
    (* TODO: Parse parameters *)
    parse_type_params oib.mind_arity_ctxt >>= fun ty_params ->
    parse_constructors mib.mind_nparams oib >>= fun ctr_reps ->
    Some (ty_ctr, ty_params, ctr_reps)
                  
let fresh_name n =
    let base = Names.id_of_string n in

  (** [is_visible_name id] returns [true] if [id] is already
      used on the Coq side. *)
    let is_visible_name id =
      try
        ignore (Nametab.locate (Libnames.qualid_of_ident id));
        true
      with Not_found -> false
    in
    (** Safe fresh name generation. *)
    Namegen.next_ident_away_from base is_visible_name

let dl x = (dummy_loc, x) 
let hole = CHole (dummy_loc, None, Misctypes.IntroAnonymous, None)

let gRecFunIn fs xss f_body let_body = 
  let fv  = fresh_name fs in
  let xvs = List.map fresh_name xss in
  (* TODO: optional argument types for xss *)
  let binder_list = List.map (fun x -> LocalRawAssum ([(dummy_loc, Name x)], Default Explicit, hole)) xvs in

  let fix_body = f_body (fv, xvs) in
  CLetIn (dummy_loc, dl (Name fv), 
          G_constr.mk_fix (dummy_loc, true, dl fv, [(dl fv, binder_list, (None, CStructRec), fix_body, (dl None))]),
          let_body fv)

let gMatch discr branches = (* val gMatch : coq_expr -> (string * string list * (var list -> coq_expr)) list -> coq_expr *)
  (* Extract the constructors of coq_expr *)
  CCases (dummy_loc,
          Term.RegularStyle,
          None (* return *), 
          [(discr, (None, None))], (* single discriminee, no as/in *)
          List.map (fun (c, cs, bf) -> 
                      let cvs = List.map fresh_name cs in
                      (dummy_loc,
                       [dl [CPatCstr (dummy_loc,
                                      Ident (dl (id_of_string c)), (* constructor name *)
                                      [],
                                      List.map (fun s -> CPatAtom (dummy_loc, Some (Ident (dl s)))) cvs (* Constructor applied to patterns *)
                                     )
                           ]
                       ],
                       bf cvs
                      )
                   ) branches)

