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

let dl x = (dummy_loc, x) 
let hole = CHole (dummy_loc, None, Misctypes.IntroAnonymous, None)

(* Everything marked "Opaque" should have its implementation be hidden in the .mli *)

(* Non-dependent version *)
type var = Id.t (* Opaque *)

let gVar x = CRef (Ident (dl x),None)

type coq_expr = constr_expr (* Opaque *)

(* Maybe this should do checks? *)
let gInject s = CRef (Qualid (Loc.ghost, qualid_of_string s), None)

type ty_param = Id.t (* Opaque *)
let ty_param_to_string (x : Id.t) = Id.to_string x

let gTyParam = mkIdentC

type ty_ctr   = Id.t (* Opaque *)
let ty_ctr_to_string (x : ty_ctr) = Id.to_string x

let gTyCtr = mkIdentC

let gArg ?assumName:(an=hole) ?assumType:(at=hole) ?assumImplicit:(ai=false) ?assumGeneralized:(ag=false) _ =
  LocalRawAssum ( [coerce_to_name an],
                  (if ag then Generalized (Implicit, Implicit, false)                       
                   else if ai then Default Implicit else Default Explicit),
                  at )
               
let str_lst_to_string sep (ss : string list) = 
  List.fold_left (fun acc s -> acc ^ sep ^ s) "" ss

type coq_type = 
  | Arrow of coq_type * coq_type
  | TyCtr of ty_ctr * coq_type list
  | TyParam of ty_param

let rec coq_type_to_string ct = 
  match ct with
  | Arrow (c1, c2) -> Printf.sprintf "%s -> %s" (coq_type_to_string c1) (coq_type_to_string c2)
  | TyCtr (ty_ctr, cs) -> ty_ctr_to_string ty_ctr ^ " " ^ str_lst_to_string " " (List.map coq_type_to_string cs)
  | TyParam tp -> ty_param_to_string tp

type constructor = Id.t (* Opaque *)
let constructor_to_string (x : constructor) = Id.to_string x

type ctr_rep = constructor * coq_type 
let ctr_rep_to_string (ctr, ct) = 
  Printf.sprintf "%s : %s" (constructor_to_string ctr) (coq_type_to_string ct)

type dt_rep = ty_ctr * ty_param list * ctr_rep list
let dt_rep_to_string (ty_ctr, ty_params, ctrs) = 
  Printf.sprintf "%s %s :=\n%s" (ty_ctr_to_string ty_ctr) 
                                (str_lst_to_string " "  (List.map ty_param_to_string ty_params))
                                (str_lst_to_string "\n" (List.map ctr_rep_to_string  ctrs))
                                 

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

let foldM f b l = List.fold_left (fun accm x -> 
                                  accm >>= fun acc ->
                                  f acc x
                                 ) b l
let sequenceM f l = 
  (foldM (fun acc x -> f x >>= fun x' -> Some (x' :: acc)) (Some []) l) >>= fun l -> Some (List.rev l)

let parse_type_params arity_ctxt =
  let param_names =
    foldM (fun acc (n, _, _) -> 
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

let rec arrowify terminal l = 
  match l with
  | [] -> terminal
  | x::xs -> Arrow (x, arrowify terminal xs)

(* Receives number of type parameters and one_inductive_body.
   -> Possibly ty_param list as well? 
   Returns list of constructor representations 
 *)                               
let parse_constructors nparams param_names result_ty oib : ctr_rep list option =
  
  let parse_constructor branch =
    let (ctr_id, ty_ctr) = branch in

    let (_, ty) = Term.decompose_prod_n nparams ty_ctr in
    
    let ctr_pats = if Term.isConst ty then [] else fst (Term.decompose_prod ty) in

    let _, pat_types = List.split (List.rev ctr_pats) in

    msgerr (str (Id.to_string ctr_id) ++ fnl ());
    let rec aux i ty = 
      if isRel ty then begin 
        msgerr (int (i + nparams) ++ str " Rel " ++ int (destRel ty) ++ fnl ());
        let db = destRel ty in
        if i + nparams = db then (* Current inductive, no params *)
          Some (TyCtr (oib.mind_typename, []))
        else (* [i + nparams - db]th parameter *)
          try Some (TyParam (List.nth param_names (i + nparams - db - 1)))
          with _ -> msgerr (str "nth failed: " ++ int (i + nparams - db - 1) ++ fnl ()); None
      end 
      else if isApp ty then begin
        let (ctr, tms) = decompose_app ty in 
        foldM (fun acc ty -> 
               aux i ty >>= fun ty' -> Some (ty' :: acc)
              ) (Some []) tms >>= fun tms' ->
        match aux i ctr with
        | Some (TyCtr (c, _)) -> Some (TyCtr (c, List.rev tms'))
(*        | Some (TyParam p) -> Some (TyCtr (p, tms')) *)
        | None -> msgerr (str "Aux failed?" ++ fnl ()); None
      end
      else if isInd ty then begin
        let ((mind,_),_) = destInd ty in
        Some (TyCtr (Label.to_id (MutInd.label mind), []))
      end
      else (msgerr (str "Case Not Handled" ++ fnl()); None)

    in sequenceM (fun x -> x) (List.mapi aux (List.map (Vars.lift (-1)) pat_types)) >>= fun types ->
       Some (ctr_id, arrowify result_ty types)
  in

  sequenceM parse_constructor (List.combine (Array.to_list oib.mind_consnames)
                                            (Array.to_list oib.mind_nf_lc))
                            
(* Convert mutual_inductive_body to this representation, if possible *)
let dt_rep_from_mib mib = 
  if Array.length mib.mind_packets > 1 then begin
    msgerr (str "Mutual inductive types not supported yet." ++ fnl());
    None
  end else 
    let oib = mib.mind_packets.(0) in
    let ty_ctr = oib.mind_typename in 
    parse_type_params oib.mind_arity_ctxt >>= fun ty_params ->
    let result_ctr = TyCtr (ty_ctr, List.map (fun x -> TyParam x) ty_params) in
    parse_constructors mib.mind_nparams ty_params result_ctr oib >>= fun ctr_reps ->
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

let gApp ?explicit:(expl=false) c cs =
  if expl then
    match c with
    | CRef (r,_) -> CAppExpl (dummy_loc, (None, r, None), cs)
    | _ -> failwith "invalid argument to gApp"
  else mkAppC (c, cs)

let gFun xss f_body =
  let xvs = List.map (fun x -> fresh_name x) xss in
  (* TODO: optional argument types for xss *)
  let binder_list = List.map (fun x -> LocalRawAssum ([(dummy_loc, Name x)], Default Explicit, hole)) xvs in
  let fun_body = f_body xvs in
  mkCLambdaN dummy_loc binder_list fun_body 
                  
let gRecFunIn fs xss f_body let_body = 
  let fv  = fresh_name fs in
  let xvs = List.map fresh_name xss in
  (* TODO: optional argument types for xss *)
  let binder_list = List.map (fun x -> LocalRawAssum ([(dummy_loc, Name x)], Default Explicit, hole)) xvs in

  let fix_body = f_body (fv, xvs) in
  CLetIn (dummy_loc, dl (Name fv), 
          G_constr.mk_fix (dummy_loc, true, dl fv, [(dl fv, binder_list, (None, CStructRec), fix_body, (dl None))]),
          let_body fv)

let gMatch discr branches = (* val gMatch : coq_expr -> (constructor * string list * (var list -> coq_expr)) list -> coq_expr *)
  CCases (dummy_loc,
          Term.RegularStyle,
          None (* return *), 
          [(discr, (None, None))], (* single discriminee, no as/in *)
          List.map (fun (c, cs, bf) -> 
                      let cvs = List.map fresh_name cs in
                      (dummy_loc,
                       [dl [CPatCstr (dummy_loc,
                                      Ident (dl c), (* constructor  *)
                                      [],
                                      List.map (fun s -> CPatAtom (dummy_loc, Some (Ident (dl s)))) cvs (* Constructor applied to patterns *)
                                     )
                           ]
                       ],
                       bf cvs
                      )
                   ) branches)

let gRecord names_and_bodies =
  CRecord (dummy_loc, None, List.map (fun (n,b) -> (Ident (dummy_loc, id_of_string n), b)) names_and_bodies)


(* Generic String Manipulations *)
let gStr s = CPrim (dummy_loc, String s)
let emptyString = gInject "Coq.Strings.String.EmptyString"
let str_append c1 c2 = gApp (gInject "Coq.Strings.String.append") [c1; c2]
let rec str_appends cs = 
  match cs with 
  | []  -> emptyString
  | [c] -> c
  | c1::cs' -> str_append c1 (str_appends cs')

