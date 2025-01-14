open Pp
open Error
open Constrexpr_ops

let cnt = ref 0 

let fresh_name n : Names.Id.t =
    let base = Names.Id.of_string n in

  (* [is_visible_name id] returns [true] if [id] is already
     used on the Coq side. *)
    let is_visible_name id =
      try
        ignore (Nametab.locate (Libnames.qualid_of_ident id));
        true
      with Not_found -> false
    in
    (* Safe fresh name generation. *)
    Namegen.next_ident_away_from base is_visible_name

let make_up_name () : Names.Id.t =
  let id = fresh_name (Printf.sprintf "mu%d_" (!cnt)) in
  cnt := !cnt + 1;
  id

(* Option monad - should probably be separated out*)
let option_map f ox =
  match ox with
  | Some x -> Some (f x)
  | None -> None
 
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

let debug_constr (c : Constr.constr) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Printer.safe_pr_constr_env env sigma c

(* vars and type parameters will always be "local", constructors should be global *)
type var = Names.Id.t
type ty_param = Names.Id.t
type ty_ctr = Libnames.qualid
type constructor = Libnames.qualid

let var_to_string x = Names.Id.to_string x
let var_of_string x = Names.Id.of_string x
let ty_param_to_string x = Names.Id.to_string x
let ty_ctr_to_string x = Libnames.string_of_qualid x
let ty_ctr_of_string x = Libnames.qualid_of_string x
let constructor_to_string x = Libnames.string_of_qualid x
let constructor_of_string x = Libnames.qualid_of_string x

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

(* Input : arity_ctxt [Name, Body (option) {expected None}, Type] 
   In reverse order.
   ASSUME: all type parameters are first
   Output: all type parameters (named arguments of type : Type) in correct order 
*)
let dep_parse_type_params arity_ctxt =
  let param_names =
    foldM (fun acc decl -> 
           match Context.Rel.Declaration.get_name decl with
           | Names.Name id -> 
              (* Actual parameters are named of type Type with some universe *)
              if Constr.is_Type (Context.Rel.Declaration.get_type decl) then Some (id :: acc) else Some acc
           | _ -> (* Ignore *) Some acc
          ) (Some []) arity_ctxt in
  param_names

let rec dep_arrowify terminal names types = 
  match names, types with
  | [], [] -> terminal
  | (Names.Name x)::ns , t::ts -> DProd ((x,t), dep_arrowify terminal ns ts)
  | Names.Anonymous::ns, t::ts -> DArrow (t, dep_arrowify terminal ns ts)
  | _, _ -> failwith "Invalid argument to dep_arrowify"

(* parse a type into a dep_type option 
   i : index of product (for DeBruijn)
   nparams : number of <Type> parameters in the beginning
   arg_names : argument names (type parameters, pattern specific variables 
 *)
let parse_dependent_type_internal i nparams ty oibopt arg_names =
  let rec aux i ty =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    msg_debug (str "Calling aux with: " ++ int i ++ str " "
               ++ Printer.pr_constr_env env sigma ty ++ fnl()); 
    if Constr.isRel ty then begin 
  (*        msgerr (int (i + nparams) ++ str " Rel " ++ int (destRel ty) ++ fnl ()); *)
      let db = Constr.destRel ty in
      if i + nparams = db then (* Current inductive, no params *)
        Some (DTyCtr (Libnames.qualid_of_ident (let Some oib = oibopt in oib.Declarations.mind_typename), []))
      else begin (* [i + nparams - db]th parameter *) 
        msg_debug (str (Printf.sprintf "Non-self-rel: %s" (rocq_constr_to_string (List.nth arg_names (i + nparams - db - 1)))) ++ fnl ());
        try Some (List.nth arg_names (i + nparams - db - 1))
        with _ -> CErrors.user_err (str "nth failed: " ++ int i ++ str " " ++ int nparams ++ str " " ++ int db ++ str " " ++ int (i + nparams - db - 1) ++ fnl ())
        end
    end 
    else if Constr.isApp ty then begin
      let (ctr, tms) = Constr.decompose_app_list ty in
      foldM (fun acc ty -> 
             aux i ty >>= fun ty' -> Some (ty' :: acc)
            ) (Some []) tms >>= fun tms' ->
      match aux i ctr with
      | Some (DTyCtr (c, _)) -> Some (DTyCtr (c, List.rev tms'))
      | Some (DCtr (c, _)) -> Some (DCtr (c, List.rev tms'))
      | Some (DTyVar x) -> 
         let xs = var_to_string x in 
         if xs = "Coq.Init.Logic.not" || xs = "not" then 
           match tms' with 
           | [c] -> Some (DNot c)
           | _   -> failwith "Not a valid negation"
         else Some (DApp (DTyVar x, List.rev tms'))
      | Some wat -> CErrors.user_err (str ("WAT: " ^ rocq_constr_to_string wat) ++ fnl ())
      | None -> CErrors.user_err (str "Aux failed?" ++ fnl ())
    end
    else if Constr.isInd ty then begin
      let ((mind, midx),_) = Constr.destInd ty in
      let mib = Environ.lookup_mind mind env in
      let id = mib.mind_packets.(midx).mind_typename in
      (* msg_debug (str (Printf.sprintf "LOOK HERE: %s - %s - %s" (MutInd.to_string mind) (Label.to_string (MutInd.label mind)) 
                                                            (Id.to_string (Label.to_id (MutInd.label mind)))) ++ fnl ());*)
      Some (DTyCtr (Libnames.qualid_of_ident id, []))
    end
    else if Constr.isConstruct ty then begin
      let (((mind, midx), idx),_) = Constr.destConstruct ty in                               

      (* Lookup the inductive *)
      let env = Global.env () in
      let mib = Environ.lookup_mind mind env in

(*      let (mp, _dn, _) = MutInd.repr3 mind in *)

      (* HACKY: figure out better way to qualify constructors *)
      let names = String.split_on_char '.' (Names.MutInd.to_string mind) in
      let prefix = List.rev (List.tl (List.rev names)) in
      let qual = String.concat "." prefix in
      msg_debug (str (Printf.sprintf "CONSTR: %s %s" qual (Names.DirPath.to_string (Lib.cwd ()))) ++ fnl ());

      (* Constructor name *)
      let cname = Names.Id.to_string (mib.mind_packets.(midx).mind_consnames.(idx - 1)) in
      let cid = Libnames.qualid_of_string (if (qual = "") || (qual = Names.DirPath.to_string (Lib.cwd ()))
                             then cname else qual ^ "." ^ cname) in
      Some (DCtr (cid, []))
    end
    else if Constr.isProd ty then begin
      let (n, t1, t2) = Constr.destProd ty in
      (* Are the 'i's correct? *)
      aux i t1 >>= fun t1' -> 
      aux i t2 >>= fun t2' ->
      (match n.Context.binder_name with
       | Names.Name x -> Some (DProd ((x, t1'), t2'))
       | Names.Anonymous ->
          CErrors.user_err (str "Anonymous product encountered: " ++ (debug_constr ty) ++ fnl ())
      )
    end
    (* Rel, App, Ind, Construct, Prod *)
    else if Constr.isConst ty then begin 
      let (x,_) = Constr.destConst ty in 
      Some (DTyVar (Names.Label.to_id (Names.Constant.label x)))
    end
    else (
      let env = Global.env() in
      let sigma = Evd.from_env env in
      CErrors.user_err (str "Dep Case Not Handled: " ++ Printer.pr_constr_env env sigma ty ++ fnl())
    ) in
  aux i ty

let parse_dependent_type ty =

    let (ctr_pats, result) = if Constr.isConst ty then ([],ty) else Term.decompose_prod ty in

    let pat_names, pat_types = List.split (List.rev ctr_pats) in

    let pat_names = List.map (fun n -> n.Context.binder_name) pat_names in
    let arg_names = 
      List.map (fun n -> match n with
                         | Names.Name x -> DTyVar x 
                         | Names.Anonymous -> DTyVar (make_up_name ()) (* Make up a name, but probably can't be used *)
               ) pat_names in 

    parse_dependent_type_internal (1 + (List.length ctr_pats)) 0 result None arg_names >>= fun result_ty ->
    sequenceM (fun x -> x) (List.mapi (fun i ty -> parse_dependent_type_internal i 0 ty None arg_names) (List.map (Vars.lift (-1)) pat_types)) >>= fun types ->
    Some (dep_arrowify result_ty pat_names types)
  
let dep_parse_type nparams param_names arity_ctxt oib =
  let len = List.length arity_ctxt in
  (* Only type parameters can be used - no dependencies on the types *)
  let arg_names = List.map (fun x -> DTyParam x) param_names in
  foldM (fun acc (i, decl) -> 
           let n = Context.Rel.Declaration.get_name decl in
           let t = Context.Rel.Declaration.get_type decl in
           msg_debug (debug_constr t ++ fnl ());
           match n with
           | Names.Name id -> (* Check if it is a parameter to add its type / name *)
              if Constr.is_Type t then Some acc 
              else parse_dependent_type_internal i nparams t (Some oib) arg_names >>= fun dt -> Some ((n,dt) :: acc)
           | _ ->  parse_dependent_type_internal i nparams t (Some oib) arg_names >>= fun dt -> Some ((n,dt) :: acc)
        ) (Some []) (List.mapi (fun i x -> (len - nparams - i, x)) arity_ctxt) >>= fun nts ->
  let (names, types) = List.split nts in
  Some (dep_arrowify (DTyCtr (constructor_of_string "Prop", [])) names types)

(* Dependent version: 
   nparams is numver of Type parameters 
   param_names are type parameters (length = nparams)

   Returns list of constructor representations 
 *)
let dep_parse_constructors nparams param_names oib : rocq_ctr list option =
  
  let parse_constructor branch : rocq_ctr option =
    let (ctr_id, ty_ctr) = branch in

    let (_, ty) = Term.decompose_prod_n nparams ty_ctr in
    
    let (ctr_pats, result) = if Constr.isConst ty then ([],ty) else Term.decompose_prod ty in

    let pat_names, pat_types = List.split (List.rev ctr_pats) in

    let pat_names = List.map (fun n -> n.Context.binder_name) pat_names in
    let arg_names = 
      List.map (fun x -> DTyParam x) param_names @ 
      List.map (fun n -> match n with
                         | Names.Name x -> DTyVar x 
                         | Names.Anonymous -> DTyVar (make_up_name ()) (* Make up a name, but probably can't be used *)
               ) pat_names in 

(*     msgerr (str "Calculating result type" ++ fnl ()); *)
    parse_dependent_type_internal (1 + (List.length ctr_pats)) nparams result (Some oib) arg_names >>= fun result_ty ->

(*     msgerr (str "Calculating types" ++ fnl ()); *)
    sequenceM (fun x -> x) (List.mapi (fun i ty -> parse_dependent_type_internal i nparams ty (Some oib) arg_names) (List.map (Vars.lift (-1)) pat_types)) >>= fun types ->
    Some (ctr_id, dep_arrowify result_ty pat_names types)
  in

  let cns = List.map Libnames.qualid_of_ident (Array.to_list oib.Declarations.mind_consnames) in
  let lc =  List.map (fun (ctx, t) -> Term.it_mkProd_or_LetIn t ctx) (Array.to_list oib.Declarations.mind_nf_lc) in
  sequenceM parse_constructor (List.combine cns lc)

(* Given a Coq constr corresponding to the type of an inductive 
   with n arguments, convert it to our representation. *)
let constr_to_rocq_constr  (c : Constr.constr) : rocq_constr option =
  None

let oib_to_rocq_relation (oib : Declarations.one_inductive_body) : rocq_relation option =
    let ty_ctr = oib.Declarations.mind_typename in 
    dep_parse_type_params oib.Declarations.mind_arity_ctxt >>= fun ty_params ->
    List.iter (fun tp -> msg_debug (str (ty_param_to_string tp) ++ fnl ())) ty_params;
    dep_parse_constructors (List.length ty_params) ty_params oib >>= fun ctr_reps ->
    dep_parse_type (List.length ty_params) ty_params oib.Declarations.mind_arity_ctxt oib >>= fun result_ty -> 
    Some (Libnames.qualid_of_ident ty_ctr, ty_params, ctr_reps, result_ty)
    
let qualid_to_rocq_relations (r : Libnames.qualid) : (int * rocq_relation list) option =
  (* Locate all returns _all_ definitions with this suffix *)
  let lookup_results = Nametab.locate_all r in
  (* We look for the first one that is an inductive *)

  try begin
    let first_ind = List.find (fun x -> match x with
                                        | Names.GlobRef.IndRef _ -> true
                                        | _ -> false) lookup_results in
    match first_ind with
    | Names.GlobRef.IndRef (mind,ix) ->
       (* Lookup the mutual inductive body in the _global_ environment. *)
       let mib = Environ.lookup_mind mind (Global.env ()) in
       (* Parse each `one_inductive_body` into a rocq relation. All should succeed. *)
       let rs = sequenceM oib_to_rocq_relation (Array.to_list mib.Declarations.mind_packets) in
       option_map (fun r -> (ix, r)) rs
      | _ -> failwith ("No Inductives named: " ^ Libnames.string_of_qualid r)
    end
  with
    Not_found -> failwith "BETTER MESG"

let ind_reference_to_rocq_relations (c : Constrexpr.constr_expr) : (int * rocq_relation list) option =
  let r = match c with
    | { CAst.v = Constrexpr.CRef (r,_);_ } -> r
    | _ -> failwith "Not a reference"
  in
  qualid_to_rocq_relations r

open Constrexpr

let debug_constr_expr (c : constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  msg_debug (str "lol");
  Feedback.msg_notice (Ppconstr.pr_constr_expr env sigma c)

(* Patterns in language that derivations target *)
type pat =
  | PCtr of constructor * pat list
  | PVar of var
  | PParam (* Type parameter *)
  | PWild

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
  | MBacktrack of mexp list
  | MFun of (pat * mexp option) list * mexp 
  | MFix of var * (var * mexp) list * mexp 
  
let m_arbitrary ty = MApp (MConst "QuickChick.Classes.arbitrary", [ty; MHole])

let m_arbitraryST prop = MApp (MConst "QuickChick.DependentClasses.arbitraryST", [MHole; prop; MHole])

let m_enum ty = MApp (MConst "QuickChick.Classes.enum", [ty; MHole])

let m_enumSuchThat prop = MApp (MConst "QuickChick.DependentClasses.enumSuchThat", [MHole; prop; MHole])

let m_fuel = MConst "QuickChick.Decidability.checkable_size_limit"

let m_decOpt prop fuel = MApp (MConst "QuickChick.Decidability.decOpt", [prop; MHole; fuel])

let m_thunkGen gen = MApp (MConst "QuickChick.Generators.thunkGen", [MHole; gen])

type producer_sort = PS_E | PS_G

type rocq_type = rocq_constr

type source = 
  | SrcNonrec of rocq_type
  | SrcRec of var * rocq_constr list

type schedule_step =
  | S_UC of var * source * producer_sort
  | S_ST of (var * rocq_type (*** (int list) list*)) list * source * producer_sort (* the (int list) list for each var means the list of all occurences of the same variable
                                                                                        that we wish to produce, any other instance of the var is an input *)
  | S_Check of source
  | S_Match of var * pat (* Used when you decompose a constructor constrained arg into a fresh variable followed by a pattern match.*)

type is_constrained = bool

type schedule_sort = ProducerSchedule of is_constrained * producer_sort * rocq_constr (* tuple of produced outputs from conclusion of constructor *)
                   | CheckerSchedule (* checkers need not bother with conclusion of constructor, only hypotheses need be checked and conclusion of constructor follows *)
                   | TheoremSchedule of rocq_constr (* conclusion of theorem to be checked *)

type schedule = schedule_step list * schedule_sort

let rec product_free_rocq_type_to_mexp (rt : rocq_type) : mexp =
  match rt with
  | DArrow (_,_) -> failwith "Not a product_free type"
  | DProd (_,_) -> failwith "Not a product-free type"
  | DTyParam p -> MId p
  | DTyCtr (c, ds) -> MTyCtr (c, List.map product_free_rocq_type_to_mexp ds)
  | DCtr (c, ds) -> MCtr (c, List.map product_free_rocq_type_to_mexp ds)
  | DTyVar v -> MId v
  | DApp (d, ds) -> MApp (product_free_rocq_type_to_mexp d, List.map product_free_rocq_type_to_mexp ds)
  | DNot d -> MTyCtr (ty_ctr_of_string "Coq.Init.Logic.not", [product_free_rocq_type_to_mexp d])
  | DHole -> MHole


let match_optbool mb some_t some_f none : mexp =
  MMatch (mb, 
          [
            (PCtr (constructor_of_string "Some", [PParam; PCtr (constructor_of_string "true", [])]), some_t);
            (PCtr (constructor_of_string "Some", [PParam; PCtr (constructor_of_string "false", [])]), some_f);
            (PCtr (constructor_of_string "None", [PParam]), none)
          ])

(* Maybe this should do checks? *)
let cInject s : constr_expr = 
  if s = "" then failwith "Called gInject with empty string";
  CAst.make @@ CRef (Libnames.qualid_of_string s, None)

let c_var v : constr_expr =
  CAst.make @@ CRef (Libnames.qualid_of_ident v, None)

let c_constructor c : constr_expr =
  CAst.make @@ CRef (c, None)

let c_ty_ctr c : constr_expr =
  CAst.make @@ CRef (c, None)

let c_hole = CAst.make @@ CHole None

let tuple_of_list (pair : 'a -> 'a -> 'a) (xs : 'a list) : 'a = (*Maybe need to convert to pattern pair?*)
  match xs with
  | [] -> failwith "No empty tuples"
  | [x] -> x
  | x::xs -> List.fold_left pair x xs

let c_pat (p : pat) : Constrexpr.cases_pattern_expr =
  let rec aux p =
    match p with
    | PCtr (c, ps) -> CAst.make @@ CPatCstr (c, Some (List.map aux ps),[])
    | PVar v -> CAst.make @@ CPatAtom (Some (Libnames.qualid_of_ident v))
    | PParam -> CAst.make @@ CPatAtom None
    | PWild -> CAst.make @@ CPatAtom None
  in aux p

let rec pat_vars (p : pat) : var list =
  match p with
  | PCtr (_, ps) -> List.concat (List.map pat_vars ps)
  | PVar v -> [v]
  | PParam -> []
  | PWild -> []

let arg_of_pat (p : pat) (ty : constr_expr option) =
  match p, ty with
  | PVar v, Some ty -> CLocalAssum ([CAst.make @@ Names.Name v], None, Default Glob_term.Explicit, ty)
  | _, _ -> CLocalPattern (c_pat p)

let c_fun (pat_args : (pat * constr_expr option) list) (f_body : var list -> constr_expr) : constr_expr =
  let args = List.concat (List.map (fun (p,_) -> pat_vars p) pat_args) in
  let local_patterns = List.map (fun (p,ty) -> arg_of_pat p ty) pat_args in
  mkLambdaCN local_patterns (f_body args)

let c_app ?explicit:(expl=true) c cs : constr_expr =
  if expl then
    let f c = match c with
    | CRef (r,_) -> Constrexpr.CAppExpl((r, None), cs)
    | _ -> failwith "invalid argument to gApp"
    in CAst.map f c
  else mkAppC (c, cs)

let c_pair x y = c_app (cInject "Coq.Init.Datatypes.pair") [c_hole; c_hole; x; y]

let c_tuple_of_list xs = tuple_of_list c_pair xs

let pat_tuple_of_list xs = tuple_of_list (fun x y -> PCtr (constructor_of_string "Coq.Init.Datatypes.pair", [PWild; PWild; x; y])) xs

let c_pat_tuple_of_List xs = c_pat (pat_tuple_of_list xs)

let c_match discr ?catchAll:(body=None) (branches : (pat * constr_expr) list) : constr_expr =
  CAst.make @@ CCases (RegularStyle,
          None (* return *), 
          [(discr, None, None)], (* single discriminee, no as/in *)
          (List.map (fun (p, bf) -> 
                      CAst.make ([[c_pat p]], bf)
                   ) branches) @ match body with
                                 | None -> []
                                 | Some c' -> [CAst.make ([[CAst.make @@ CPatAtom None]], c')])

let c_let v c1 c2 : constr_expr =
  CAst.make @@ CLetIn (CAst.make @@ Names.Name v, c1, None, c2)

(*  (a,b,c)  => pair (pair (pair a b) c) d  *)
(* 

let c_match discr ?catchAll:(body=None) ?params:(holes=0) (branches : (constructor * string list * (var list -> coq_expr)) list) : constr_expr =
  CAst.make @@ CCases (RegularStyle,
          None (* return *), 
          [(discr, None, None)], (* single discriminee, no as/in *)
          (List.map (fun (c, cs, bf) -> 
                      let cvs : Id.t list = List.map fresh_name cs in
                      CAst.make ([[CAst.make @@ CPatCstr (c,
                                      None,
                                      List.init holes (fun _ -> CAst.make @@ CPatAtom None) @
                                      List.map (fun s -> CAst.make @@ CPatAtom (Some (qualid_of_ident s))) cvs (* Constructor applied to patterns *)
                                    )
                           ]],
                       bf cvs)
                   ) branches) @ match body with
                                 | None -> []
                                 | Some c' -> [CAst.make ([[CAst.make @@ CPatAtom None]], c')]) *)

type derive_sort = D_Gen | D_Enum | D_Check | D_Thm

let c_bindGen gen k = c_app (cInject "QuickChick.Generators.bindGen") [c_hole; c_hole; gen; k]

let c_bindOpt prod k = c_app (cInject "QuickChick.Producer.bindOpt") [c_hole; c_hole; c_hole; c_hole; prod; k]

let c_andBind check k = c_app (cInject "QuickChick.Decidability.andBind") [check; k] 
  (*Not a real function, either add or preprocess these binds into matches in rocq_constr to mexp conversion*)

let c_bindEnum enum k = c_app (cInject "QuickChick.Enumerators.bindEnum") [c_hole; c_hole; enum; k]

let c_enumerating enum k init_size = c_app (cInject "QuickChick.Enumerators.enumerating") [c_hole; enum; k; init_size]

let c_enumeratingOpt enum k init_size = c_app (cInject "QuickChick.Enumerators.enumeratingOpt") [c_hole; enum; k; init_size]

let c_forAll check k = c_app (cInject "QuickChick.Checker.forAll") [c_hole; c_hole; c_hole; c_hole; check; k]

let c_forAllMaybe check k = c_app (cInject "QuickChick.Checker.forAllMaybe") [c_hole; c_hole; c_hole; c_hole; check; k]
 
let c_checker c = c_app (cInject "QuickChick.Checker.checker") [c_hole; c_hole; c]

let c_tt = cInject "Coq.Init.Datatypes.tt"

let c_None ty = c_app (cInject "Coq.Init.Datatypes.None") [ty]

let c_Some ty x = c_app (cInject "Coq.Init.Datatypes.Some") [ty; x]

let c_nil ty = c_app (cInject "Coq.Init.Datatypes.nil") [ty]

let c_cons ty x xs = c_app (cInject "Coq.Init.Datatypes.cons") [ty; x; xs]

let rec c_list ty = function
  | [] -> c_nil ty
  | x::xs -> c_cons ty x (c_list ty xs)

let derive_sort_to_string (ds : derive_sort) : string =
  match ds with
  | D_Gen -> "Gen"
  | D_Enum -> "Enum"
  | D_Check -> "Check"
  | D_Thm -> "Thm"

let monad_sort_to_string (ms : monad_sort) : string =
  match ms with
  | MG -> "Gen"
  | MGOpt -> "GenOpt"
  | ME -> "Enum"
  | MEOpt -> "EnumOpt"
  | MC -> "Check"
  | MId -> "Id"

let c_bind (ms : monad_sort) (ds : derive_sort) (m1 : constr_expr) (vs : var list) (m2 : constr_expr) : constr_expr =
  let args = match vs with
    | [] -> []
    | _ -> [pat_tuple_of_list (List.map (fun v -> PVar v) vs), None] in
  let k = c_fun args (fun _ -> m2) in
  match ds, ms with
  | D_Gen, MG -> c_bindGen m1 k
  | D_Gen, MGOpt -> c_bindOpt m1 k
  | D_Gen, MC -> c_andBind m1 k
  | D_Enum, ME -> c_bindEnum m1 k
  | D_Enum, MEOpt -> c_bindOpt m1 k
  | D_Enum, MC -> c_andBind m1 k
  | D_Check, MC -> c_andBind m1 k
  | D_Check, ME -> c_enumerating m1 k (c_var (var_of_string "init_size"))
  | D_Check, MEOpt -> c_enumeratingOpt m1 k (c_var (var_of_string "init_size"))
  | D_Thm, MC -> c_andBind m1 k
  | D_Thm, MG -> c_forAll m1 k
  | D_Thm, MGOpt -> c_forAllMaybe m1 k
  | _, _ -> failwith ("Invalid bind for derive_sort" ^ derive_sort_to_string ds ^ " and monad_sort " ^ monad_sort_to_string ms)

let c_ret (ds : derive_sort) (m : constr_expr) : constr_expr =
  match ds with
  | D_Gen -> c_app (cInject "QuickChick.Generators.returnGen") [c_hole; m]
  | D_Enum -> c_app (cInject "QuickChick.Enumerators.returnEnum") [c_hole; m]
  | D_Check -> m
  | D_Thm -> c_checker m

let c_fail (ds : derive_sort) : constr_expr =
  match ds with
  | D_Gen -> c_ret D_Gen (c_None c_hole)
  | D_Enum -> c_app (cInject "QuickChick.Enumerators.failEnum") [c_hole]
  | D_Check -> c_None c_hole
  | D_Thm -> c_checker c_tt

let c_out_of_fuel (ds : derive_sort) : constr_expr =
  match ds with
  | D_Gen -> c_fail D_Gen
  | D_Enum -> c_ret D_Enum (c_None c_hole)
  | D_Check -> c_None c_hole
  | D_Thm -> c_checker c_tt

let c_backtrack (ds : derive_sort) (ms : constr_expr list) : constr_expr =
  match ds with
  | D_Gen -> c_app (cInject "QuickChick.Generators.backtrack") [c_hole; c_list c_hole @@ ms] (* ms : list (nat * G (option A)) *)
  | D_Enum -> c_app (cInject "QuickChick.Enumerators.enumerate") [c_hole; c_list c_hole @@ ms] (* ms : list (E (option A))*)
  | D_Check -> c_app (cInject "QuickChick.Decidability.checker_backtrack") [c_list c_hole @@ ms] (* ms : list (unit -> option A)*)
  | D_Thm -> failwith "Backtrack not supported for theorems."

let rec mexp_to_constr_expr (me : mexp) (ds : derive_sort) : constr_expr =
  match me with
  | MBind (ms, m, vs, k) -> c_bind ms ds (mexp_to_constr_expr m ds) vs (mexp_to_constr_expr k ds)
  | MRet m -> c_ret ds (mexp_to_constr_expr m ds)
  | MFail -> c_fail ds
  | MOutOfFuel -> c_out_of_fuel ds
  | MId v -> c_var v
  | MApp (m, ms) -> c_app (mexp_to_constr_expr m ds) (List.map (fun m -> mexp_to_constr_expr m ds) ms)
  | MCtr (c, ms) -> c_app (c_constructor c) (List.map (fun m -> mexp_to_constr_expr m ds) ms)
  | MTyCtr (c, ms) -> c_app (c_ty_ctr c) (List.map (fun m -> mexp_to_constr_expr m ds) ms)
  | MConst s -> cInject s
  | MEscape e -> e
  | MMatch (m, pms) -> c_match (mexp_to_constr_expr m ds) (List.map (fun (p,m) -> (p, mexp_to_constr_expr m ds)) pms)
  | MHole -> c_hole
  | MLet (v, m1, m2) -> c_let v (mexp_to_constr_expr m1 ds) (mexp_to_constr_expr m2 ds)
  | MBacktrack ms -> c_backtrack ds (List.map (fun case -> mexp_to_constr_expr case ds) ms)
  | MFun (vs, m) -> c_fun (List.map (fun (v,ty) -> v, option_map (fun ty -> mexp_to_constr_expr ty ds) ty) vs) (fun _ -> (mexp_to_constr_expr m ds))
  | MFix (f, vs, m) ->
    let lid = CAst.make f in
    let args = List.map (fun (v,ty) -> CLocalAssum ([CAst.make @@ Names.Name v], None, Default Glob_term.Explicit, mexp_to_constr_expr ty ds)) vs in
    CAst.make @@ CFix (lid, [(lid,None,None,args,c_hole, mexp_to_constr_expr m ds)])


let prod_sort_to_monad_sort (ps : producer_sort) : monad_sort =
  match ps with
  | PS_E -> ME
  | PS_G -> MG

let prod_sort_to_monad_opt_sort (ps : producer_sort) : monad_sort =
  match ps with
  | PS_E -> MEOpt
  | PS_G -> MGOpt
(* 
let rename_rocq_type_vars (rt : rocq_type) (v : var) (locations : int list list) : rocq_type =
  let other_v = fresh_name (var_to_string v) in
  let rec aux loc rt = 
    match rt with
    | DTyParam p -> DTyParam p
    | DTyCtr (c, ds) -> DTyCtr (c, List.mapi (fun i d -> aux (loc @ [i]) d) ds)
    | DCtr (c, ds) -> DCtr (c, List.mapi (fun i d -> aux (loc @ [i]) d) ds)
    | DTyVar x -> if x = v then DTyVar (if List.mem loc locations then v else other_v) else DTyVar x
    | DApp (d, ds) -> DApp (d, List.mapi (fun i d -> aux (loc @ [i]) d) ds)
    | DNot d -> DNot (aux (loc @ [0]) d)
    | DHole -> DHole
  in
  aux [] rt *)

let unconstrained_producer (ps : producer_sort) ty =
  match ps with
  | PS_E -> m_enum ty
  | PS_G -> m_arbitrary ty

let such_that_producer (ps : producer_sort) vars p =
  let p_vars = List.map (fun v -> PVar v) vars in
  let arg_tuple = pat_tuple_of_list p_vars in
  let p_with_args = MFun ([arg_tuple,None], p) in
  match ps with
  | PS_E -> m_enumSuchThat p_with_args
  | PS_G -> m_arbitraryST p_with_args
  
let num_of_ctrs (c : constructor) =
  let env = Global.env () in
  let glob_ref = Nametab.global c in
  let ((mind,n),_) = Globnames.destConstructRef glob_ref in
  let mib = Environ.lookup_mind mind env in
  Array.length (mib.mind_packets.(n).mind_consnames)

let is_singleton (c : constructor) : bool =
  num_of_ctrs c = 1

let rec total_pat (p : pat) : bool =
  match p with
  | PCtr (c, ps) -> 
    is_singleton c && List.for_all total_pat ps
  | PParam | PWild | PVar _ -> true

let rec_call r args =
  MApp (MId r, MId (var_of_string "init_size") :: MId (var_of_string "size'") :: List.map product_free_rocq_type_to_mexp args)

let schedule_step_to_mexp (step : schedule_step) : mexp -> mexp = fun k ->
  match step with
  | S_UC (v, prod, ps) -> 
    let producer = (match prod with
      | SrcNonrec ty -> unconstrained_producer ps (product_free_rocq_type_to_mexp ty)
      | SrcRec (rec_f, args) -> rec_call rec_f args) in
    MBind (prod_sort_to_monad_sort ps, producer, [v], k)
  | S_ST (vars_tys, prod, ps) -> 
    let producer = (match prod with
      | SrcNonrec ty -> such_that_producer ps (List.map fst vars_tys) (product_free_rocq_type_to_mexp ty)
      | SrcRec (rec_f, args) -> rec_call rec_f args) in
    let vars = List.map fst vars_tys in
    MBind (prod_sort_to_monad_opt_sort ps, producer, vars, k)
  | S_Check src -> 
    let checker = (match src with
      | SrcNonrec ty -> m_decOpt (product_free_rocq_type_to_mexp ty) m_fuel
      | SrcRec (rec_f, args) -> rec_call rec_f args) in
    MBind (MC, checker, [], k)
  | S_Match (v, p) -> 
    if total_pat p then
      MMatch (MId v, [(p, k)])
    else
      MMatch (MId v, [(p, k); (PWild, MFail)])

(* Theorem = producer composed with a checker *)

let m_Some ty x = MApp (MConst "Coq.Init.Datatypes.Some", [ty; x])

let m_None ty = MApp (MConst "Coq.Init.Datatypes.None", [ty])

let m_bool = MConst "Coq.Init.Datatypes.bool"

let m_true = MConst "Coq.Init.Datatypes.true"

let m_false = MConst "Coq.Init.Datatypes.false"

(* Maybe start this by checking that all the variables used/produced in the conclusion are actually created in the steps?*)
(* let schedule_to_mexp ((steps, s_sort) : schedule) : mexp =
  let rec aux steps k =
    match steps with
    | [] -> k
    | step :: steps' -> aux steps' (schedule_step_to_mexp step k)
  in
  let finally = match s_sort with
    | ProducerSchedule (ps, concl_outputs) -> MRet (product_free_rocq_type_to_mexp concl_outputs)
    | CheckerSchedule -> MRet (m_Some m_bool m_true)
    | TheoremSchedule concl -> match_optbool (m_decOpt (product_free_rocq_type_to_mexp concl) m_fuel) (MRet (m_Some m_bool m_true)) (MRet (m_Some m_bool m_false)) MOutOfFuel
  in *)
  (* aux steps finally    *)

(* Rewrite the above schedule_to_mexp as a fold*)
let schedule_to_mexp ((steps, s_sort) : schedule) : mexp =
  let finally = match s_sort with
    | ProducerSchedule (is_constrained, ps, concl_outputs) -> MRet ((if is_constrained then m_Some MHole else (fun x -> x)) @@ product_free_rocq_type_to_mexp concl_outputs)
    | CheckerSchedule -> MRet (m_Some m_bool m_true)
    | TheoremSchedule concl -> match_optbool (m_decOpt (product_free_rocq_type_to_mexp concl) m_fuel) (MRet (m_Some m_bool m_true)) (MRet (m_Some m_bool m_false)) MOutOfFuel
  in
  List.fold_right schedule_step_to_mexp steps finally

let schedule_to_constr_expr (s : schedule) (ds : derive_sort) : constr_expr =
  mexp_to_constr_expr (schedule_to_mexp s) ds

module VarOrd = struct
  type t = var
  let compare x y = compare (var_to_string x) (var_to_string y)
end

module VM = Map.Make(VarOrd)
(* module US = Set.Make(UnknownOrd) *)
          
(* Maps input variables to patterns *)
type pat_map = pat VM.t

type inductive_schedule = string * (var * mexp) list * (schedule * (var * pat) list) list * (schedule * (var * pat) list) list 
  (*Name string, fixed input variable/type list, list of base schedules, and a list non base schedules paired with how they match on those variables*)

type rec_or_base = Base | Rec

let backtrack_decoration (ds : derive_sort) (rec_or_base : rec_or_base) (m : mexp) : mexp =
  match ds with
  | D_Gen -> 
    let weight = (match rec_or_base with 
                 | Rec -> MId (var_of_string "size")
                 | Base -> MConst "Coq.Init.Nat.one") in
    MCtr (constructor_of_string "Coq.Init.Datatypes.pair", [MHole; MHole; weight; m_thunkGen (MFun ([PWild,None], m))])
  | D_Enum -> m
  | D_Check -> MFun ([PWild, None], m)
  | D_Thm -> failwith "Backtrack not supported for theorems."

let inductive_schedule_to_mexp (is : inductive_schedule) (ds : derive_sort) : mexp =
  let (name, inputs, base_scheds, rec_scheds) = is in
  let nat_ty = MConst "Coq.Init.Datatypes.nat" in
  let prelude base_k all_k = MFix (var_of_string "rec", (var_of_string "init_size", nat_ty) :: (var_of_string "size", nat_ty) :: inputs, 
    MMatch (MId (var_of_string "size"), 
            [
              (PCtr (constructor_of_string "Coq.Init.Datatypes.O", []), 
                base_k);
              (PCtr (constructor_of_string "Coq.Init.Datatypes.S", [PVar (var_of_string "size'")]), 
                all_k);
            ])) in
  let match_pats inp_pats (k : mexp) =
    List.fold_left (fun acc (v, pat) -> 
      MMatch (MId v, (pat, acc) :: (if total_pat pat then [] else [(PWild, MFail)]))
    ) k inp_pats in
  let base_backtrack = List.map (fun (s, inp_pats) -> 
    backtrack_decoration ds Base (match_pats inp_pats (schedule_to_mexp s))) base_scheds in
  let rec_backtrack = List.map (fun (s, inp_pats) ->
    backtrack_decoration ds Rec (match_pats inp_pats (schedule_to_mexp s))) rec_scheds in
  let all_backtrack = base_backtrack @ rec_backtrack in
  let fun_name = var_of_string (name ^ derive_sort_to_string ds) in
  let final_let fixp = 
    MLet (fun_name, 
          fixp, 
          MFun ([PVar (var_of_string "size"), Some (MConst "Coq.Init.Datatypes.nat")], 
            MApp (MId fun_name,
                  [MId (var_of_string "size"); MId (var_of_string "size")]))) in
  final_let (prelude (MBacktrack base_backtrack) (MBacktrack all_backtrack))

let inductive_schedule_to_constr_expr (is : inductive_schedule) (ds : derive_sort) : constr_expr =
  mexp_to_constr_expr (inductive_schedule_to_mexp is ds) ds

let find_typeclass_bindings typeclass_name ctr =
  msg_debug (str ("Finding typeclass bindings for:" ^ Libnames.string_of_qualid ctr) ++ fnl());
  let env = Global.env () in
  let evd = Evd.from_env env in
  let db = Hints.searchtable_map "typeclass_instances" in
  let result = ref [] in

  (* Add comment here *)
  let prod_check i =
    String.equal (Names.MutInd.to_string (fst i)) ("QuickChick.DependentClasses." ^ typeclass_name)  in    
  let dec_check i =
    String.equal (Names.MutInd.to_string (fst i)) ("QuickChick.Decidability." ^ typeclass_name)  in

  let handle_hint b hint =
    msg_debug (str "Processing... (" ++ str typeclass_name ++ str ")"  ++ Hints.FullHint.print env evd hint ++ fnl ());
    begin match Hints.FullHint.repr hint with
    | Hints.Res_pf h ->
       msg_debug (str "ResPF" ++ fnl ());
    | Hints.Give_exact h ->
       msg_debug (str "GiveExact" ++ fnl ());
    | _ ->
       msg_debug (str "..." ++ fnl ());
(*    let (co, c) = Hints.hint_as_term hint in
    msg_debug (Ppconstr.pr_constr env evd c ++ fnl ());
 *************)
(*               
    match Hints.FullHint.pattern hint with
    | Some p -> 
       msg_debug (Ppconstr.pr_constr_pattern_expr env evd (Constrextern.extern_constr_pattern [] evd p) ++ fnl ())
    | _ ->
       msg_debug (str "Not an Option" ++ fnl ())
 *)
    end
  in 

  (* Iterate through all of the hints *)
  Hints.Hint_db.iter (fun go hm hints ->
      begin match go with
      | Some (Names.GlobRef.IndRef i) when prod_check i ->
         List.iter (handle_hint true ) hints
      | Some (Names.GlobRef.IndRef i) when dec_check i ->
         (* eq hack          if Names.Id.to_string (qualid_basename ctr) = "eq" then result := [[false; false; false]]
         else *) List.iter (handle_hint false) hints
      | _ -> ()
      end
    ) db;
  []

module ScheduleExamples = struct
  let var = var_of_string
  let ctr = constructor_of_string
  let ty_ctr = ty_ctr_of_string

  (* forall Gamma e tau e', typing' Gamma e tau -> bigstep' e e' -> typing' Gamma e' tau*)
  let thm_schedule = 
    [
      S_UC (var "Gamma", SrcNonrec (DTyCtr (ty_ctr "list", [DTyCtr (ty_ctr "type",[])])), PS_G);
      S_UC (var "tau", SrcNonrec (DTyCtr (ty_ctr "type", [])), PS_G);
      S_ST ([(var "e", DTyCtr (ty_ctr "term", []))], SrcNonrec (DTyCtr (ty_ctr "typing'", [DTyVar (var "Gamma"); DTyVar (var "e"); DTyVar (var "tau")])), PS_G);
      S_ST ([(var "e'", DTyCtr (ty_ctr "term", []))], SrcNonrec (DTyCtr (ty_ctr "bigstep'", [DTyVar (var "e"); DTyVar (var "e'")])), PS_G);
    ], TheoremSchedule (DTyCtr (ty_ctr "typing'", [DTyVar (var "Gamma"); DTyVar (var "e'"); DTyVar (var "tau")]))

  (*
  Inductive typing (G : env) : term -> type -> Prop :=
  | TId :
      forall x t,
        bind G x t ->
        typing G (Id x) t
  | TConst :
      forall n,
        typing G (Const n) N
  | TAbs :
      forall e t1 t2,
        typing (t1 :: G) e t2 ->
        typing G (Abs t1 e) (Arrow t1 t2)
  | TApp :
      forall e1 e2 t1 t2,
        typing G e2 t1 ->
        typing G e1 (Arrow t1 t2) ->
        typing G (App e1 e2) t2.
  *)

(* typing G (Abs t1 e) ty

  Inductive typing (G : env) : term -> type -> Prop :=
  | TAbs :
      forall e t1 t2,
        typing (t1 :: G) e t2 ->
        typing G (Abs t1 e) (Arrow t1 t2)

*)

(* typing (t' :: G_) e' t2_

  Inductive typing (G : env) : term -> type -> Prop :=
  | TId :
      forall x t,
        bind G x t ->
        typing G (Id x) t
  | TConst :
      forall n,
        typing G (Const n) N
  | TAbs :
        typing (t1_ :: t :: G_) e t2_ ->
        typing (t :: G_) (Abs t1_ e) (Arrow t1_ t2_)
  | TApp :
        typing (t :: G_) e2 t1 ->
        typing (t :: G_) e1 (Arrow t1 t2_) ->
        typing (t :: G_) (App e1 e2) t2_.


*)

  let check_typing_TId _G _x _t =
    [
      S_Check (SrcNonrec (DTyCtr (ty_ctr "bind", [_G; _x; _t])))
    ], CheckerSchedule

  let check_typing_TConst _G _n =
    [

    ], CheckerSchedule

  let check_typing_TAbs _G _t1 _t1' _t2 _e =
    [
      S_Check (SrcNonrec (DTyCtr ((ty_ctr "eq"), [DTyCtr (ty_ctr "type", []); _t1; _t1'])));
      S_Check (SrcRec ((var "rec"),[DCtr (ctr "cons",[DHole; _t1; _G]); _e; _t2]))
    ], CheckerSchedule

  let check_typing_TApp _G _e1 _e2 _t2 =
    [
      S_ST ([(var "t1", DTyCtr (ty_ctr "type", []))], SrcNonrec (DTyCtr (ty_ctr "typing", [_G; _e2; DTyVar (var "t1")])), PS_E);
      S_Check (SrcRec ((var "rec"), [_G; _e1; DTyCtr (ty_ctr "Arrow", [DTyVar (var "t1"); _t2])]))
    ], CheckerSchedule

  let check_typing_inductive_schedule : inductive_schedule =
    let list_ty = MTyCtr (ty_ctr "list", [MTyCtr (ty_ctr "type", [])]) in
    let term = MTyCtr (ty_ctr "term", []) in
    let ty = MTyCtr (ty_ctr "type", []) in
    let inputs = [var "G", list_ty; var "e", term; var "tau", ty] in
    let base_scheds = [(check_typing_TId (DTyVar (var "G")) (DTyVar (var "x")) (DTyVar (var "t")), 
                        [(var "e", PCtr (ctr "Id", [PVar (var "x")]));
                         (var "tau", PVar (var "t"))]);
                       (check_typing_TConst (DTyVar (var "G")) (DTyVar (var "n")),
                        [(var "e", PCtr (ctr "Const", [PVar (var "n")]));
                         (var "tau", PCtr (ctr "N", []))]
                       )
                      ] in
    let rec_scheds = [(check_typing_TAbs (DTyVar (var "G")) (DTyVar (var "t1")) (DTyVar (var "t1'")) (DTyVar (var "t2")) (DTyVar (var "e")),
                        [(var "e", PCtr (ctr "Abs", [PVar (var "t1"); PVar (var "e")]));
                        (var "tau", PCtr (ctr "Arrow", [PVar (var "t1'"); PVar (var "t2")]))]
                      );
                      (check_typing_TApp (DTyVar (var "G")) (DTyVar (var "e1")) (DTyVar (var "e2")) (DTyVar (var "t2")),
                        [(var "e", PCtr (ctr "App", [PVar (var "e1"); PVar (var "e2")]));
                        (var "tau", PVar (var "t2"))]
                      )
                      ] in
    ("typing_iii", inputs, base_scheds, rec_scheds)


(* 
  let schedule_gen_iio_TId _G _x =
    [
      S_ST ([(var "t", DTyCtr (ty_ctr "type", []))], SrcNonrec (DTyCtr (ty_ctr "bind", [_G; _x; DTyVar (var "t")])), PS_G);
    ], ProducerSchedule (true, PS_G, (DTyVar (var "t")))
  
  let schedule_gen_iio_TConst _G _n =
    [

    ], ProducerSchedule (true, PS_G, (DTyCtr (ty_ctr "N", [])))
  
  let schedule_gen_iio_TAbs _G _t1 _e =
    [
      S_ST ([(var "t2", DTyCtr (ty_ctr "type", []))], DTyCtr (ty_ctr "typing", [DCtr (ctr "cons",[DHole; _t1; _G]); _e; DCtr (ctr "Arrow",[_t1; DTyVar (var "t2")])]), PS_G)
    ], ProducerSchedule (true, PS_G, (DTyCtr (ty_ctr "Arrow", [_t1; DTyVar (var "t2")])))

  let schedule_gen_iio_TApp _G _e1 _e2 =
    [
      S_ST ([(var "t1", DTyCtr (ty_ctr "type", []))], DTyCtr (ty_ctr "typing", [_G; _e2; DTyVar (var "t1")]), PS_G);
      S_ST ([(var "t2", DTyCtr (ty_ctr "type", []))], DTyCtr (ty_ctr "typing", [_G; _e1; DTyCtr (ty_ctr "Arrow", [DTyVar (var "t1"); DTyVar (var "t2")])]), PS_G);
    ], ProducerSchedule (true, PS_G, (DTyVar (var "t2")))

  (*Now the generator for typing G e (Arrow t1 t2)*)
  let schedule_gen_arrows_TId _G _x _t1 =
    [
      S_ST ([(var "t2", DTyCtr (ty_ctr "type", []))], DTyCtr (ty_ctr "bind", [_G; _x; DCtr (ctr "Arrow",[_t1;DTyVar (var "t2")])]), PS_G);
    ], ProducerSchedule (true, PS_G, (DCtr (ctr "Arrow",[_t1; DTyVar (var "t2")])))

  let schedule_gen_arrows_TConst _G _n = None (* N incompatible with Arrow t1 t2 *)

  let schedule_gen_arrows_TAbs _G _t1 _t1' _e = (*_t1 is the type from the abstration matched on, _t1' is the t1 from (Arrow t1 t2), must be equal*)
    [ 
      S_Check (DTyCtr (ty_ctr "eq", [DTyCtr (ty_ctr "type", []); _t1; _t1']));
      S_ST ([(var "t2", DTyCtr (ty_ctr "type", []))], DTyCtr (ty_ctr "typing", [DCtr (ctr "cons",[DHole; _t1; _G]); _e; DCtr (ctr "Arrow",[_t1; DTyVar (var "t2")])]), PS_G)
    ], ProducerSchedule (true, PS_G, (DTyCtr (ty_ctr "Arrow", [_t1; DTyVar (var "t2")])))

  (*  | TApp_specialized :
    forall e1 e2 t1' t1 t2,
      typing G e2 t1' ->
      typing G e1 (Arrow t1' (Arrow t1 t2)) ->
      typing G (App e1 e2) (Arrow t1 t2).
*)

  let schedule_gen_arrows_TApp _G _e1 _e2 _t1 =
    [
      S_ST ([(var "t1'", DTyCtr (ty_ctr "type", []))], DTyCtr (ty_ctr "typing", [_G; _e2; DTyVar (var "t1'")]), PS_G);
      S_ST ([(var "t2", DTyCtr (ty_ctr "type", []))], DTyCtr (ty_ctr "typing", [_G; _e1; DTyCtr (ty_ctr "Arrow", [DTyVar (var "t1'"); DTyCtr (ty_ctr "Arrow", [_t1; DTyVar (var "t2")])])]), PS_G);
    ], ProducerSchedule (true, PS_G, (DTyCtr (ty_ctr "Arrow", [_t1; DTyVar (var "t2")])))
 *)


  (* 
  Inductive bind : list type -> nat -> type -> Prop :=
  | BindNow   : forall tau env, bind (tau :: env) O tau
  | BindLater : forall tau tau' x env,
    bind env x tau -> bind (tau' :: env) (S x) tau.
  *)

  let shcd_bindNow_gen_ioo _tau _env =
    [
    ], ProducerSchedule (true, PS_G, (DTyCtr (ty_ctr "pair", [DHole; DHole; DTyCtr (ty_ctr "O", []); _tau])))

  let schd_bindLater_gen_ioo _tau' _env =
    [
      S_ST ([(var "x", DTyCtr (ty_ctr "nat", [])); (var "tau", DTyCtr (ty_ctr "type", []))], SrcRec ((var "rec"), [_env]), PS_G)
    ], ProducerSchedule (true, PS_G, (DTyCtr (ty_ctr "pair", [DHole; DHole; DTyCtr (ty_ctr "S", [DTyVar (var "x")]); DTyVar (var "tau")])))

  let ind_schd_bind_gen_ioo =
    let list_ty = MTyCtr (ty_ctr "list", [MTyCtr (ty_ctr "type", [])]) in
    let inputs = [var "env",list_ty] in

    let base_scheds = [
      shcd_bindNow_gen_ioo (DTyVar (var "tau")) (DTyVar (var "env")),
        [(var "env", PCtr (ctr "cons", [PWild; PVar (var "tau"); PVar (var "env")]))]
    ] in

    let rec_scheds = [
      schd_bindLater_gen_ioo (DTyVar (var "tau'")) (DTyVar (var "env")),
        [(var "env", PCtr (ctr "cons", [PWild; PVar (var "tau'"); PVar (var "env")]))]
    ] in

    ("bind_ioo",inputs, base_scheds, rec_scheds)
  end 
(* let rec schedule_to_mexp (steps, concl, m_sort) : mexp = *)

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
