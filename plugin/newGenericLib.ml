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

let make_up_name_str s =
  let id = fresh_name (Printf.sprintf "%s%d_" s (!cnt)) in
  cnt := !cnt + 1;
  id

let str_lst_to_string sep (ss : string list) = 
  List.fold_left (fun acc s -> acc ^ sep ^ s) "" ss

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
let var_of_id x = x
let ty_param_to_string x = Names.Id.to_string x
let ty_ctr_to_string x = Libnames.string_of_qualid x
let ty_ctr_basename (x : ty_ctr) = Libnames.qualid_basename x
let ty_ctr_of_string x = Libnames.qualid_of_string x
let ty_ctr_to_ctr x = x
let constructor_to_string x = Libnames.string_of_qualid x
let constructor_of_string x = Libnames.qualid_of_string x

(* Patterns in language that derivations target *)
type pat =
  | PCtr of constructor * pat list
  | PVar of var
  | PParam (* Type parameter *)
  | PWild

(* Wrapper around constr that we use to represent the types of
   inductives and theorems that we plan to derive for or quickcheck *)
type rocq_constr = 
  | DArrow of rocq_constr * rocq_constr (* Unnamed arrows *)
  | DLambda of var * rocq_constr * rocq_constr (* Named arrows *)
  | DProd  of (var * rocq_constr) * rocq_constr (* Binding arrows *)
  | DTyParam of ty_param (* Type parameters - for simplicity *)
  | DTyCtr of ty_ctr * rocq_constr list (* Type Constructor *)
  | DCtr of constructor * rocq_constr list (* Type Constructor *)
  | DTyVar of var (* Use of a previously captured type variable *)
  | DApp of rocq_constr * rocq_constr list (* Type-level function applications *)
  | DMatch of rocq_constr * (pat * rocq_constr) list (* Pattern matching *)
  | DNot of rocq_constr (* Negation as a toplevel *)
  | DHole (* For adding holes *)

let pat_to_string p =
  let rec aux p =
    match p with
    | PCtr (c, ps) -> Printf.sprintf "%s %s" (constructor_to_string c) (String.concat " " (List.map aux ps))
    | PVar v -> var_to_string v
    | PParam -> "Param"
    | PWild -> "_"
  in
  aux p

let rec rocq_constr_to_string (rc : rocq_constr) : string =
  match rc with 
  | DArrow (rc1, rc2) ->
     Printf.sprintf "%s -> %s" (rocq_constr_to_string rc1) (rocq_constr_to_string rc2)
  | DLambda (x, rc1, rc2) ->
     Printf.sprintf "fun (%s : %s) => %s" (var_to_string x) (rocq_constr_to_string rc1) (rocq_constr_to_string rc2)
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
  | DMatch (rc, pats) ->
     Printf.sprintf "match %s with %s" (rocq_constr_to_string rc) 
                    (String.concat " | " (List.map (fun (pat, rc) -> Printf.sprintf "%s -> %s" (pat_to_string pat) (rocq_constr_to_string rc)) pats))
  | DNot d ->
     Printf.sprintf "~ ( %s )" (rocq_constr_to_string d)
  | DHole -> "_"

let rocq_constr_to_pat (rc : rocq_constr) : pat = 
  let rec aux rc = 
    match rc with
    | DCtr (c, ds) -> PCtr (c, List.map aux ds)
    | DTyVar v -> PVar v
    | DTyParam _ -> PParam
    | DTyCtr _ -> PWild
    | _ -> failwith ("Not a valid pattern: " ^ rocq_constr_to_string rc)
  in
  aux rc

let type_info t = 
  let rec type_info' (vars, hyps) = function
    | DProd (v, t) -> type_info' (v :: vars, hyps) t
    | DArrow (h, t) -> type_info' (vars, h :: hyps) t
    | DTyCtr _ as concl -> (List.rev vars, List.rev hyps, concl)
    | DNot (DTyCtr _) as concl -> (List.rev vars, List.rev hyps, concl)
    | a -> failwith ("Not a valid type: " ^ rocq_constr_to_string a) in
  type_info' ([], []) t

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

(* parse a type into a rocq_constr option 
   i : index of product (for DeBruijn)
   nparams : number of <Type> parameters in the beginning
   arg_names : argument names (type parameters, pattern specific variables 
 *)
let parse_dependent_type_internal i nparams ty oibopt arg_names =
  let rec aux locals i ty =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    msg_debug (str "Calling aux with: " ++ int i ++ str " "
               ++ Printer.pr_constr_env env sigma ty ++ fnl()); 
    if Constr.isRel ty then begin
      msg_debug (str "Rel: " ++ debug_constr ty ++ fnl ());
      let db = Constr.destRel ty in
      let num_local = List.length locals in
      if num_local > 0 && db <= num_local then
        (* It's a locally bound variable. De Bruijn 1 => local_binders.(0) *)
        (msg_debug (str "db: " ++ int db ++ str " num_local: " ++ int num_local ++ fnl());
        (match List.nth locals (db - 1) with
        | Names.Name name -> Some (DTyVar name)
        | _ -> CErrors.user_err (str "Anonymous Rel encountered: " ++ (debug_constr ty) ++ fnl ())))
      else
        let db_global = db - num_local in
        match oibopt with
        | Some oib when i + nparams = db_global ->
            (* Inductive itself. *)
            Some (DTyCtr (Libnames.qualid_of_ident (oib.Declarations.mind_typename), []))
        | _ ->
            try
              Some (List.nth arg_names (i + nparams - db_global - 1))
            with _ ->
              CErrors.user_err (str "nth failed (Rel): " ++ (debug_constr ty) ++ fnl ())
      end
    else if Constr.isApp ty then begin
      msg_debug (str "App: " ++ debug_constr ty ++ fnl ());
      let (ctr, tms) = Constr.decompose_app_list ty in
      foldM (fun acc ty -> 
             aux locals i ty >>= fun ty' -> Some (ty' :: acc)
            ) (Some []) tms >>= fun tms' ->
      match aux locals i ctr with
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
      msg_debug (str "Ind: " ++ debug_constr ty ++ fnl ());
      let ((mind, midx),_) = Constr.destInd ty in
      let mib = Environ.lookup_mind mind env in
      let id = mib.mind_packets.(midx).mind_typename in
      (* msg_debug (str (Printf.sprintf "LOOK HERE: %s - %s - %s" (MutInd.to_string mind) (Label.to_string (MutInd.label mind)) 
                                                            (Id.to_string (Label.to_id (MutInd.label mind)))) ++ fnl ());*)
      Some (DTyCtr (Libnames.qualid_of_ident id, []))
    end
    else if Constr.isConstruct ty then begin
      msg_debug (str "Construct: " ++ debug_constr ty ++ fnl ());
      let (((mind, midx), idx),_) = Constr.destConstruct ty in                               

      (* Lookup the inductive *)
      let env = Global.env () in
      msg_debug (str (Printf.sprintf "ACONSTR: %s" (Names.MutInd.to_string mind)) ++ fnl ());
      let mib = Environ.lookup_mind mind env in

(*      let (mp, _dn, _) = MutInd.repr3 mind in *)
      (* HACKY: figure out better way to qualify constructors *)
      let names = String.split_on_char '.' (Names.MutInd.to_string mind) in
      let prefix = List.rev (List.tl (List.rev names)) in
      let qual = String.concat "." prefix in
      msg_debug (str (Printf.sprintf "CONSTR: %s %s" qual (Names.DirPath.to_string (Lib.cwd ()))) ++ fnl ());
      (* Constructor name *)
      msg_debug (int (mib.mind_ntypes) ++ fnl ());
      let cname = Names.Id.to_string (mib.mind_packets.(midx).mind_consnames.(idx - 1)) in
      let cid = Libnames.qualid_of_string (if (qual = "") || (qual = Names.DirPath.to_string (Lib.cwd ()))
                             then cname else qual ^ "." ^ cname) in
      Some (DCtr (cid, []))
    end
    else if Constr.isProd ty then begin
      msg_debug (str "Prod: " ++ debug_constr ty ++ fnl ());
      let (n, t1, t2) = Constr.destProd ty in
      (* Are the 'i's correct? *)
      aux locals i t1 >>= fun t1' -> 
      aux (n.Context.binder_name :: locals) i t2 >>= fun t2' ->
      (match n.Context.binder_name with
       | Names.Name x -> Some (DProd ((x, t1'), t2'))
       | Names.Anonymous -> let name = make_up_name () in
                            Some (DProd ((name, t1'), t2'))
          (* CErrors.user_err (str "Anonymous product encountered: " ++ (debug_constr ty) ++ fnl ()) *)
      )
    end
    else if Constr.isLambda ty then begin
      msg_debug (str "Lambda: " ++ debug_constr ty ++ fnl ());
      let (x, t, e) = Constr.destLambda ty in
      aux locals i t >>= fun t' ->
      aux (x.Context.binder_name :: locals) i e >>= fun e' ->
      (match x.Context.binder_name with
      | Names.Name x -> Some (DLambda (x, t', e'))
      | Names.Anonymous ->
          CErrors.user_err (str "Anonymous lambda encountered: " ++ (debug_constr ty) ++ fnl ())
      )
    end 
    else if Constr.isCase ty then begin
      (* Constructs a destructor of inductive type.

    [mkCase us ci params p c ac] stand for match [c] as [x] in [I args] return [p] with [ac]
    presented as describe in [ci].


    [p] structure is [args x |- "return clause"]

    [ac]{^ ith} element is ith constructor case presented as
    {e construct_args |- case_term } *)
      let (case_info, _univs, _params, _ret_clause, _iv, discriminee, branches) = Constr.destCase ty in
      msg_debug (str "Case: " ++ debug_constr discriminee ++ fnl ());
      let inductive = case_info.Constr.ci_ind in
      let branches_list = List.mapi (fun idx ((bindings_arr : (Names.Name.t,Sorts.relevance) Context.pbinder_annot array), branch) ->
        let bindings  = Array.to_list ( bindings_arr) in
        let branch_local_bindings : ty_param list = List.map (fun decl -> match decl.Context.binder_name with 
                                                                          | Names.Name x -> x
                                                                          | _ -> failwith "Anonymous binding in branch") bindings in
        let param_count = case_info.Constr.ci_npar in
        let arg_names = List.map (fun x -> PVar x) branch_local_bindings in
        let constructor = Constr.mkConstructUi ((UVars.in_punivs inductive), idx + 1) in
        let constructor_name = 
          (match aux locals i constructor with
          | Some (DCtr (c, [])) -> c
          | _ -> failwith "Not a constructor")
        in 
        let wilds = List.init param_count (fun _ -> PWild) in
        let pattern = PCtr (constructor_name, wilds @ arg_names) in
        let branch_local_names : Names.Name.t list = List.map (fun name -> Names.Name.mk_name  name) branch_local_bindings in
        let branch_rocq = 
          (match aux (List.rev branch_local_names @ locals) i branch with
          | Some x -> x
          | _ -> failwith "Branch not parsed")
        in
        (pattern, branch_rocq))
        (Array.to_list branches)
      in 
      (match aux locals i discriminee with
      | Some discriminee_rocq -> Some (DMatch (discriminee_rocq, branches_list))
      | _ -> failwith "Discriminee not parsed")
    end
    (* Rel, App, Ind, Construct, Prod *)
    else if Constr.isConst ty then begin 
      msg_debug (str "Const: " ++ debug_constr ty ++ fnl ());
      let (x,_) = Constr.destConst ty in 
      Some (DTyVar (Names.Label.to_id (Names.Constant.label x)))
    end
    else if Constr.isSort ty then begin
      if Constr.is_Prop ty then
        Some (DTyCtr (ty_ctr_of_string "Prop", []))
      else if Constr.is_Type ty then
        Some (DTyCtr (ty_ctr_of_string "Type", []))
      else
        CErrors.user_err (str "Sort not handled: " ++ (debug_constr ty) ++ fnl ())
      end
    else (
      let env = Global.env() in
      let sigma = Evd.from_env env in
      CErrors.user_err (str "Dep Case Not Handled: " ++ Printer.pr_constr_env env sigma ty ++ fnl())
    ) in
  aux [] i ty

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
    let dtype = DTyCtr (ty_ctr_of_string "Type", []) in
    let ty_ctr = oib.Declarations.mind_typename in 
    dep_parse_type_params oib.Declarations.mind_arity_ctxt >>= fun ty_params ->
    List.iter (fun tp -> msg_debug (str (ty_param_to_string tp) ++ fnl ())) ty_params;
    dep_parse_constructors (List.length ty_params) ty_params oib >>= fun ctr_reps ->
    let ctr_reps' = List.map (fun (ctr_name, ty) -> 
      ctr_name, dep_arrowify ty (List.map (fun n -> Names.Name n) ty_params) (List.init (List.length ty_params) (fun _ -> dtype))) ctr_reps in
    dep_parse_type (List.length ty_params) ty_params oib.Declarations.mind_arity_ctxt oib >>= fun result_ty -> 
    Some (Libnames.qualid_of_ident ty_ctr, ty_params, ctr_reps', result_ty)
    
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
    Not_found -> failwith ("No Inductives named: " ^ Libnames.string_of_qualid r)

let ty_ctr_to_rocq_relations (r : ty_ctr) : (int * rocq_relation list) option =
  qualid_to_rocq_relations r

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
  Feedback.msg_notice (Ppconstr.pr_constr_expr env sigma c)

let constr_expr_to_string (c : constr_expr) : string =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Ppconstr.pr_constr_expr env sigma c |> Pp.string_of_ppcmds

let relation_unconstrained_variables (relation_type : rocq_constr) : (var * int) list =
  let collect_tyvars i = function
    | DTyVar x -> [(x, i)]
    | _ -> []
  in
  match relation_type with
  | DTyCtr (_, ds) -> List.mapi collect_tyvars ds |> List.concat
  | _ -> []

(*Takes an instance of a relation in a type, like P a (C b) c, and returns 
  [(a, [0]); (b, [1;0]); (c, [2])], the list of variables and their locations*)
let relation_instance_variables (relation_type : rocq_constr) : (var * int list) list =
  let rec collect_tyvars path = function
    | DTyVar x -> [(x, path)]
    | DCtr (_, ds) -> List.concat (List.mapi (fun i d -> collect_tyvars (path @ [i]) d) ds)
    | DApp (d, ds) -> List.concat (List.mapi (fun i d -> collect_tyvars (path @ [i]) d) (d :: ds))
    | _ -> []
  in
  match relation_type with
  | DTyCtr (_, ds) -> List.concat (List.mapi (fun i d -> collect_tyvars [i] d) ds)
  | _ -> failwith "relation_instance_variables works on type constructors only"

let relation_instance_variables' (relation_type : rocq_constr) : (var * int list list) list =
  let vars = relation_instance_variables relation_type in
  let rec insert (v, path) var_paths =
    match var_paths with
    | [] -> [(v, [path])]
    | (v', paths) :: var_paths' -> 
      if v = v' then 
        (v, path :: paths) :: var_paths' 
      else 
        (v', paths) :: insert (v, path) var_paths'
    in
  List.fold_right insert vars []

let remove_duplicates l =
  let rec remove_duplicates' l acc =
    match l with
    | [] -> acc
    | x :: xs -> if List.mem x acc then remove_duplicates' xs acc else remove_duplicates' xs (x :: acc) in
  remove_duplicates' l []

let variables_in_hypothesis (hyp : rocq_constr) : var list =
  let rec collect_tyvars = function
    | DTyVar x -> [x]
    | DCtr (_, ds) -> List.concat (List.map collect_tyvars ds)
    | DApp (_, ds) -> List.concat (List.map collect_tyvars (ds))
    | DTyCtr (_, ds) -> List.concat (List.map collect_tyvars ds)
    | _ -> []
  in
  remove_duplicates (collect_tyvars hyp)

let rec rocq_constr_relations' i = function
  | DProd (_,dt2) -> rocq_constr_relations' i dt2
  | DArrow (dt1, dt2) ->
    (match dt1 with
    | DTyCtr _ -> (i,dt1) :: rocq_constr_relations' (i + 1) dt2 
    | _ -> rocq_constr_relations' (i + 1) dt2)
  | _ -> []
  
let rocq_constr_relations dt = rocq_constr_relations' 0 dt

let theorem_relations_unconstrained_variables dt : (int * (var * int) list) list =
  List.map (fun (i, dt) -> i,relation_unconstrained_variables dt) (rocq_constr_relations dt)

let theorem_variable_uses rocq_thm : (int * (var * int list) list) list =
  List.map (fun (i, dt) -> i,relation_instance_variables dt) (rocq_constr_relations rocq_thm)

let theorem_variable_uses' rocq_thm : (int * (var * int list list) list) list =
  List.map (fun (i, dt) -> i,relation_instance_variables' dt) (rocq_constr_relations rocq_thm)

let rec rocq_constr_one_relation_variables = function
  | DTyCtr (_, ds) -> List.concat (List.map rocq_constr_one_relation_variables ds)
  | DTyVar x -> [x]
  | DCtr (_, ds) -> List.concat (List.map rocq_constr_one_relation_variables ds)
  | DApp (d, ds) -> List.concat (List.map rocq_constr_one_relation_variables (d :: ds))
  | _ -> (*error all args must be abstract*) CErrors.user_err (str "rocq_constr_one_relation_variables: Not a type variable" ++ fnl())


let rec rocq_constr_variables = function
  | DProd ((x,_),dt) -> x :: rocq_constr_variables dt
  | _ -> []

let rocq_constr_var_relation_uses dt : (var * (int * int) list) list =
  let ty_vars = rocq_constr_variables dt in
  let theorem_unconstrained_variables : (int * (var * int) list) list = theorem_relations_unconstrained_variables dt 
in 
  (*for every quantified variable in dt, look in the map from relation indices to lists of associated unconstrained variables, and collect a list of
    relation index and the argument index associated with the variable.*)
  List.map (
    fun v ->
      v, List.concat_map 
          (fun (rel_index, var_indices) ->
            List.filter_map 
              (fun (var, arg_index) -> if v = var then Some (rel_index, arg_index) else None) 
              var_indices) 
          theorem_unconstrained_variables
  ) ty_vars

let rocq_constr_var_relation_uses' dt : (var * (int * int list list) list) list =
  let ty_vars = rocq_constr_variables dt in
  let theorem_var_uses : (int * (var * int list list) list) list = theorem_variable_uses' dt in

  List.map (
    fun v ->
      v, List.concat_map 
          (fun (rel_index, var_uses) ->
            List.filter_map 
              (fun (var, arg_indices) -> if v = var then Some (rel_index, arg_indices) else None) 
              var_uses) 
          theorem_var_uses
  ) ty_vars

(* Patterns in language that derivations target
type pat =
  | PCtr of constructor * pat list
  | PVar of var
  | PParam (* Type parameter *)
  | PWild *)

type monad_sort =
  | MG 
  | MGOpt
  | ME
  | MEOpt
  | MC
  | MId

type derive_sort = D_Gen | D_Enum | D_Check | D_Thm

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
  | MFun of (pat * mexp option) list * mexp 
  | MFix of var * (var * mexp) list * mexp * derive_sort
  | MMutFix of (var * (var * mexp) list * mexp * derive_sort) list * var 
  | MArrow of mexp * mexp
  | MProd of (var * mexp) list * mexp
  
let m_arbitrary ty = MApp (MConst "QuickChick.Classes.arbitrary", [ty; MHole])

let m_arbitraryST prop = MApp (MConst "QuickChick.DependentClasses.arbitraryST", [MHole; prop; MHole])

let m_arbitrarySized ty size = MApp (MConst "QuickChick.Classes.arbitrarySized", [ty; MHole; size])

let m_arbitrarySizeST prop size = MApp (MConst "QuickChick.DependentClasses.arbitrarySizeST", [MHole; prop; MHole; size])

let m_enum ty = MApp (MConst "QuickChick.Classes.enum", [ty; MHole])

let m_enumSuchThat prop = MApp (MConst "QuickChick.DependentClasses.enumSuchThat", [MHole; prop; MHole])

let m_enumSized ty size = MApp (MConst "QuickChick.Classes.enumSized", [ty; MHole; size])

let m_enumSizeST prop size = MApp (MConst "QuickChick.DependentClasses.enumSizeST", [MHole; prop; MHole; size])

let m_fuel = MConst "QuickChick.Decidability.checkable_size_limit"

let m_decOpt prop fuel = MApp (MConst "QuickChick.Decidability.decOpt", [prop; MHole; fuel])

let m_thunkGen gen = MApp (MConst "QuickChick.Generators.thunkGen", [MHole; gen])

type producer_sort = PS_E | PS_G

type rocq_type = rocq_constr

type source = 
  | SrcNonrec of rocq_type
  | SrcRec of var * rocq_constr list
  | SrcMutrec of var * rocq_constr list
  | SrcDef of var * rocq_constr list

let source_to_string = function
  | SrcNonrec t -> rocq_constr_to_string t
  | SrcRec (v, cs) -> Printf.sprintf "Rec(%s %s)" (var_to_string v) (String.concat " " (List.map rocq_constr_to_string cs))
  | SrcMutrec (v, cs) -> Printf.sprintf "Mutrec(%s %s)" (var_to_string v) (String.concat " " (List.map rocq_constr_to_string cs))
  | SrcDef (v, cs) -> Printf.sprintf "Def(%s %s)" (var_to_string v) (String.concat " " (List.map rocq_constr_to_string cs))

type schedule_step =
  | S_UC of var * source * producer_sort
  | S_ST of (var * rocq_type (*** (int list) list*)) list * source * producer_sort (* the (int list) list for each var means the list of all occurences of the same variable
                                                                                        that we wish to produce, any other instance of the var is an input *)
  | S_Check of source * bool (* Source and polarity (true or negated)*)
  | S_Match of var * pat (* Used when you decompose a constructor constrained arg into a fresh variable followed by a pattern match.*)
  | S_Let of var * rocq_constr 

let schedule_step_to_string (s : schedule_step) =
  match s with
  | S_UC (v, s, ps) -> Printf.sprintf "%s <-%s %s" (var_to_string v) (match ps with PS_E -> "E" | PS_G -> "G") (source_to_string s) 
  | S_ST (vs, s, ps) -> Printf.sprintf "(%s) <-%s %s" (String.concat ", " (List.map (fun (v, t) -> Printf.sprintf "%s : %s" (var_to_string v) (rocq_constr_to_string t)) vs)) (match ps with PS_E -> "E" | PS_G -> "G") (source_to_string s) 
  | S_Check (s,pol) -> Printf.sprintf "check %s%s" (if pol then "" else "~ ")(source_to_string s)
  | S_Match (v, p) -> Printf.sprintf "match %s with %s" (var_to_string v) (pat_to_string p)
  | S_Let (v, c) -> Printf.sprintf "let %s = %s" (var_to_string v) (rocq_constr_to_string c)

type is_constrained = bool

type schedule_sort = ProducerSchedule of is_constrained * producer_sort * rocq_constr (* tuple of produced outputs from conclusion of constructor *)
                   | CheckerSchedule (* checkers need not bother with conclusion of constructor, only hypotheses need be checked and conclusion of constructor follows *)
                   | TheoremSchedule of rocq_constr * bool (* conclusion of theorem to be checked, bool true if typeclass used false if function used. *)

type schedule = schedule_step list * schedule_sort

let schedule_sort_to_string = function
  | ProducerSchedule (true, ps, c) -> Printf.sprintf "return%s (Some %s)" (match ps with PS_E -> "Enum" | PS_G -> "Gen") (rocq_constr_to_string c)
  | ProducerSchedule (false, ps, c) -> Printf.sprintf "return%s %s" (match ps with PS_E -> "Enum" | PS_G -> "Gen") (rocq_constr_to_string c)
  | CheckerSchedule -> "relation satisfied"
  | TheoremSchedule (concl,_) -> Printf.sprintf "check conclusion: %s" (rocq_constr_to_string concl)

let schedule_to_string (s : schedule) =
  let (steps, sort) = s in
  Printf.sprintf "do %s \n=> %s\n" (String.concat " ;\n " (List.map schedule_step_to_string steps)) (schedule_sort_to_string sort)

let rec product_free_rocq_type_to_mexp (rt : rocq_type) : mexp =
  match rt with
  | DArrow (_,_) -> failwith "Not a product_free type"
  | DProd (_,_) -> failwith "Not a product-free type"
  | DMatch _ -> failwith "Not a product-free type: Matches contain bindings"
  | DLambda _ -> failwith "Not a product-free type: Lambdas contain bindings"
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

let tuple_of_list (pair : 'a -> 'a -> 'a) (xs : 'a list) (def : 'a option) : 'a = (*Maybe need to convert to pattern pair?*)
  match xs with
  | [] -> (match def with Some a -> a | _ -> failwith "No empty tuples")
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

let c_Type = CAst.make @@ Constrexpr.CSort expr_Set_sort

let c_pair x y = c_app (cInject "Coq.Init.Datatypes.pair") [c_hole; c_hole; x; y]

let c_tuple_of_list xs = tuple_of_list c_pair xs None

let pat_tuple_of_list xs = tuple_of_list (fun x y -> PCtr (constructor_of_string "Coq.Init.Datatypes.pair", [PWild; PWild; x; y])) xs None

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
                              
let c_if cond c1 c2 : constr_expr =
  CAst.make @@ CIf (cond, (None, None) , c1, c2)

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

let c_bindGen gen k = c_app (cInject "QuickChick.Generators.bindGen") [c_hole; c_hole; gen; k]

let c_bindOpt prod k = c_app (cInject "QuickChick.Producer.bindOpt") [c_hole; c_hole; c_hole; c_hole; prod; k]

let c_andBind check k = c_app (cInject "QuickChick.Decidability.andBind") [check; k]

let c_checker c = c_app (cInject "QuickChick.Checker.checker") [c_hole; c_hole; c]

let c_None ty = c_app (cInject "Coq.Init.Datatypes.None") [ty]

let c_Some ty x = c_app (cInject "Coq.Init.Datatypes.Some") [ty; x]

let c_tt = cInject "Coq.Init.Datatypes.tt"

let c_false = cInject "Coq.Init.Datatypes.false"

let c_succ x = c_app (cInject "Coq.Init.Datatypes.S") [x]

let c_zero =  (cInject "Coq.Init.Datatypes.O")



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
  | D_Check -> c_Some c_hole c_false
  | D_Thm -> c_checker c_tt

let c_out_of_fuel (ds : derive_sort) : constr_expr =
  match ds with
  | D_Gen -> c_fail D_Gen
  | D_Enum -> c_ret D_Enum (c_None c_hole)
  | D_Check -> c_None c_hole
  | D_Thm -> c_checker c_tt

let c_guard check k (ds : derive_sort) = 
  c_match 
    (* ?catchAll:(Some (Some (c_fail ds)))  *)
    check 
    [(PCtr (constructor_of_string "Coq.Init.Datatypes.Some", [PWild; PCtr (constructor_of_string "Coq.Init.Datatypes.true",[])]), k);
     (PCtr (constructor_of_string "Coq.Init.Datatypes.Some", [PWild; PCtr (constructor_of_string "Coq.Init.Datatypes.false",[])]), c_fail ds);
     (PCtr (constructor_of_string "Coq.Init.Datatypes.None", [PWild]), c_out_of_fuel ds)]
  
  (* c_if check k (c_fail ds) *)

let c_bindEnum enum k = c_app (cInject "QuickChick.Enumerators.bindEnum") [c_hole; c_hole; enum; k]

let c_enumerating enum k init_size = c_app (cInject "QuickChick.Enumerators.enumerating") [c_hole; enum; k; init_size]

let c_enumeratingOpt enum k init_size = c_app (cInject "QuickChick.Enumerators.enumeratingOpt") [c_hole; enum; k; init_size]

let c_forAll check k = c_app (cInject "QuickChick.Checker.forAll") [c_hole; c_hole; c_hole; c_hole; check; k]

let c_forAllChecker check k = c_app (cInject "QuickChick.Checker.forAllChecker") [c_hole; c_hole; check; k]

let c_forAllMaybe check k = c_app (cInject "QuickChick.Checker.forAllMaybe") [c_hole; c_hole; c_hole; c_hole; check; k]

let c_forAllMaybeChecker check k = c_app (cInject "QuickChick.Checker.forAllMaybeChecker") [c_hole; c_hole; check; k]

let c_quickCheck p = c_app (cInject "QuickChick.Test.quickCheck") [c_hole; c_hole; p]

let c_show typ = c_app (cInject "QuickChick.Show.show") [c_hole; c_hole; typ]

let c_sized typ = c_app (cInject "QuickChick.Producer.sized") [c_hole; c_hole; c_hole; typ]

let c_theorem = cInject "theorem"

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
  | D_Gen, MC -> c_guard m1 k ds
  | D_Enum, ME -> c_bindEnum m1 k
  | D_Enum, MEOpt -> c_bindOpt m1 k
  | D_Enum, MC -> c_guard m1 k ds
  | D_Check, MC -> c_andBind m1 k
  | D_Check, ME -> c_enumerating m1 k (c_var (var_of_string "init_size"))
  | D_Check, MEOpt -> c_enumeratingOpt m1 k (c_var (var_of_string "init_size"))
  | D_Thm, MC -> c_guard m1 k ds
  | D_Thm, MG -> c_forAllChecker m1 k
  | D_Thm, MGOpt -> c_forAllMaybeChecker m1 k
  | _, _ -> failwith ("Invalid bind for derive_sort" ^ derive_sort_to_string ds ^ " and monad_sort " ^ monad_sort_to_string ms)

let c_backtrack (ds : derive_sort) (is_constrained : bool) (first : constr_expr) (ms : constr_expr list) : constr_expr =
  match ds, is_constrained with
  | D_Gen, true -> c_app (cInject "QuickChick.Generators.backtrack") [c_hole; c_list c_hole @@ ms] (* ms : list (nat * G (option A)) *)
  | D_Gen, false -> c_app (cInject "QuickChick.Generators.freq_") [c_hole; first; c_list c_hole @@ ms]
  | D_Enum, true -> c_app (cInject "QuickChick.Enumerators.enumerate") [c_hole; c_list c_hole @@ ms] (* ms : list (E (option A))*)
  | D_Enum, false -> c_app (cInject "QuickChick.Producer.oneOf_") [c_hole; c_hole; c_hole; first; c_list c_hole @@ ms]
  | D_Check, _ -> c_app (cInject "QuickChick.Decidability.checker_backtrack") [c_list c_hole @@ ms] (* ms : list (unit -> option A)*)
  | D_Thm, _ -> failwith "Backtrack not supported for theorems."

let rec mexp_to_constr_expr (me : mexp) (ds : derive_sort) : constr_expr =
  match me with
  | MBind (ms, m, vs, k) -> c_bind ms ds (mexp_to_constr_expr m ds) vs (mexp_to_constr_expr k ds)
  | MRet m -> c_ret ds (mexp_to_constr_expr m ds)
  | MFail -> c_fail ds
  | MOutOfFuel -> c_out_of_fuel ds
  | MId v -> c_var v
  | MApp (m, ms) -> c_app (mexp_to_constr_expr m ds) (List.map (fun m -> mexp_to_constr_expr m ds) ms)
  | MCtr (c, ms) -> c_app (c_constructor c) (List.map (fun m -> mexp_to_constr_expr m ds) ms)
  | MTyCtr (c, []) when c = ty_ctr_of_string "Type" -> c_Type 
  | MTyCtr (c, ms) -> c_app (c_ty_ctr c) (List.map (fun m -> mexp_to_constr_expr m ds) ms)
  | MConst s -> cInject s
  | MEscape e -> e
  | MMatch (m, pms) -> c_match (mexp_to_constr_expr m ds) (List.map (fun (p,m) -> (p, mexp_to_constr_expr m ds)) pms)
  | MHole -> c_hole
  | MLet (v, m1, m2) -> c_let v (mexp_to_constr_expr m1 ds) (mexp_to_constr_expr m2 ds)
  | MBacktrack (default, ms, is_constrained, ds) -> c_backtrack ds is_constrained (mexp_to_constr_expr default ds) (List.map (fun case -> mexp_to_constr_expr case ds) ms)
  | MFun (vs, m) -> c_fun (List.map (fun (v,ty) -> v, option_map (fun ty -> mexp_to_constr_expr ty ds) ty) vs) (fun _ -> (mexp_to_constr_expr m ds))
  | MFix (f, vs, m, ds) ->
    let lid = CAst.make f in
    let args = List.map (fun (v,ty) -> CLocalAssum ([CAst.make @@ Names.Name v], None, Default Glob_term.Explicit, mexp_to_constr_expr ty ds)) vs in
    CAst.make @@ CFix (lid, [(lid,None,None,args,c_hole, mexp_to_constr_expr m ds)])
  | MMutFix (funs, v) ->
    let funs = List.map (fun (f, vs, m, ds) -> 
      let lid = CAst.make f in
      let args = List.map (fun (v,ty) -> CLocalAssum ([CAst.make @@ Names.Name v], None, Default Glob_term.Explicit, mexp_to_constr_expr ty ds) ) vs in
      (lid, None, None, args, c_hole, mexp_to_constr_expr m ds)) funs in
    CAst.make @@ CFix (CAst.make v, funs)

let rec mexp_to_string (me : mexp) : string =
  match me with
  | MBind (ms, m, vs, k) -> Printf.sprintf "bind_%s %s (fun %s -> %s)" (monad_sort_to_string ms) (mexp_to_string m) (String.concat " " (List.map var_to_string vs)) (mexp_to_string k)
  | MRet m -> Printf.sprintf "ret %s" (mexp_to_string m)
  | MFail -> "fail"
  | MOutOfFuel -> "out_of_fuel"
  | MId v -> var_to_string v
  | MApp (m, ms) -> Printf.sprintf "%s %s" (mexp_to_string m) (String.concat " " (List.map mexp_to_string ms))
  | MCtr (c, ms) -> Printf.sprintf "%s %s" (constructor_to_string c) (String.concat " " (List.map mexp_to_string ms))
  | MTyCtr (c, ms) -> Printf.sprintf "%s %s" (ty_ctr_to_string c) (String.concat " " (List.map mexp_to_string ms))
  | MConst s -> s
  | MEscape e -> constr_expr_to_string e
  | MMatch (m, pms) -> Printf.sprintf "match %s with %s" (mexp_to_string m) (String.concat " | " (List.map (fun (p,m) -> Printf.sprintf "%s -> %s" (pat_to_string p) (mexp_to_string m)) pms))
  | MHole -> "_"
  | MLet (v, m1, m2) -> Printf.sprintf "let %s = %s in %s" (var_to_string v) (mexp_to_string m1) (mexp_to_string m2)
  | MBacktrack (default, ms, is_constrained, ds) -> Printf.sprintf "backtrack %s %s %s %s" (mexp_to_string default) (String.concat " " (List.map mexp_to_string ms)) (if is_constrained then "true" else "false") (derive_sort_to_string ds)
  | MFun (vs, m) -> Printf.sprintf "fun %s -> %s" (String.concat " " (List.map (fun (v,ty) -> Printf.sprintf "%s%s" (pat_to_string v) (
    (match ty with 
    | None -> ""
    | Some ty -> Printf.sprintf " : %s" (mexp_to_string ty)))) vs)) (mexp_to_string m)
  (* | MFix (f, vs, m, ds) -> Printf.sprintf "fix %s %s = %s in %s" (var_to_string f) (String.concat " " (List.map (fun (v,ty) -> Printf.sprintf "%s%s" (pat_to_string v) (
    (match ty with 
    | None -> ""
    | Some ty -> Printf.sprintf " : %s" (mexp_to_string ty))) vs)) (mexp_to_string m) (derive_sort_to_string ds)
  | MMutFix (funs, v) -> 
    let fun_to_string (f, vs, m, ds) is_first = Printf.sprintf "%s %s %s = %s in %s" (if is_first then "fix" else "and") (var_to_string f) (String.concat " " (List.map (fun (v,ty) -> Printf.sprintf "%s%s" (pat_to_string v) (
      (match ty with 
      | None -> ""
      | Some ty -> Printf.sprintf " : %s" (mexp_to_string ty))) vs)) (mexp_to_string m) (derive_sort_to_string ds) in *)



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
  | PS_E -> m_enumSized ty (MId (var_of_string "init_size"))
  | PS_G -> m_arbitrarySized ty (MId (var_of_string "init_size"))

let such_that_producer (ps : producer_sort) vars p =
  let p_vars = List.map (fun v -> PVar v) vars in
  let arg_tuple = pat_tuple_of_list p_vars in
  let p_with_args = MFun ([arg_tuple,None], p) in
  match ps with
  | PS_E -> m_enumSizeST p_with_args (MId (var_of_string "init_size"))
  | PS_G -> m_arbitrarySizeST p_with_args (MId (var_of_string "init_size"))
  
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

let mut_rec_call fuel r args =
  MApp (MId r, fuel :: MId (var_of_string "init_size") :: MId (var_of_string "size'") :: List.map product_free_rocq_type_to_mexp args)

let def_call fuel r args =
  MApp (MId r, fuel :: List.map product_free_rocq_type_to_mexp args)

let m_negb_opt x = MApp (MConst "QuickChick.Decidability.negbOpt", [x])

let schedule_step_to_mexp (step : schedule_step) mfuel (def_fuel : mexp) : mexp -> mexp = fun k ->
  match step with
  | S_UC (v, prod, ps) -> 
    let producer = (match prod with
      | SrcNonrec ty -> unconstrained_producer ps (product_free_rocq_type_to_mexp ty)
      | SrcRec (rec_f, args) -> rec_call rec_f args
      | SrcMutrec (rec_f, args) -> mut_rec_call mfuel rec_f args
      | SrcDef (def_f, args) -> def_call def_fuel def_f args) in
    MBind (prod_sort_to_monad_sort ps, producer, [v], k)
  | S_ST (vars_tys, prod, ps) -> 
    let producer = (match prod with
      | SrcNonrec ty -> such_that_producer ps (List.map fst vars_tys) (product_free_rocq_type_to_mexp ty)
      | SrcRec (rec_f, args) -> rec_call rec_f args
      | SrcMutrec (rec_f, args) -> mut_rec_call mfuel rec_f args
      | SrcDef (def_f, args) -> def_call def_fuel def_f args) in
    let vars = List.map fst vars_tys in
    MBind (prod_sort_to_monad_opt_sort ps, producer, vars, k)
  | S_Check (src,pol) -> 
    let checker = (match src with
      | SrcNonrec ty -> m_decOpt (product_free_rocq_type_to_mexp ty) m_fuel
      | SrcRec (rec_f, args) -> rec_call rec_f args
      | SrcMutrec (rec_f, args) -> mut_rec_call mfuel rec_f args
      | SrcDef (def_f, args) -> def_call def_fuel def_f args) in
    MBind (MC, (if pol then checker else m_negb_opt checker), [], k)
  | S_Match (v, p) -> 
    if total_pat p then
      MMatch (MId v, [(p, k)])
    else
      MMatch (MId v, [(p, k); (PWild, MFail)])
  | S_Let (v, c) -> MLet (v, product_free_rocq_type_to_mexp c, k)

(* Theorem = producer composed with a checker *)

let m_Some ty x = MApp (MConst "Coq.Init.Datatypes.Some", [ty; x])

let m_None ty = MApp (MConst "Coq.Init.Datatypes.None", [ty])

let m_bool = MConst "Coq.Init.Datatypes.bool"

let m_true = MConst "Coq.Init.Datatypes.true"

let m_false = MConst "Coq.Init.Datatypes.false"

let m_mul x y = MApp (MConst "Coq.Init.Nat.mul", [x; y])

let m_three = MConst "Coq.Init.Nat.S (Coq.Init.Nat.S (Coq.Init.Nat.S Coq.Init.Datatypes.O))"

let m_theorem_check_fuel mfuel = 
  m_mul m_three mfuel

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
let schedule_to_mexp ((steps, s_sort) : schedule) (mfuel : mexp) (def_fuel : mexp) : mexp =
  let finally = match s_sort with
    | ProducerSchedule (is_constrained, ps, concl_outputs) -> MRet ((if is_constrained then m_Some MHole else (fun x -> x)) @@ product_free_rocq_type_to_mexp concl_outputs)
    | CheckerSchedule -> MRet (m_Some m_bool m_true)
    | TheoremSchedule (DNot concl, true) -> match_optbool (m_negb_opt @@ m_decOpt (product_free_rocq_type_to_mexp concl) (m_theorem_check_fuel m_fuel)) (MRet (m_Some m_bool m_true)) (MRet (m_Some m_bool m_false)) MOutOfFuel
    | TheoremSchedule (DNot concl, false) -> match_optbool (m_negb_opt @@ product_free_rocq_type_to_mexp concl) (MRet (m_Some m_bool m_true)) (MRet (m_Some m_bool m_false)) MOutOfFuel
    | TheoremSchedule (concl, true) -> match_optbool (m_decOpt (product_free_rocq_type_to_mexp concl) m_fuel) (MRet (m_Some m_bool m_true)) (MRet (m_Some m_bool m_false)) MOutOfFuel
    | TheoremSchedule (concl, false) -> match_optbool (product_free_rocq_type_to_mexp concl) (MRet (m_Some m_bool m_true)) (MRet (m_Some m_bool m_false)) MOutOfFuel
  in
  List.fold_right (fun schd acc -> schedule_step_to_mexp schd mfuel def_fuel acc) steps finally

(* let type_of_schedule (ischd_name, inps, nonrec_schds, rec_schds : inductive_schedule) (ds : derive_sort) (is_constrained : bool) : mexp = *)



let fuel_zero = MConst "Coq.Init.Datatypes.O"
let fuel_size = MId (var_of_string "size")
let fuel_sizem = MId (var_of_string "sizem")
let fuel_init_size = MId (var_of_string "init_size")

let schedule_to_constr_expr (s : schedule) (ds : derive_sort) : constr_expr =
  mexp_to_constr_expr (schedule_to_mexp s (MId (var_of_string "size")) (MId (var_of_string "init_size"))) ds

let compile_and_print_schedule (s : schedule) (ds : derive_sort) : unit =
  let ce = schedule_to_constr_expr s ds in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Feedback.msg_notice (Ppconstr.pr_constr_expr env sigma ce ++ fnl())

let compile_and_pp_schedule (s : schedule) (ds : derive_sort) : Pp.t =
  let ce = schedule_to_constr_expr s ds in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (Ppconstr.pr_constr_expr env sigma ce ++ fnl())

module VarOrd = struct
  type t = var
  let compare x y = compare (var_to_string x) (var_to_string y)
end

module VM = Map.Make(VarOrd)
(* module US = Set.Make(UnknownOrd) *)

module VS = Set.Make(VarOrd)

type var_set = VS.t
          
(* Maps input variables to patterns *)
type pat_map = pat VM.t

type inductive_schedule = string * (var * mexp) list * (var * mexp list) list * (schedule * (var * pat) list) list * (schedule * (var * pat) list) list 
  (*Name string, fixed input variable/type list, type variable/required typeclasses, list of base schedules, and a list non base schedules paired with how they match on those variables*)

type mutual_inductive_chain = inductive_schedule list list

type inductive_schedule_with_dependencies = inductive_schedule list * string

let inductive_schedule_to_string (is : inductive_schedule) : string =
  let (name, inputs, param_deps, base_scheds, rec_scheds) = is in
  let inputs_str = String.concat ", " (List.map (fun (v, ty) -> var_to_string v ^ " : " ^ mexp_to_string ty) inputs) in
  let param_deps_str = String.concat ", " (List.map (fun (v, ty) -> var_to_string v ^ " : " ^ String.concat ", " (List.map mexp_to_string ty)) param_deps) in
  let base_scheds_str = String.concat " \n|\n\n " (List.map (fun (s, inp_pats) -> schedule_to_string s) base_scheds) in
  let rec_scheds_str = String.concat " \n|\n\n " (List.map (fun (s, inp_pats) -> schedule_to_string s) rec_scheds) in
  Printf.sprintf "Inductive %s (%s) :=\n  Base:\n %s\n  Rec: %s" name inputs_str base_scheds_str rec_scheds_str

let filter_mapi (f : int -> 'a -> 'b option) (l : 'a list) : 'b list =
  let rec aux i l =
    match l with
    | [] -> []
    | now :: after -> 
      match f i now with
      | Some x -> x :: aux (i + 1) after
      | None -> aux (i + 1) after in
  aux 0 l

let schedule_step_dependence (s : schedule_step) : (rocq_constr * int list * derive_sort * bool) option =
  match s with
  | S_UC (v, SrcNonrec (DTyParam param), ps) -> None (*Parameters handled elsewhere*)
  | S_UC (v, SrcNonrec t, ps) -> Some (t, [], (match ps with PS_E -> D_Enum | PS_G -> D_Gen), false)
  | S_ST (vs, SrcNonrec (DTyCtr (ind, args)), ps) -> 
    let output_vars = List.map fst vs in
    let arg_vars = List.map (fun arg -> variables_in_hypothesis arg) args in 
    let output_idxs = filter_mapi (fun i arg_vars -> if List.exists (fun v -> List.mem v arg_vars) output_vars then Some i else None) arg_vars in
    Some (DTyCtr (ind, args), output_idxs, (match ps with PS_E -> D_Enum | PS_G -> D_Gen), true)
  | S_Check (SrcNonrec (DTyCtr (c, [DTyParam _;_;_])), pol) when c = constructor_of_string "Coq.Init.Datatypes.eq" -> 
    None (*Parameters handled elsewhere*)
  | S_Check (SrcNonrec t, pol) -> Some (t, [], D_Check, true)
  | S_Match _ | S_UC _ 
  | S_ST    _ | S_Check _ 
  | S_Let _ -> None

let schedule_dependents ((steps, final) : schedule) : (rocq_constr * int list * derive_sort * bool) list =
  let final_depends = match final with
  | TheoremSchedule (t,not_def) -> if not_def then [(t, [], D_Check, true)] else [] 
  | _ -> [] in
  final_depends @ List.filter_map schedule_step_dependence steps

let schedule_with_dependents (s : schedule) : (schedule_step * (rocq_constr * int list * derive_sort * bool) option) list * (schedule_sort * (rocq_constr * int list * derive_sort * bool) option) =
  let (steps, final) = s in
  let final_depends = match final with
  | TheoremSchedule (t,true) -> final, Some (t, [], D_Check, true)
  | TheoremSchedule (t,false) -> final, None
  | _ -> final, None in

  let step_depends = List.map (fun step -> (step, schedule_step_dependence step)) steps in

  step_depends, final_depends

(* let parameter_dependents_from_ind_sched =  *)

let inductive_schedule_dependents (is : inductive_schedule) : (rocq_constr * int list * derive_sort * bool) list =
  let (_, _, param_deps, base_scheds, rec_scheds) = is in
  List.concat (List.map (fun (schd,_) -> schedule_dependents schd) (base_scheds @ rec_scheds))

let inductive_schedule_with_dependents (is : inductive_schedule) =
  let (name, vars, param_deps, base_scheds, rec_scheds) = is in
  let match_schd_deps = List.map (fun (schd,matches) -> schedule_with_dependents schd, matches) in
  name, vars, match_schd_deps base_scheds, match_schd_deps rec_scheds

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
  | D_Thm -> failwith ("Backtrack not supported for theorems: " ^ mexp_to_string m)

let inductive_schedule_to_mexp (is : inductive_schedule) (ds : derive_sort) (is_constrained : bool) : mexp =
  let (name, inputs, param_deps, base_scheds, rec_scheds) = is in
  Feedback.msg_notice (str ("Compiling inductive schedule: " ^ name) ++ fnl());
  if ds = D_Thm && name = "theorem" then begin
    let thm_mexp = 
      (match base_scheds with
      | [(s, inp_pats)] -> schedule_to_mexp s fuel_size fuel_size
      | _ -> failwith "Expected a single base schedule for the theorem") in
    MFun ([PVar (var_of_string "size"), Some (MConst "Coq.Init.Datatypes.nat")], thm_mexp) 
    end 
  else begin

  let nat_ty = MConst "Coq.Init.Datatypes.nat" in
  let prelude base_k all_k rec_scheds = 
    match rec_scheds with
    | [] -> MFun ([PVar (var_of_string "size'"), Some (MConst "Coq.Init.Datatypes.nat"); PVar (var_of_string "init_size"), Some (MConst "Coq.Init.Datatypes.nat")] 
                    @ List.map (fun (i,ty) -> PVar i, Some ty) inputs,
                  base_k)
    | _ -> 
      MFix (var_of_string "rec", (var_of_string "init_size", nat_ty) :: (var_of_string "size", nat_ty) :: inputs, 
        MMatch (MId (var_of_string "size"), 
                [
                  (PCtr (constructor_of_string "Coq.Init.Datatypes.O", []), 
                    base_k);
                  (PCtr (constructor_of_string "Coq.Init.Datatypes.S", [PVar (var_of_string "size'")]), 
                    all_k);
                ]), ds) in
  let match_pats inp_pats (k : mexp) =
    List.fold_left (fun acc (v, pat) -> 
      MMatch (MId v, (pat, acc) :: (if total_pat pat then [] else [(PWild, MFail)]))
    ) k inp_pats in
  let base_backtrack = 
    let add_on = if is_constrained && (ds = D_Check || ds = D_Enum && rec_scheds <> []) then [backtrack_decoration ds Base (MOutOfFuel)] else [] in
    List.map (fun (s, inp_pats) -> 
    backtrack_decoration ds Base (match_pats inp_pats (schedule_to_mexp s fuel_sizem fuel_init_size))) base_scheds @ add_on in
  let base_backtrack_for_all = List.map (fun (s, inp_pats) -> 
    backtrack_decoration ds Base (match_pats inp_pats (schedule_to_mexp s fuel_sizem fuel_init_size))) base_scheds in (*TODO: FIX FUEL SIZE*)
  let rec_backtrack = List.map (fun (s, inp_pats) ->
    backtrack_decoration ds Rec (match_pats inp_pats (schedule_to_mexp s fuel_sizem fuel_init_size))) rec_scheds in
  let all_backtrack = base_backtrack_for_all @ rec_backtrack in
  let fun_name = var_of_string (name ^ derive_sort_to_string ds) in
  let final_let fixp = 
    MLet (fun_name, 
          fixp, 
          MFun ([PVar (var_of_string "size"), Some (MConst "Coq.Init.Datatypes.nat")], 
            MApp (MId fun_name,
                  [MId (var_of_string "size"); MId (var_of_string "size")]))) in
  let first = 
    match base_scheds with
    | [] -> failwith "TODO: handle empty inductives"
    | (s, inp_pats) :: _ -> match_pats inp_pats (schedule_to_mexp s fuel_sizem fuel_init_size) in
  
  final_let (prelude (MBacktrack (first, base_backtrack, is_constrained, ds)) (MBacktrack (first, all_backtrack, is_constrained, ds)) rec_scheds)
  end

let inductive_schedule_with_dependencies_to_mexp unconstrained_inds (ind_schds : (inductive_schedule * derive_sort * is_constrained) list) (output_ind_schd_name : string) : mexp =
  let match_pats inp_pats (k : mexp) =
    List.fold_left (fun acc (v, pat) -> 
      MMatch (MId v, (pat, acc) :: (if total_pat pat then [] else [(PWild, MFail)]))
    ) k inp_pats in
  let prelude base_k all_k = 
  MMatch (MId (var_of_string "sizem"), 
          [
            (PCtr (constructor_of_string "Coq.Init.Datatypes.O", []), 
              base_k);
            (PCtr (constructor_of_string "Coq.Init.Datatypes.S", [PVar (var_of_string "sizem")]), 
              all_k);
          ]) in
  let dependency_mexp ((ind_schd_name,inputs,param_deps,base_scheds,_) as is, ds, is_constrained) = 
    Feedback.msg_notice (str ("Compiling inductive schedule: " ^ ind_schd_name) ++ str " " ++ str (derive_sort_to_string ds) ++ str " " ++ str (if is_constrained then "constrained" else "unconstrained") ++ fnl());
    let first = 
      match base_scheds with
      | [] -> failwith "TODO: handle empty inductives"
      | (s, inp_pats) :: _ -> match_pats inp_pats (schedule_to_mexp s fuel_zero fuel_init_size) in
    let out_of_fuel =
      (match ds, is_constrained with
      | D_Gen, true | D_Enum, true | D_Check, _ | D_Thm, true -> MOutOfFuel
      | _ -> first) in
    if ds = D_Thm && ind_schd_name = "theorem" then begin
      (* let thm_mexp = 
        (match base_scheds with
        | [(s, inp_pats)] -> schedule_to_mexp s fuel_sizem fuel_init_size
        | _ -> failwith "Expected a single base schedule for the theorem") in
      let add_fuel_let = MLet (var_of_string "size", MId (var_of_string "sizem"), thm_mexp) in
      (var_of_string "theorem", [(var_of_string "sizem"), (MConst "Coq.Init.Datatypes.nat")], prelude (MFun ([], out_of_fuel)) add_fuel_let, D_Thm)
      end *)
      failwith "Theorems should not be in a mutual fixpoint ever"
    end
    else 
    (* let mexp = 
      (match inductive_schedule_to_mexp is ds is_constrained with
      | MLet (fun_name, fixp, MFun (_,body)) -> MLet (var_of_string "size", MCtr (constructor_of_string "Coq.Init.Datatypes.S", [MId (var_of_string "sizem")]), MLet (fun_name, fixp, body))
      | m -> failwith "Expected a let binding") in *)
    let mexp = 
      (match inductive_schedule_to_mexp is ds is_constrained with
      | MLet (fun_name, fixp, MFun (_,_)) -> 
        MLet (fun_name, fixp, 
          (MApp (MId fun_name,
            [MId (var_of_string "init_size"); MId (var_of_string "size'")])))
        
   
      | m -> failwith "Expected a let binding") in

    (var_of_string ind_schd_name, List.map (fun v -> (var_of_string v), (MConst "Coq.Init.Datatypes.nat")) ["sizem";"init_size";"size'"], prelude (MFun (List.map (fun (x,t) -> PVar x, Some t) inputs, out_of_fuel)) mexp, ds)
  in

  let unconstrained_ind_mexp k = List.fold_left (fun acc ((ind_schd_name,_,_,_,_) as is, ds, is_constrained) -> 
    let mexp = inductive_schedule_to_mexp is ds is_constrained in
    MLet (var_of_string ind_schd_name, mexp, acc)) k unconstrained_inds in

  unconstrained_ind_mexp (MLet (var_of_string output_ind_schd_name, MMutFix (List.map dependency_mexp ind_schds, var_of_string output_ind_schd_name), 
    MFun ([PVar (var_of_string "size"), Some (MConst "Coq.Init.Datatypes.nat")], 
      MApp (MId (var_of_string output_ind_schd_name),
        [MConst "QuickChick.Decidability.mutual_fuel"; MId (var_of_string "size"); MId (var_of_string "size")]))))
  

let turn_def_calls_into_mutrec_calls (ind_schd : inductive_schedule) names : inductive_schedule =
  Feedback.msg_notice (str "Turning def calls into mutrec calls with names: " ++ str (String.concat ", " names) ++ fnl());
  Feedback.msg_notice (str "Inductive schedule: " ++ str (inductive_schedule_to_string ind_schd) ++ fnl());
  let (name, inputs, param_deps, base_scheds, rec_scheds) = ind_schd in

  let update_source (src : source) : source =
    match src with
    | SrcDef (def_f, args) when List.mem (var_to_string def_f) names -> SrcMutrec (def_f, args)
    | _ -> src in

  let turn_def_calls_step (s : schedule_step) : schedule_step =
    match s with
    | S_UC (v, src, ps) -> S_UC (v, update_source src, ps)
    | S_ST (vs, src, ps) -> S_ST (vs, update_source src, ps)
    | S_Check (src, pol) -> S_Check (update_source src, pol)
    | S_Match (v, p) -> S_Match (v, p)
    | S_Let (v, c) -> S_Let (v, c) 
  in

  let turn_def_calls_sched (s : schedule) : schedule =
    let (steps, final) = s in
    let new_steps = List.map turn_def_calls_step steps in
    new_steps, final in

  let new_scheds scheds = List.map (fun (s, inp_pats) -> turn_def_calls_sched s, inp_pats) scheds in

  let new_rec_scheds = new_scheds rec_scheds in

  let (new_mutrec_scheds, new_base_scheds) = List.partition 
    (fun ((steps,_),_) -> List.exists (function
    | S_UC (_, SrcMutrec _, _)
    | S_ST (_, SrcMutrec _, _)
    | S_Check (SrcMutrec _, _) -> true
    | a -> false) steps) (new_scheds base_scheds)
  in

  name, inputs, [], new_base_scheds, new_rec_scheds @ new_mutrec_scheds


(* let inductive_schedules_to_mexp (components : (inductive_schedule * derive_sort * is_constrained) list list) (output_ind_schd_name : string) : mexp =
  let handle_component comp k =
    msg_debug (str "Handling component" ++ fnl());
    msg_debug (int (List.length comp) ++ fnl());
    match comp with
    | [(is, ds, is_constrained)] -> 
      let name = match is with (n,_,_,_) -> n in
      let body = inductive_schedule_to_mexp is ds is_constrained in
      MLet (var_of_string name, body, k)
    | _ -> 
      let names = List.map (fun (is,_,_) -> match is with (n,_,_,_) -> n) comp in
      let comp = List.map (fun (is, ds, is_constrained) -> turn_def_calls_into_mutrec_calls is names, ds, is_constrained) comp in
      let (name, mut_body, res) = match inductive_schedule_with_dependencies_to_mexp [] comp "placeholder" with 
        | MLet (name, mut_body, res) -> name, mut_body, res
        | _ -> failwith "Expected a mut_body in a let" in 
      let update_name n = function MMutFix (funs, _) -> MMutFix (funs, var_of_string n) | _ -> failwith "Expected a MMutFix" in
      List.fold_right (fun name acc -> MLet (var_of_string name, update_name name mut_body, acc)) names k in
  List.fold_right handle_component components (MId (var_of_string output_ind_schd_name)) *)

let inductive_schedules_to_def_mexps (components : (inductive_schedule * derive_sort * is_constrained) list list) (output_ind_schd_name : string) : (var * mexp * derive_sort) list list =
  let handle_component comp =
    msg_debug (str "Handling component" ++ fnl());
    msg_debug (int (List.length comp) ++ fnl());
    match comp with
    | [(is, ds, is_constrained)] -> 
      let name = match is with (n,_,_,_,_) -> n in
      let body = inductive_schedule_to_mexp is ds is_constrained in
      [var_of_string name, body, ds]
    | _ -> 
      let names = List.map (fun (is,_,_) -> match is with (n,_,_,_,_) -> n) comp in
      let comp = List.map (fun (is, ds, is_constrained) -> turn_def_calls_into_mutrec_calls is names, ds, is_constrained) comp in
      let mut_body = inductive_schedule_with_dependencies_to_mexp [] comp "placeholder" in 
      (* let bodies = match mut_body with MMutFix (funs, _) -> funs | _ -> failwith "Expected a MMutFix" in *)
      let body_to_mexp (name, arg_tys, body, ds) = name, MFix (name, arg_tys, body, ds), ds in
      let update_name n = function 
        | MLet (name, MMutFix (funs, _), ds) -> MLet (name, MMutFix (funs, var_of_string n), ds)
        | _ -> failwith "Expected a MLet with MMutFix body" in
        
        (* function MMutFix (funs, _) -> MMutFix (funs, var_of_string n) | _ -> failwith "Expected a MMutFix" in *)
      List.map (fun name -> (var_of_string name, update_name name mut_body, D_Gen)) names in (*Fix to get a ds into scope out of the mut body*)
  
        (*name, MFun (List.map (fun (x,t) -> PVar x, Some t) arg_tys, body), ds in *)
      (* List.map body_to_mexp bodies in *)
  List.map handle_component components

let inductive_schedules_to_def_constr_exprs (components : (inductive_schedule * derive_sort * is_constrained) list list) (output_ind_schd_name : string) : (var * constr_expr) list list =
  let mexp_components = inductive_schedules_to_def_mexps components output_ind_schd_name in

  let handle_component comp =
    List.map (fun (v, m, ds) -> v, mexp_to_constr_expr m ds) comp in

  List.map handle_component mexp_components

let inductive_schedule_with_dependencies_to_constr_expr unconstrained_inds (ind_schds : (inductive_schedule * derive_sort * is_constrained) list) (output_ind_schd_name : string) : constr_expr =
  mexp_to_constr_expr (inductive_schedule_with_dependencies_to_mexp unconstrained_inds ind_schds output_ind_schd_name) D_Gen (*D_Anything works, ds is irrelevant*)

let inductive_schedule_to_constr_expr (is : inductive_schedule) (ds : derive_sort) (is_constrained : bool) : constr_expr =
  mexp_to_constr_expr (inductive_schedule_to_mexp is ds is_constrained) ds

(* let inductive_schedules_to_constr_expr (components : (inductive_schedule * derive_sort * is_constrained) list list) (output_ind_schd_name : string) : constr_expr =
  let mexp = inductive_schedules_to_mexp components output_ind_schd_name in
  (* msg_debug (str "Inductive schedules mexp: " ++ str (mexp_to_string mexp) ++ fnl()); *)
  mexp_to_constr_expr mexp D_Thm *)

type parsed_classes = {gen : rocq_constr list; 
                        enum : rocq_constr list;
                        genST : (var list * rocq_constr) list; 
                        enumST : (var list * rocq_constr) list;
                        checker : rocq_constr list;
                        decEq : rocq_constr list}

let print_parsed_classes parsed =
  let print_list name l = 
    Feedback.msg_notice (str (name ^ ": ") ++ fnl());
    List.iter (fun c -> Feedback.msg_notice (str (rocq_constr_to_string c) ++ fnl())) l in
  let print_list_fun name class_name l = 
    Feedback.msg_notice (str (name ^ ": ") ++ fnl());
    List.iter (fun (vs, c) -> 
      (match vs with
      | [] -> Feedback.msg_notice (str (class_name ^ " () => " ^ rocq_constr_to_string c) ++ fnl())
      | [v] -> Feedback.msg_notice (str (class_name ^ " (fun " ^ (var_to_string v) ^ " => " ^ rocq_constr_to_string c ^ ")") ++ fnl())
      | vs -> Feedback.msg_notice (str (class_name ^ " (fun '(" ^ (String.concat ", " (List.map var_to_string vs)) ^ ") => " ^ rocq_constr_to_string c ^ ")") ++ fnl()))) l in
  print_list "Gen" parsed.gen;
  print_list "Enum" parsed.enum;
  print_list_fun "GenST" "GenSizedSuchThat" parsed.genST;
  print_list_fun "EnumST" "EnumSizedSuchThat" parsed.enumST;
  print_list "Checker" parsed.checker;
  print_list "DecEq" parsed.decEq
  
let ty_ctr_eq (a : ty_ctr) (b : ty_ctr) : bool =
  String.equal (ty_ctr_to_string a) (ty_ctr_to_string b) 
  
let find_typeclass_bindings ctr =
  msg_debug (str ("Finding typeclass bindings for:" ^ Libnames.string_of_qualid ctr) ++ fnl());
  let env = Global.env () in
  let evd = Evd.from_env env in
  let db = Hints.searchtable_map "typeclass_instances" in
(* 
  let prod_check i =
    String.equal (Names.MutInd.to_string (fst i)) ("QuickChick.DependentClasses." ^ typeclass_name)
    || String.equal (Names.MutInd.to_string (fst i)) ("QuickChick.Classes." ^ typeclass_name)  in    
  let dec_check i =
    String.equal (Names.MutInd.to_string (fst i)) ("QuickChick.Decidability." ^ typeclass_name)  in *)

  let type_of_hint hint =
    (* Go from the hint to the type of its constant *)
    let (co, ec) = Hints.hint_as_term hint in
    let c = EConstr.to_constr evd ec in
    match Constr.kind c with
    | Constr.Const cst -> 
      let (typ,_constraints) = Environ.constant_type env cst in
        typ 
    | _ -> failwith ("hint not a constant in search for " ^ Libnames.string_of_qualid ctr)
    in

  let rec find_concl (typ : rocq_constr) : rocq_constr = 
    match typ with
    | DProd (v, t) -> find_concl t
    | DArrow (v, t) -> find_concl t
    | DApp _ -> typ
  in

  let rocq_eq_to_alpha (a : rocq_constr) (b : rocq_constr) : bool = 
    let rec aux (a : rocq_constr) (b : rocq_constr) (m : (var, var) Hashtbl.t) : bool =
      try
      match a, b with
      | DTyParam p1, DTyParam p2 -> String.equal (var_to_string p1) (var_to_string p2)
      | DTyCtr (c1, ds1), DTyCtr (c2, ds2) -> 
        String.equal (ty_ctr_to_string c1) (ty_ctr_to_string c2) && List.for_all2 (fun d1 d2 -> aux d1 d2 m) ds1 ds2
      | DCtr (c1, ds1), DCtr (c2, ds2) -> 
        String.equal (constructor_to_string c1) (constructor_to_string c2) && List.for_all2 (fun d1 d2 -> aux d1 d2 m) ds1 ds2
      | DTyVar v1, DTyVar v2 -> 
        (try 
          let v2' = Hashtbl.find m v1 in
          String.equal (var_to_string v2) (var_to_string v2')
        with Not_found -> 
          Hashtbl.add m v1 v2;
          true)
      | DApp (d1, ds1), DApp (d2, ds2) -> 
        aux d1 d2 m && List.for_all2 (fun d1 d2 -> aux d1 d2 m) ds1 ds2
      | DNot d1, DNot d2 -> aux d1 d2 m
      | DHole, DHole -> true
      | DArrow _, DArrow _ | DProd _, DProd _ | DMatch _, DMatch _ -> failwith ("equality not supported for arrows and products: " ^ rocq_constr_to_string a ^ " =? " ^ rocq_constr_to_string b)
      | _ -> false
      with Invalid_argument _ -> false
    in
    aux a b (Hashtbl.create 10)
  in 

  let rec parse_pair_matches (ins : var list) (matches : rocq_constr) : (var list * rocq_constr) option =
    match matches with
    | DMatch (DTyVar disc, [(PCtr (pair_c, [_;_;PVar x;PVar y]), next_match)]) when String.equal (constructor_to_string pair_c) "Coq.Init.Datatypes.pair" -> 
      let remove_disc = List.filter (fun v -> not (String.equal (var_to_string v) (ty_param_to_string disc))) ins in
      parse_pair_matches (y :: x :: remove_disc) next_match
    | DTyCtr (ind_relation, args) as concl -> Some (List.rev ins, concl)
    | _ -> None 
  in

  let rec add_class (parsed : parsed_classes) (class_instance : rocq_constr) (ind_name : ty_ctr) : parsed_classes =
    match class_instance with
    | DTyCtr (c, [DTyCtr (ind_relation, args)]) when ty_ctr_eq ind_relation ind_name -> 
      msg_debug (str "Processing instance of " ++ str (ty_ctr_to_string ind_name) ++ fnl ());
      (match ty_ctr_to_string c with
      | "QuickChick.Classes.GenSized" | "GenSized" -> {parsed with gen = class_instance :: parsed.gen}
      | "QuickChick.Classes.EnumSized" | "EnumSized" -> {parsed with enum = class_instance :: parsed.enum}
      | "QuickChick.Decidability.DecOpt" | "QuickChick.Decidability.Dec" | "DecOpt" | "Dec" -> {parsed with checker = class_instance :: parsed.checker}
      | "QuickChick.Decidability.Dec_Eq" | "Dec_Eq" -> {parsed with decEq = class_instance :: parsed.decEq}
      | _ -> msg_debug (str "Unknown non such that class: " ++ 
                        str (ty_ctr_to_string c) ++ str " for constr: " ++ 
                        str (rocq_constr_to_string class_instance) ++ fnl ()); 
             parsed  
      )
    | DTyCtr (c, [DTyCtr (ind_relation,args)]) -> 
      msg_debug ( str "Skipping instance of " ++ str (ty_ctr_to_string ind_relation) ++ fnl ());
      parsed
    | DTyCtr (c, [typ; DLambda (v, ty, e)]) ->
      (match parse_pair_matches [v] e with
      | Some ((ins, DTyCtr (ind_relation, args)) as instance) when ty_ctr_eq ind_relation ind_name -> 
        (match ty_ctr_to_string c with
        | "QuickChick.DependentClasses.GenSizedSuchThat" | "GenSizedSuchThat" -> {parsed with genST = instance :: parsed.genST}
        | "QuickChick.DependentClasses.EnumSizedSuchThat" | "EnumSizedSuchThat" -> {parsed with enumST = instance :: parsed.enumST}
        | _ -> msg_debug (str "Unknown such that class: " ++ 
                          str (ty_ctr_to_string c) ++ str " for constr: " ++ 
                          str (rocq_constr_to_string class_instance) ++ fnl ()); 
               parsed
        )
      | Some ((_, DTyCtr (ind,_))) -> msg_debug (str "Instance inductive does not match: " ++ 
                                str (ty_ctr_to_string ind) ++ str " =? " ++ 
                                str (ty_ctr_to_string ind_name) ++ fnl ());
                                 parsed
      | None -> msg_debug (str "Failed to parse such that class: " ++ 
                          str (ty_ctr_to_string c) ++ str " for constr: " ++ 
                          str (rocq_constr_to_string class_instance) ++ fnl ()); 
               parsed
      )
    | DArrow (_, t) -> add_class parsed t ind_name
    | DProd (_, t) -> add_class parsed t ind_name
    | _ -> msg_debug (str "Incorrect class Instance structure: " ++ 
                      str (rocq_constr_to_string class_instance) ++ fnl ()); 
             parsed
  in

  let handle_hint hint parsed hint_sort ind_name =
    let typ = type_of_hint hint in
    let env = Global.env () in
    let evd = Evd.from_env env in
    msg_debug (str "Type: " ++ Constr.debug_print typ ++ fnl ());
    msg_debug (str "Type2: " ++ Ppconstr.pr_constr_expr env evd (Constrextern.extern_constr env evd (EConstr.of_constr typ)) ++ fnl ());
    match parse_dependent_type typ with
    | Some rocq -> 
      let rocq_str = rocq_constr_to_string rocq in
      msg_debug (str hint_sort ++ str rocq_str ++ fnl ());
      add_class parsed rocq ind_name
    | None ->
      msg_debug (str hint_sort ++ str " Failed to parse" ++ fnl ());
      parsed
    in

  let init_parsed = {gen = []; enum = []; genST = []; enumST = []; checker = []; decEq = []} in

  let handle_full_hint full_hint parsed =
    (* Feedback.msg_notice (str "Processing Hint: " ++ Hints.FullHint.print env evd full_hint ++ fnl ()); *)
    match Hints.FullHint.repr full_hint with
    | Hints.Res_pf h -> handle_hint h parsed "ResPF" ctr
    | Hints.Give_exact h -> handle_hint h parsed "GiveExact" ctr
    | _ -> (*Feedback.msg_notice (str "Hints.FullHint.repr unrecognized" ++ fnl ()); *)
    parsed
    in

  (* let handle_full_hint b hint =
    msg_debug (str "Processing... (" ++ str typeclass_name ++ str ")"  ++ Hints.FullHint.print env evd hint ++ fnl ());
    begin match Hints.FullHint.repr hint with
    | Hints.Res_pf h ->
      let typ = type_of_hint h in
      let env = Global.env () in
      let evd = Evd.from_env env in
      msg_debug (str "Type: " ++ Constr.debug_print typ ++ fnl ());
      msg_debug (str "Type2: " ++ Ppconstr.pr_constr_expr env evd (Constrextern.extern_constr env evd (EConstr.of_constr typ)) ++ fnl ());
      (match parse_dependent_type typ with
      | Some rocq -> 
        let rocq_str = rocq_constr_to_string rocq in
        msg_debug (str "ResPF: " ++ str rocq_str ++ fnl ());
        
        [rocq] 
      | None ->
        msg_debug (str "ResPF: " ++ str "Failed to parse" ++ fnl ());
        []
      )
    | Hints.Give_exact h ->
      let typ = type_of_hint h in
      let env = Global.env () in
      let evd = Evd.from_env env in
      msg_debug (str "Type: " ++ Constr.debug_print typ ++ fnl ());
      msg_debug (str "Type2: " ++ Ppconstr.pr_constr_expr env evd (Constrextern.extern_constr env evd (EConstr.of_constr typ)) ++ fnl ());
      (match parse_dependent_type typ with
      | Some rocq -> 
        let rocq_str = rocq_constr_to_string rocq in
        msg_debug (str "GiveExact: " ++ str rocq_str ++ fnl ());
        
        [rocq] 
      | None ->
        msg_debug (str "GiveExact: " ++ str "Failed to parse" ++ fnl ());
       [])
    | _ ->
       msg_debug (str "..." ++ fnl ()); []

    end
  in  *)
  let quickchick_prefix_check = function
    | "QuickChick.DependentClasses.GenSizedSuchThat"
    | "QuickChick.DependentClasses.EnumSizedSuchThat" 
    | "QuickChick.Classes.GenSized"
    | "QuickChick.Classes.EnumSized"
    | "QuickChick.Decidability.DecOpt"
    | "QuickChick.Decidability.Dec"
    | "QuickChick.Decidability.Dec_Eq" -> true
    | _ -> false in
  (* Iterate through all of the hints *)
  let parsed_final = Hints.Hint_db.fold (fun go hm hints parsed ->
    begin match go with
    | Some (Names.GlobRef.IndRef i) when quickchick_prefix_check (Names.MutInd.to_string (fst i)) ->
        msg_debug (str "Found a QuickChick hint:" ++ str (Names.MutInd.to_string (fst i)) ++ fnl ());
        List.fold_left (fun acc hint ->
          (* Feedback.msg_notice (str "Processing Hint: " ++ Hints.FullHint.print env evd hint ++ fnl ()); *)
          handle_full_hint hint acc) parsed hints
    | Some (Names.GlobRef.IndRef i) ->
      msg_debug (str "Not a QuickChick hint:" ++ str (Names.MutInd.to_string (fst i)) ++ fnl ());
      parsed
    | _ -> 
      (* List.iter (fun hint -> Feedback.msg_notice (str "Not QuickChick: " ++ Hints.FullHint.print env evd hint ++ fnl ())) hints; *)
      parsed
    end
      (* begin match go with
      | Some (Names.GlobRef.IndRef i) when prod_check i ->
         msg_debug (str "Found a producer hint" ++ str (Names.MutInd.to_string (fst i)) ++ fnl ());
         List.fold_left (fun acc hint -> handle_hint true hint @ acc) acc hints
      | Some (Names.GlobRef.IndRef i) when dec_check i ->
         (* eq hack          if Names.Id.to_string (qualid_basename ctr) = "eq" then result := [[false; false; false]]
         else *) List.fold_left (fun acc hint -> handle_hint false hint @ acc) acc hints
      | _ -> acc
      end *)
    ) db init_parsed
    in 
    print_parsed_classes parsed_final;
    parsed_final
  
(* 
let find_typeclass_bindings' typeclass_name ctr =
  msg_debug (str ("Finding typeclass bindings for:" ^ Libnames.string_of_qualid ctr) ++ fnl());
  let env = Global.env () in
  let evd = Evd.from_env env in
  let db = Hints.searchtable_map "typeclass_instances" in
  let result = ref [] in
  let prod_check i =
    String.equal (Names.MutInd.to_string (fst i)) ("QuickChick.DependentClasses." ^ typeclass_name)  in    
  let dec_check i =
    String.equal (Names.MutInd.to_string (fst i)) ("QuickChick.Decidability." ^ typeclass_name)  in
  let type_of_hint h = 
    (* Go from the hint to the type of its constant *)
    let (_,ec) = Hints.hint_as_term h in
    let c = EConstr.to_constr evd ec in
    match Constr.kind c with
    | Constr.Const cst -> 
      let (typ,_constraints) = Environ.constant_type env cst in
        typ 
    | _ -> failwith ("hint not a constant in search for " ^ Libnames.string_of_qualid ctr)
    in
  (* Find the conclusion of a type *)
  let rec find_concl typ =
    match Constr.kind typ with
    | Constr.Lambda (_binder,_binder_type,typ') -> find_concl typ'
    | Constr.Prod (_binder,_binder_type,typ') -> find_concl typ'
    | Constr.App _ -> typ
    | _ -> failwith ("FindConcl can't handle: " ^ Pp.string_of_ppcmds (Printer.pr_constr_env env evd typ))
  in
  let handle_producer_hint lambda =
    match Constr.kind lambda with
    | Constr.Lambda (_binder,_binder_type,Constr.App (Constr.Ind ((mind,_),_) as cln,clargs)) ->
      msg_debug (str "Entering producer lambda" ++ fnl ());
      msg_debug (str "Found a hint for: " ++ Constr.debug_print cln ++ fnl ());
      let mind_id = Label.to_id (MutInd.label mind) in
      let ctr_id = qualid_basename ctr in
      if Id.equal mind_id ctr_id then begin
        msg_debug (str "Producer Match Found: " ++ Id.print ctr_id ++ fnl ());
        let standard = ref true in
        (* Calculate mode as list of booleans: *)
        let res = 
          List.map (fun arg ->
            if Constr.isMeta arg then
              false (* Check not equal id name *)
            else if Constr.isRef arg then
              false
            (* Bound by the last lambda means it's output *)
            else if Constr.isRelN 1 arg then
              true
            else if Constr.isRel arg then
              false
            else if Constr.isApp arg then
              begin standard := false; true end
            else failwith "New FTB/0"
          ) (Array.to_list clargs) in
        if !standard then begin
            List.iter (fun b -> msg_debug (bool b ++ str " ")) res;
            msg_debug (fnl ());
            result := res :: !result
          end
        else msg_debug (str "not standard/producer" ++ fnl ())
        end 
      else 
        msg_debug (str "Function Applied in the lambda's body not desired ty_ctr: " ++ Id.print ctr_id ++ str " " ++ Id.print mind_id ++ fnl ())
    | Constr.Lambda (_,_,Constr.App _) -> msg_debug (str "First arg is lambda but its body isn't an applied inductive" ++ fnl ())
    | Constr.Lambda _ -> msg_debug (str "First arg is lambda but its body isn't an application at all" ++ fnl ())
    | _ -> msg_debug (str "First arg not lambda" ++ fnl ())
  in
  let handle_checker_hint app =
    if Id.to_string (qualid_basename ctr) = "eq" then ()
    else match Constr.kind app with
    | Constr.App (Constr.Ind ((mind,_),_) as cln,clargs) ->
      let mind_id = Label.to_id (MutInd.label mind) in
      let ctr_id = qualid_basename ctr in
      msg_debug (str "In checker/app for: " ++ Id.print ctr_id ++ str " " ++ Id.print mind_id ++ fnl ());
      if Id.equal mind_id ctr_id then (
        msg_debug (str "Checker Match Found: " ++ Id.print ctr_id ++ fnl ());
        let standard = ref true in
        (* Calculate mode as list of booleans: *)
        (* For checking, mode is alsways false *)
        let res = List.map (fun arg -> 
                      if Constr.isMeta arg then
                        false (* Check not equal id name *)
                      else if Constr.isRef arg then
                        false
                      else if Constr.isRel arg then
                        false
                      else if Constr.isApp arg then
                        begin standard := false; true end
                      else failwith "New FTB/0"
                    ) (Array.to_list clargs) in
        if !standard then begin
            List.iter (fun b -> msg_debug (bool b ++ str " ")) res;
            msg_debug (fnl ());
            result := res :: !result
          end
        else msg_debug (str "not standard/checker" ++ fnl ())
      )
      else
        msg_debug (str "not equal/checker/isApp" ++ fnl ())
    | _ -> msg_debug (str "not an applied inductive" ++ fnl ())
      in

  let handle_checker_hint app = 
    if Id.to_string (qualid_basename ctr) = "eq" then ()
    else if isApp app then (
      msg_debug (str "Entering checker app" ++ fnl ());               
      let (cln, clargs) = Constr.destApp app in               
      (* TODO: Search for Mutual inductives properly *)
      let ((mind,_),_) = Constr.destInd cln in
      let mind_id = Label.to_id (Names.MutInd.label mind) in
      let ctr_id = qualid_basename ctr in
      msg_debug (str "In checker/app for: " ++ Id.print ctr_id ++ str " " ++ Id.print mind_id ++ fnl ());
      
      if Id.equal mind_id ctr_id then (
        msg_debug (str "Checker Match Found: " ++ Id.print ctr_id ++ fnl ());
        let standard = ref true in
        (* Calculate mode as list of booleans: *)
        (* For checking, mode is alsways false *)
        let res = List.map (fun arg -> 
                      if Constr.isMeta arg then
                        false (* Check not equal id name *)
                      else if Constr.isRef arg then
                        false
                      else if Constr.isRel arg then
                        false
                      else if Constr.isApp arg then
                        begin standard := false; true end
                      else failwith "New FTB/0"
                    ) (Array.to_list clargs) in
        if !standard then begin
            List.iter (fun b -> msg_debug (bool b ++ str " ")) res;
            msg_debug (fnl ());
            result := res :: !result
          end
        else msg_debug (str "not standard/checker" ++ fnl ())
      )
      else
        msg_debug (str "not equal/checker/isApp" ++ fnl ());
    )
    else msg_debug (str "not isApp 0" ++ fnl ())
    in
  
  let handle_hint_repr b h =
    let typ = type_of_hint h in
    let (typ_cl, typ_args) = Constr.destApp (find_concl typ) in
    msg_debug (str "Conclusion of current hint is: " ++ fnl ());
    msg_debug (Constr.debug_print (find_concl typ));
    try 
    if b then
      (* For producer, check the second argument (the first is the type of the lambda) *)
      handle_producer_hint typ_args.(1)
    else
      (* For checker, check the first argument. *)
      handle_checker_hint typ_args.(0)
    with _ -> msg_debug (str "exception?" ++ fnl ())
  in
  let handle_hint b hint =
    msg_debug (str "Processing... (" ++ str typeclass_name ++ str ")"  ++ Hints.FullHint.print env evd hint ++ fnl ());
    begin match Hints.FullHint.repr hint with
    | Hints.Res_pf h ->
       handle_hint_repr b h
    | Hints.Give_exact h ->
       handle_hint_repr b h
    (* TODO: Replicate pattern-based behavior from below in constr form *)
    | Hints.Extern (Some (PApp (PRef g, args)), _) ->
    (* begin match Hints.FullHint.pattern hint with
    | Some (PApp (PRef g, args)) -> *)
       begin
         let arg_index = if b then 1 else 0 in 
(*         msg_debug (str ("Hint for :" ^ (string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty g))) ++ fnl ());
         msg_debug (str (Printf.sprintf "Arg Length: %d. Arg index: %d\n" (Array.length args) arg_index) ++ fnl ());*)
         match args.(arg_index) with
         | PLambda (name, t, PApp (PRef gctr, res_args)) ->
            let gctr_qualid = Nametab.shortest_qualid_of_global Id.Set.empty gctr in
            if qualid_eq gctr_qualid ctr then begin
                msg_debug (str "Found a match!" ++ fnl ());
                msg_debug (str ("Conclusion is Application of:" ^
                                  (Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty gctr)))
                           ++ fnl ());
                let standard = ref true in
                let res = List.map (fun p ->
                              match p with
                              | PMeta (Some id) ->
                                 if not (Name.equal (Name id) name)
                                 then false
                                 else failwith "FTB/How is this true"
                              | PRef _ -> false 
                              | PRel _ -> true
                              | PApp _ -> standard := false; true                                        
                              | _ -> debug_pattern "FTB/0" p
                            ) (Array.to_list res_args) in
                if !standard then 
                  result := res :: !result
                else ()
              end
            else ()
         | PApp (PRef gctr, res_args) ->
            let gctr_qualid = Nametab.shortest_qualid_of_global Id.Set.empty gctr in
            if qualid_eq gctr_qualid ctr then begin
                msg_debug (str "Found a match!" ++ fnl ());
                msg_debug (str ("Conclusion is Application of:" ^
                                  (Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty gctr)))
                           ++ fnl ());
                let standard = ref true in
                let res = List.map (fun p ->
                              match p with
                              | PMeta (Some id) -> false
                              | PRef _ -> false 
                              | PRel _ -> true
                              | PApp _ -> standard := false; true                                        
                              | _ -> debug_pattern "FTB/00" p
                            ) (Array.to_list res_args) in
                if !standard then 
                  result := res :: !result
                else ()
              end
            else ()
         | PLambda (name, t, PCase (_, arr, _, [n, ns, PApp (PRef gctr, res_args)])) ->
            let gctr_qualid = Nametab.shortest_qualid_of_global Id.Set.empty gctr in
            if qualid_eq gctr_qualid ctr then begin
                msg_debug (str "Found a match!" ++ fnl ());
                msg_debug (str ("Conclusion is Application of:" ^
                                  (Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty gctr)))
                           ++ fnl ());
                let standard = ref true in
                let res = List.map (fun p ->
                              match p with
                              | PMeta (Some id) -> false 
(*                                 if not (Name.equal (Name id) name)
                                 then false
                                 else failwith "FTB/How is this true" *)
                              | PRef _ -> false 
                              | PRel _ -> true
                              | PApp _ -> standard := false; true                                        
                              | _ -> debug_pattern "FTB/0" p
                            ) (Array.to_list res_args) in
                if !standard then 
                  result := res :: !result
                else ()
              end
            else ()
         | PMeta (Some id) -> () (* failwith (Id.to_string id) *)
         | PProd _ -> ()
         | _ -> debug_pattern "FTB/1" args.(arg_index)
       end
    | Hints.Extern _ -> failwith "FTB/Apply"      
    | Hints.ERes_pf _ -> failwith "FTB/EApply"
    | Hints.Res_pf_THEN_trivial_fail _ -> failwith "FTB/Imm"
    | Hints.Unfold_nth _ -> failwith "FTB/Unf"
    end in
  Hints.Hint_db.iter (fun go hm hints ->
      begin match go with
      | Some (GlobRef.IndRef i) when prod_check i ->
         List.iter (handle_hint true ) hints
      | Some (GlobRef.IndRef i) when dec_check i ->
         if Id.to_string (qualid_basename ctr) = "eq" then result := [[false; false; false]]
         else List.iter (handle_hint false) hints
      | _ -> ()
      end
    ) db;
    !result *)

(* type bindings_and_unbound = binding list * rocq_constr list  *)
type relation_variables = (int * var list) list
type var_uses_in_relations = (var * (int * int list list) list) list
type rocq_constr_var_map_views = relation_variables * var_uses_in_relations


let list_pair_with_rest l =
  let rec aux before current =
    match current with
    | [] -> []
    | now :: after -> ((List.rev before) @ after, now) :: aux (now :: before) after in
  aux [] l


let rec list_bind (l : 'a list) (f : 'a -> 'b list) : 'b list =
  match l with
  | [] -> []
  | x :: xs -> f x @ list_bind xs f

let (>>=:) = list_bind

let para_list_bind (l : 'a list) (f : 'a -> 'a list -> 'b list) : 'b list =
  let rec aux before l =
    match l with
    | [] -> []
    | now :: after -> f now (List.rev before @ after) @ aux (now :: before) after in
  aux [] l

let (>>=*) = para_list_bind 

let list_bindi (l : 'a list) (f : int -> 'a -> 'b list) : 'b list =
  let rec aux i l =
    match l with
    | [] -> []
    | now :: after -> (f i now) @ aux (i + 1) after in
  aux 0 l

let (>>=:+) = list_bindi 

let guard (b : bool) : unit list =
  if b then [()] else []

let (>>:) (l : 'a list) (next : 'b list) : 'b list =
  l >>=: (fun _ -> next)

let possible_schedules (variables : (var * rocq_type) list) (hypotheses : rocq_constr list) (fixed : var list) (rec_call : ty_ctr * int list) (ds : derive_sort) : schedule_step list list =
  (* Feedback.msg_debug (str (ty_ctr_to_string (fst rec_call)) ++ str " " ++ str (String.concat " " (List.map string_of_int (snd rec_call))) ++ fnl ()); *)
  let rec hyp_polarity (h : rocq_constr) : rocq_constr * bool =
    match h with
    | DNot h -> let (h', p) = hyp_polarity h in (h', not p)
    | DTyCtr (ind, args) -> (DTyCtr (ind, args), true)
    | _ -> failwith @@ "Hypothesis is not a type constructor 0" ^ rocq_constr_to_string h in

  let hypothesis_variables = List.map (fun h -> 
    let (h, p) = hyp_polarity h in
    (h, variables_in_hypothesis h, p)) hypotheses in
  let sorted_hypotheses = List.sort (fun (_,v1,_) (_,v2,_) -> compare (List.length v1) (List.length v2)) hypothesis_variables in

  let is_rec_call (binding : var list) (h : rocq_constr) : bool =
    match h with
    | DTyCtr (ind, args) -> 
      let output_pos = filter_mapi (fun i arg ->
        let variables = variables_in_hypothesis arg in
        if variables = [] then None else (*If the argument is filled with a constant, like 0, its not an output.*)
        if List.for_all (fun v -> List.mem v binding) variables then Some i else
        if List.exists (fun v -> List.mem v binding) variables then failwith "Hypothesis arguments cannot have both fixed and yet-to-be-bound variables" 
        else None) args in
    
      ty_ctr_eq ind (fst rec_call) && List.sort compare (snd rec_call) = List.sort compare output_pos
    | _ -> failwith @@ "Hypothesis is not a type constructor 1" ^ rocq_constr_to_string h in

  let collect_check_steps (bound_vars : var list) (checked_hypotheses : int list) (sorted_hypotheses : (rocq_constr * var list * bool) list) : (int * (source * bool)) list =
    filter_mapi (fun i (h, vs, polarity) -> 
      if not (List.mem i checked_hypotheses) && List.for_all (fun v -> List.mem v bound_vars) vs then 
        let src = if ds = D_Check && snd rec_call = [] then
          (match h with
          | DTyCtr (ind, args) when ty_ctr_eq (fst rec_call) ind -> SrcRec (var_of_string "rec", args)
          | DTyCtr (ind, args) -> SrcNonrec h
          | _ -> failwith @@ "Hypothesis is not a type constructor 2" ^ rocq_constr_to_string h) 
        else SrcNonrec h in
        Some (i, (src, polarity)) 
      else None) sorted_hypotheses 
  in

  let prod_sort = (match ds with
  | D_Check | D_Enum -> PS_E
  | D_Gen | D_Thm -> PS_G) in

  let rec split3 = function
    | [] -> ([], [], [])
    | (a,b,c) :: xs -> let (as', bs', cs') = split3 xs in (a :: as', b :: bs', c :: cs') in
    

  let outputs_inputs_not_under_same_constructor (hyp : rocq_constr) (output_vars : var list) : bool =
    match hyp with
    | DTyCtr (ind, args) ->
      (* Feedback.msg_notice (str "Checking if outputs and inputs are not under the same constructor of " ++ str (ty_ctr_to_string ind) ++ fnl ()); *)
      not @@ List.exists (fun arg ->
        let variables = variables_in_hypothesis arg in 
        List.exists (fun v -> List.mem v output_vars) variables && List.exists (fun v -> not (List.mem v output_vars)) variables) args
    | _ -> failwith @@ "Hypothesis is not a type constructor 3" ^ rocq_constr_to_string hyp in

  let outputs_not_constrained_by_function_application (hyp : rocq_constr) (output_vars : var list) : bool =
    match hyp with
    | DTyCtr (ind, args) ->
      not @@ List.exists (fun arg ->
        let rec check b arg =
          match arg with
          | DCtr (ctr_name, args) -> List.exists (check b) args
          | DTyCtr (ind, args) -> List.exists (check b) args
          | DApp (_, args) -> List.exists (check true) args
          | DTyVar v when b -> List.mem v output_vars
          | _ -> false in
        check false arg) args
    | _ -> failwith @@ "Hypothesis is not a type constructor 3" ^ rocq_constr_to_string hyp in
 

  let handle_constrained_outputs hyp output_vars : schedule_step list * rocq_constr * var list =
    match hyp with
    | DTyCtr (ind, args) ->
      let (matches, args', new_outputs) = split3 (List.map (fun arg -> 
        let variables = variables_in_hypothesis arg in
        match arg with
        | DCtr (ctr_name,_) when variables <> [] && List.for_all (fun v -> List.mem v output_vars) variables -> 
          let new_name = make_up_name_str ("v" ^ String.concat "_" (List.map var_to_string variables)) in
          let new_match = S_Match (new_name, rocq_constr_to_pat arg) in
          (Some new_match, DTyVar new_name, Some new_name)
        | DTyVar v when List.mem v output_vars -> (None, arg, Some v)
        | _ -> (None, arg, None)
        ) args) in
      (List.filter_map (fun x -> x) matches, DTyCtr (ind, args'), List.filter_map (fun x -> x) new_outputs)
    | _ -> failwith @@ "Hypothesis is not a type constructor 4" ^ rocq_constr_to_string hyp in

  let normalize_schedule (steps : schedule_step list) : schedule_step list =
    let rec normalize steps u_block =
      match steps with
      | [] -> List.sort compare u_block
      | S_UC (v, src, ps) :: steps -> normalize steps (S_UC (v, src, ps) :: u_block)
      | step :: steps -> List.sort compare u_block @ step :: normalize steps [] in
    normalize steps []
    in 

  let rec dfs (bound_vars : var list) (remaining_vars : var list) 
              (checked_hypotheses : int list) (schedule_so_far : schedule_step list)
              : schedule_step list list =
    (* msg_debug (str "Bound Vars: " ++ str (String.concat ", " (List.map var_to_string bound_vars)) ++ fnl ());
    msg_debug (str "Remaining Vars: " ++ str (String.concat ", " (List.map var_to_string remaining_vars)) ++ fnl ()); *)
    begin match remaining_vars with
    | [] -> [List.rev schedule_so_far]
    | _ ->
      let unconstrained_prod_paths = remaining_vars >>=* (fun v remaining_vars' ->
        let (new_checked_idxs,new_checked_hyps) = List.split @@ collect_check_steps (v :: bound_vars) checked_hypotheses sorted_hypotheses in
        let ty = try List.assoc v variables with Not_found -> failwith "How? All variables start typed" in
        let src = 
          (match ty with
          | DTyCtr (ind, args) when ty_ctr_eq ind (fst rec_call) -> SrcRec (var_of_string "rec", args)
          | DTyCtr (ind, args) -> SrcNonrec ty
          | DTyParam param -> SrcNonrec ty
          (* | DTyParam param -> SrcNonrec ty TODO: Will need to add a typeclass constraint for this *)
          | _ -> failwith ("Variable type is not a type constructor: " ^ rocq_constr_to_string ty ^ " " ^ (ty_ctr_to_string (fst rec_call)))) in
        let unconstrained_prod_step = S_UC (v, src, prod_sort) in
        let checks = List.rev @@ List.map (fun (src,pol) -> S_Check (src,pol)) new_checked_hyps in
        dfs (v :: bound_vars) remaining_vars' (new_checked_idxs @ checked_hypotheses) (checks @ unconstrained_prod_step :: schedule_so_far))
      in
      let remaining_hypotheses = filter_mapi (fun i hyp -> if List.mem i checked_hypotheses then None else Some (i, hyp)) sorted_hypotheses in
      (* msg_debug (str "Remaining Hypotheses: " ++ str (String.concat ", " (List.map (fun (i, h) -> string_of_int i) remaining_hypotheses)) ++ fnl ()); *)
      let constrained_prod_paths = remaining_hypotheses >>=: (fun (i, (hyp, hyp_vars, pol)) ->
        guard pol >>=: fun _ -> (* Negated hypotheses cannot be generated such that, only checked *)
        guard (not (List.mem i checked_hypotheses)) >>=: fun _ -> 
        let rem_var_set = VS.of_list remaining_vars in
        let hyp_var_set = VS.of_list hyp_vars in
        let output_set = VS.inter rem_var_set hyp_var_set in
        let remaining_vars' = VS.elements @@ VS.diff rem_var_set output_set in
        let output_vars = (VS.elements output_set) in
        guard (output_vars <> []) >>=: fun _ -> ( (*guard should never trigger*)
        guard (outputs_inputs_not_under_same_constructor hyp output_vars) >>=: fun _ -> 
        guard (outputs_not_constrained_by_function_application hyp output_vars) >>=: fun _ ->
        let (new_matches, hyp', new_outputs) = handle_constrained_outputs hyp output_vars in 
        let typed_outputs = List.map (fun v -> (v, try List.assoc v variables with Not_found -> DHole)) new_outputs in
        let constraining_relation = 
          (match hyp' with
          | DTyCtr (ind, args) when is_rec_call output_vars hyp -> (*Should actually check if whole term equal up to alpha and that outputs match and typeclass derived match*)
            let input_args = List.filteri (fun i _ -> not (List.mem i (snd rec_call))) args in
            SrcRec (var_of_string "rec", input_args)
          | DTyCtr (_, _) ->
            SrcNonrec hyp'
          | _ -> failwith @@ "Hypothesis is not a type constructor " ^ rocq_constr_to_string hyp'
          ) in  
        let constrained_prod_step = S_ST (typed_outputs, constraining_relation, prod_sort) in
        let (new_checked_idxs,new_checked_hyps) = List.split @@ collect_check_steps (output_vars @ bound_vars) (i :: checked_hypotheses) sorted_hypotheses in
        let checks = List.rev @@ List.map (fun (src,pol) -> S_Check (src,pol)) new_checked_hyps in
        dfs (output_vars @ bound_vars) remaining_vars' (i :: new_checked_idxs @ checked_hypotheses) (checks @ new_matches @ constrained_prod_step :: schedule_so_far)))
      in 
      (* msg_debug (str "Unconstrained: " ++ int (List.length unconstrained_prod_paths) ++ str " Constrained: " ++ int (List.length constrained_prod_paths) ++ fnl ()); *)
      constrained_prod_paths @ unconstrained_prod_paths

    end
  in
  let remaining_vars = List.filter (fun v -> not (List.mem v fixed)) (List.map fst variables) in
  let (new_checked_idxs, new_checked_hyps) = List.split @@ collect_check_steps fixed [] sorted_hypotheses in
  let first_checks = List.rev @@ List.map (fun (src,pol) -> S_Check (src,pol)) new_checked_hyps in
  let schedules = dfs fixed remaining_vars new_checked_idxs first_checks in
  let schedules_normalized = List.map normalize_schedule schedules in
  let schedules_sorted_deduplicated = List.sort_uniq compare schedules_normalized in
  let schedules_sorted_length = List.sort (fun s1 s2 -> List.length s1 - List.length s2) schedules_sorted_deduplicated in
  (* let compare_checks_then_length (s1 : schedule_step list) (s2 : schedule_step list) : int =
    let count_checks (s : schedule_step list) : int =
      List.length (List.filter (function S_Check _ -> true | _ -> false) s) in
    let checks1 = count_checks s1 in
    let checks2 = count_checks s2 in
    if checks1 = checks2 then List.length s1 - List.length s2 else checks1 - checks2 in
  let schedules_sorted = List.sort compare_checks_then_length schedules in *)
  (*print schedules*)
  schedules_sorted_length


(* typing g e t -> step e e' -> typing g e' t *)

(* (fun '(e,t') -> typing (x :: xs) (Abs t e) (Arrow t t'))

[in : x xs t] [out : e, t']*)

(* typing (x :: xs) (Abs t e) (Arrow t t'), g -> x :: xs; e' -> Abs t e;    
*)
(* Need to use unify from UnifyQC to instantiate the initial maps! *)
(* let specialize_constructor relation_instance conclusion fixed =


let specialize_constructor relation_instance conclusion fixed : rocq_constr * (var * rocq_constr list) list =
  match relation_instance, conclusion with
  | DTyCtr (ctr, args), DTyCtr (ctr', args') when ty_ctr_eq ctr ctr' -> 
    let rec aux arg arg' (vm : pat_map) : rocq_constr * pat_map = 
      match arg, arg' with
      | DTyCtr (c, args), DTyCtr (c', args') when ty_ctr_eq c c' ->
        let args, vm' = List.fold_left2 (fun (args, vm) arg arg' -> 
          let arg, vm' = aux arg arg' vm in
          arg :: args, vm') ([], vm) args args' in
        DTyCtr (c, List.rev args), vm'
      | DTyCtr (c, args), DTyVar v ->  *)


(* Given a type and a *)


let rocq_constr_tuple_of_list xs = tuple_of_list (fun x y -> DCtr (constructor_of_string "Coq.Init.Datatypes.pair", [DHole; DHole; x; y])) xs (Some (DTyCtr (ty_ctr_of_string "Coq.Init.Datatypes.tt",[])))


(* let finalize_schedule schedule_steps concl output_vars umap (ds : derive_sort) (opt : bool) : schedule option =
  match ds with
  | D_Check -> Some (schedule_steps, CheckerSchedule) 
  | D_Theorem -> Some (shchedule_steps, TheoremSchedule concl)
  | D_Gen | D_Enum ->
    sequenceM (evaluate_vars umap) output_vars >>= fun output_values ->
      let producer_type = (match ds with D_Gen -> PS_G | D_Enum -> PS_E | _ -> failwith "impossible") in
      Some (schedule_steps, ProducerSchedule (opt, producer_type, rocq_constr_tuple_of_list output_values)) *)



(*
type range = Ctr of constructor * range list
           | Unknown of unknown
           | Undef of rocq_constr
           | FixedInput
           | Parameter of ty_param
           | RangeHole*)




  
      




          
        



        


(* INVARIANT: ind_vars holds, for each hypothesis inductive, the list of variables used in it that haven't already been bound.*)
(* INVARIANT: var_uses holds, for each variable, a list of pairs (idx,positions), where idx is the index of a hypothesis and positions the list
   of positions inside that inductive (e.g. [[0;1;1];[2]] for a in P (A c (B b a)) c a). The lists only hold the indices of inductives that are 
   (* still available to bind.*)
let rec binding_options' ((ind_vars, var_uses) : rocq_constr_var_map_views) (typed_vars : (var * rocq_type) list) : var_uses_in_relations list =
  if typed_vars = [] then [var_uses] else begin
  let var_to_bind_options = list_pair_with_rest typed_vars in
  let bind_variable_to_relation var ty idx_var_idx_opt : rocq_constr_var_map_views * (var * rocq_constr) list =
    match idx_var_idx_opt with
    | None -> 
        let ind_vars' = List.map (fun (i, vs) -> (i, List.filter (fun v -> v <> var) vs)) ind_vars in
        let var_uses' = (var, []) :: List.remove_assoc var var_uses in
        let typed_vars' = List.remove_assoc var typed_vars in
        ((ind_vars', var_uses'), typed_vars')
    | Some (idx, var_idx) -> 
        let ind_uses : var list = safe_assoc idx ind_vars in
        let ind_uses' = List.filter (fun v -> v <> var) ind_uses in
        let var_uses' = (var, [(idx, var_idx)]) :: (List.map (fun v -> (v,[])) ind_uses') @ (assoc_remove_all_in_set ind_uses var_uses) in
        let typed_vars' = assoc_remove_all_in_set ind_uses typed_vars in
        let ind_vars' = List.map (fun (i, vs) -> (i, List.filter (fun v -> not (List.mem v ind_uses)) vs)) ind_vars in
            ((ind_vars', var_uses'), typed_vars') in
  let bind_variable_to_relations var ty : (rocq_constr_var_map_views * (var * rocq_constr) list) list =
    let uses = None :: List.map (fun x -> Some x) (safe_assoc var var_uses) in
    List.map (fun idx_var_idx_opt -> bind_variable_to_relation var ty idx_var_idx_opt) uses in
  var_to_bind_options >>=: (fun (_,(var,ty)) ->
  bind_variable_to_relations var ty >>=: (fun (dtvm_views, typed_vars) ->
    binding_options' dtvm_views typed_vars)) 
  end *)


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
    ], TheoremSchedule (DTyCtr (ty_ctr "typing'", [DTyVar (var "Gamma"); DTyVar (var "e'"); DTyVar (var "tau")]), true)

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

  (* G -> G_ -> Fixed 
     e1_ -> App e1 e2
            e1 -> Fixed
            e2 -> Fixed
            Match App e1 e2
     t2 -> Arrow t1 t2_ 
    
    
      
  *)

  (* EnumST (fun t1 => typing G_ e1_ (Arrow t1 t2_))*)

(* typing g (Abs t e) (Arrow t t') *)

(* typing G (Abs t1 e) ty

  Inductive typing (G : env) : term -> type -> Prop :=
  | TAbs :
      forall e t1 t2,
        typing (t1 :: G) e t2 ->
        typing G (Abs t1 e) (Arrow t1 t2)

*)


(*Inductive term :=
| Const (n : nat)
| App (f x : term)
| Abs (ty : type) (e : term)
| Id (x : nat)
.*)

  let gen_const_schedule = 
    [
      S_UC (var "n", SrcNonrec (DTyCtr (ty_ctr "nat", [])), PS_G)
    ], ProducerSchedule (false, PS_G, DCtr (ctr "Const", [DTyVar (var "n")]))

  let gen_id_schedule = 
    [
      S_UC (var "x", SrcNonrec (DTyCtr (ty_ctr "nat", [])), PS_G)
    ], ProducerSchedule (false, PS_G, DCtr (ctr "Id", [DTyVar (var "x")]))

  let gen_app_schedule = 
    [
      S_UC (var "f", SrcRec (var "rec",[]), PS_G);
      S_UC (var "x", SrcRec (var "rec",[]), PS_G)
    ], ProducerSchedule (false, PS_G, DCtr (ctr "App", [DTyVar (var "f"); DTyVar (var "x")]))

  let gen_abs_schedule = 
    [
      S_UC (var "ty", SrcNonrec (DTyCtr (ty_ctr "type", [])), PS_G);
      S_UC (var "e", SrcRec (var "rec",[]), PS_G)
    ], ProducerSchedule (false, PS_G, DCtr (ctr "Abs", [DTyVar (var "ty"); DTyVar (var "e")]))

  let gen_term_inductive_schedule : inductive_schedule = 
    "term" , [] , [], [gen_const_schedule, []; gen_id_schedule, []] , [gen_app_schedule, []; gen_abs_schedule, []]
  

  

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
      S_Check (SrcNonrec (DTyCtr (ty_ctr "bind", [_G; _x; _t])), true)
    ], CheckerSchedule

  let check_typing_TConst _G _n =
    [

    ], CheckerSchedule

  let check_typing_TAbs _G _t1 _t1' _t2 _e =
    [
      S_Check (SrcNonrec (DTyCtr ((ty_ctr "eq"), [DTyCtr (ty_ctr "type", []); _t1; _t1'])), true);
      S_Check (SrcRec ((var "rec"),[DCtr (ctr "cons",[DHole; _t1; _G]); _e; _t2]), true)
    ], CheckerSchedule

  let check_typing_TApp _G _e1 _e2 _t2 =
    [
      S_ST ([(var "t1", DTyCtr (ty_ctr "type", []))], SrcNonrec (DTyCtr (ty_ctr "typing", [_G; _e2; DTyVar (var "t1")])), PS_E);
      S_Check (SrcRec ((var "rec"), [_G; _e1; DTyCtr (ty_ctr "Arrow", [DTyVar (var "t1"); _t2])]), true)
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
    ("typing_iii", inputs, [], base_scheds, rec_scheds)


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

  let ind_schd_bind_gen_ioo : inductive_schedule =
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

    ("bind_ioo",inputs, [], base_scheds, rec_scheds)
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
