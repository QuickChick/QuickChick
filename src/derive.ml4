open Pp
open Loc
open Names
open Extract_env
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
open Decl_kinds
open GenericLib

type derivable = Show | Arbitrary | Size

let list_last l = List.nth l (List.length l - 1)
let list_init l = List.rev (List.tl (List.rev l))
let list_drop_every n l = 
  let rec aux i = function
    | [] -> []
    | x::xs -> if i == n then aux 1 xs else x::aux (i+1) xs
  in aux 1 l
                                      
let print_der = function
  | Show -> "Show"
  | Arbitrary -> "Arbitrary"
  | Size -> "Size"

let debug_environ () =
  let env = Global.env () in
  let preEnv = Environ.pre_env env in
  let minds = preEnv.env_globals.env_inductives in
  Mindmap_env.iter (fun k _ -> msgerr (str (MutInd.debug_to_string k) ++ fnl())) minds

let rec replace v x = function
  | [] -> []
  | y::ys -> if y = v then x::ys else y::(replace v x ys)

(* Generic derivation function *)
let derive (cn : derivable) (c : constr_expr) (instance_name : string) =
  msgerr (str (print_der cn) ++ fnl ());
  let r = match c with
    | CRef (r,_) -> r
    | _ -> failwith "Argument must be typeclass name" in

  (* Extract id/string representation - which to use? :/ *)
  let qidl = qualid_of_reference r in

  let env = Global.env () in
  
  let glob_ref = Nametab.global r in
  let (mind,_) = Globnames.destIndRef glob_ref in
  let mib = Environ.lookup_mind mind env in

  let (ty_ctr, ty_params, ctrs) =
    match dt_rep_from_mib mib with
    | Some dt -> dt
    | None -> failwith "Not supported type"  in

  let coqTyCtr = gTyCtr ty_ctr in
  let coqTyParams = List.map gTyParam ty_params in

  let full_dt = gApp coqTyCtr coqTyParams in

  let class_name = match cn with 
    | Show -> "QuickChick.Show.Show"
    | Size -> "QuickChick.GenLow.GenLow.CanonicalSize"
    | Arbitrary -> "QuickChick.Arbitrary.Arbitrary" in
  
  (* Generate typeclass constraints. For each type parameter "A" we need `{_ : <Class Name> A} *)
  let instance_arguments =
    List.concat (List.map (fun tp ->
                           [ gArg ~assumName:tp ~assumImplicit:true ();
                             gArg ~assumType:(gApp (gInject class_name) [tp]) ~assumGeneralized:true ()]
                          ) coqTyParams) in

  (* The instance type *)
  let instance_type = gApp (gInject class_name) [full_dt] in

  let isCurrentTyCtr = function 
    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
    | _ -> false in

  let isBaseBranch ty = fold_ty' (fun b ty' -> b && not (isCurrentTyCtr ty')) true ty in
  
  (* Create the instance record. Only need to extend this for extra instances *)
  let instance_record iargs = 
    
    match cn with 
    | Show ->

       (* Create the function body by recursing on the structure of x *)
       let show_body x =

         let branch rec_name (ctr,ty) = 
           
           (ctr, generate_names_from_type "p" ty, 
            fun vs -> str_append (gStr (constructor_to_string ctr ^ "  "))
                                 (fold_ty_vars (fun _ v ty' -> str_appends [ gStr "( " 
                                                                           ; gApp (if isCurrentTyCtr ty' then gVar rec_name else gInject "show") [gVar v]
                                                                           ; gStr " )"
                                                                           ])
                                               (fun s1 s2 -> str_appends [s1; gStr " "; s2]) emptyString ty vs))
         in 

         gRecFunIn "aux" ["x'"] 
                   (fun (aux, [x']) -> gMatch (gVar x') (List.map (branch aux) ctrs))
                   (fun aux -> gApp (gVar aux) [gVar x])
       in 

       let show_fun = gFun ["x"] (fun [x] -> show_body x) in
       gRecord [("show", show_fun)]

    | Arbitrary -> 
       msgerr (str "Here" ++ fnl ());
       (* Create the function body by recursing on the structure of x *)
       let arbitrary_decl = 

         (* Need reverse fold for this *)
         let create_for_branch tyParams ps rec_name size (ctr, ty) =
           let rec aux i acc ty : coq_expr =
             match ty with
             | Arrow (ty1, ty2) -> 
                bindGen (if isCurrentTyCtr ty1 then gApp (gVar rec_name) (gVar size :: List.map gVar ps) else gInject "arbitrary")
                        (Printf.sprintf "p%d" i)
                        (fun pi -> aux (i+1) ((gVar pi) :: acc) ty2)
             | _ -> returnGen (gApp ~explicit:true (gCtr ctr) (tyParams @ List.rev acc))
           in aux 0 [] ty in

         let bases = List.filter (fun (_, ty) -> isBaseBranch ty) ctrs in
         let aux_arb =
             let explicitly_typed_arguments =
               List.concat (List.map (fun tp ->
                           [ gArg ~assumName:tp ();
                             gArg ~assumName:(gVar (make_up_name())) ~assumType:(gApp (gInject class_name) [tp]) ()]
                          ) coqTyParams) in

             gRecFunInWithArgs
               "aux_arb" (gArg ~assumName:(gInject "size") () :: explicitly_typed_arguments)
               (fun (aux_arb, size::ps) ->
                let tyParams = List.map gVar (list_drop_every 2 ps) in
                gMatch (gVar size)
                       [(injectCtr "O", [],
                         fun _ -> oneof (List.map (create_for_branch tyParams ps aux_arb size) bases))
                       ;(injectCtr "S", ["size'"], 
                         fun [size'] -> frequency (List.map (fun (ctr,ty') ->
                                                             ((if isBaseBranch ty' then gInt 1 else gVar size),
                                                              create_for_branch tyParams ps aux_arb size' (ctr,ty'))) ctrs))
                       ])
               (fun x -> gVar x) in 

         let fn = defineConstant (instance_name ^ "Sized") aux_arb in
         msgerr (str "Defined" ++ fnl ());

         gApp (gInject "sized") [gFun ["s"] (fun [s] -> gApp (gVar fn) ((gVar s) :: List.map gVar iargs))]
       in                                                                            
       
       (* Shrinking function *)
       let shrink_body x =  
         let create_branch aux_shrink (ctr, ty) = 
           (ctr, generate_names_from_type "p" ty,
            fold_ty_vars (fun allParams v ty' -> 
                          let liftNth = gFun ["shrunk"] 
                                             (fun [shrunk] -> gApp ~explicit:true (gCtr ctr)
                                                                   (coqTyParams @ (replace (gVar v) (gVar shrunk) (List.map gVar allParams)))) in
                          lst_appends (if isCurrentTyCtr ty' then
                                         [ gList [gVar v] ; gApp (gInject "List.map") [liftNth; gApp (gVar aux_shrink) [gVar v]]]
                                       else
                                         [ gApp (gInject "List.map") [liftNth; gApp (gInject "shrink") [gVar v]]]))
                         lst_append list_nil ty) in

         let aux_shrink_body rec_fun x' = gMatch (gVar x') (List.map (create_branch rec_fun) ctrs) in
         
         gRecFunIn "aux_shrink" ["x'"]
                   (fun (aux_shrink, [x']) -> aux_shrink_body aux_shrink x')
                   (fun aux_shrink -> gApp (gVar aux_shrink) [gVar x])
       in

       let shrink_decl = gFun ["x"] (fun [x] -> shrink_body x) in

       gRecord [("arbitrary", arbitrary_decl); ("shrink", shrink_decl)]
    | Size ->
       let sizeOf_body x = 
         let create_branch rec_name (ctr, ty) =
           (ctr, generate_names_from_type "p" ty,
            if isBaseBranch ty then fun _ -> gInt 0 
            else fun vs -> 
                 let opts = fold_ty_vars (fun _ v ty' ->
                                          if isCurrentTyCtr ty' then [Some (gApp (gVar rec_name) [gVar v])]
                                          else [None]) (fun l1 l2 -> l1 @ l2) [] ty vs in
                 gApp (gInject "S") [maximum (cat_maybes opts)]) in
         
         gRecFunIn "aux_size" ["x'"] 
                   (fun (aux_size, [x']) -> gMatch (gVar x') (List.map (create_branch aux_size) ctrs))
                   (fun aux_size -> gApp (gVar aux_size) [gVar x]) in
       let sizeOf_decl = gFun ["x"] (fun [x] -> sizeOf_body x) in
       gRecord [("sizeOf", sizeOf_decl)]
  in 

  declare_class_instance instance_arguments instance_name instance_type instance_record

VERNAC COMMAND EXTEND DeriveShow
  | ["DeriveShow" constr(c) "as" string(s)] -> [derive Show c s]
END;;

VERNAC COMMAND EXTEND DeriveArbitrary
  | ["DeriveArbitrary" constr(c) "as" string(s)] -> [derive Arbitrary c s]
END;;

VERNAC COMMAND EXTEND DeriveSize
  | ["DeriveSize" constr(c) "as" string(s)] -> [derive Size c s]
END;;


(* Advanced Generators *)

(* Unknowns are strings *)
type unknown = string

(* Ranges are undefined, unknowns or constructors applied to ranges *)
type range = Ctr of constructor * range list | Unknown of unknown | Undef | FixedInput

module UM = Map.Make(String)
         
type umap = range UM.t 

let lookup k m = try Some (UM.find k m) with Not_found -> None

let (>>=) (m : 'a option) (f : 'a -> 'b option) : 'b option = 
  match m with 
  | Some a -> f a 
  | None -> None 

let fold_opt (f : 'b -> 'a -> 'b option) (b : 'b) (xs : 'a list) : 'b option = 
  let f' x k z = f z x >>= k in
  List.fold_right f' xs (fun x -> Some x) b

(* I NEED AN OPTION MONAD *)
let rec unify (k : umap) (r1 : range) (r2 : range) : (umap * range) option = 
  match r1, r2 with 
  | Unknown u, FixedInput
  | FixedInput, Unknown u -> 
     begin match lookup u k with 
     | Some r -> 
        begin match unify k r FixedInput with
        | Some (k', r') -> Some (UM.add u r' k', Unknown u)
        | None -> None
        end
     | None -> Some (UM.add u FixedInput k, Unknown u)
     end
  | Unknown u1, Unknown u2 -> 
     if u1 == u2 then Some (k, Unknown u1)
     else let (u1', u2') = if u1 < u2 then (u1, u2) else (u2, u1) in
          begin match lookup u1 k, lookup u2 k with 
          | Some r1, Some r2 -> 
             begin match unify k r1 r2 with 
             | Some (k', r') -> Some (UM.add u1' (Unknown u2') (UM.add u2' r' k'), Unknown u1')
             | None -> None
             end
          | Some r, None  
          | None, Some r -> Some (UM.add u1' (Unknown u2') (UM.add u2' r k), Unknown u1')
(*           | None, None -> None - LEO: Should be an error case - commenting out to see if it happens *)
          end
  | Ctr (c1, rs1), Ctr (c2, rs2) -> 
     if c1 == c2 then 
       begin match fold_opt (fun b a -> let (r1, r2) = a in 
                               let (k, l) = b in 
                               unify k r1 r2 >>= fun b' -> 
                               let (k', r') = b' in 
                               Some (k', r'::l)
                            ) (k , []) (List.combine rs1 rs2) with
       | Some (k', rs) -> Some (k', Ctr (c1, List.rev rs))
       | None -> None
       end
     else None
  | _, _ -> None

(*
type annotation = Size | Weight of int

(* Try to see if a constr represents a _W or _Size annotation *)     
let get_annotation (c : Term.constr) : annotation option =
  if Term.eq_constr c (mk_constr "_Size") then Some Size 
  else if Term.isApp c then
    let (c', cs) = Term.destApp c in
    if Term.eq_constr c' (mk_constr "_W") then
      Some (Weight number_of_apps cs.(0))
    else None    
  else None
                                     
let rec strip_prod_aux (l : (Names.name * Term.constr) list) (t : Term.types) : (annotation * Term.types) =
  let ([(n,c)], t) = Term.decompose_prod_n 1 t in
  match get_annotation c with
  | Some Size -> (Size, Term.compose_prod l (Vars.lift (-1) t))
  | Some (Weight n) -> (Weight n, Term.compose_prod l (Vars.lift (-1) t))
  | None -> strip_prod_aux ((n,c)::l) t

let strip_prod (t : Term.types) : (annotation * Term.types) =
  strip_prod_aux [] t

let get_user_arity (i : Declarations.inductive_arity) : Term.constr =
  match i with
  | RegularArity ra -> ra.mind_user_arity
(* Template arity? *)

let strip_last_char (s : string) : string =
  String.sub s 0 (String.length s - 1)

                                        
let deriveGenerators c mind_name gen_name = 
  match c with
  | CRef (r,_) ->

     let env = Global.env () in
     
     let glob_ref = Nametab.global r in
     let ind = Globnames.destIndRef glob_ref in 
     let (mind, _) = ind in

     let mib = Environ.lookup_mind mind env in
     let oib = mib.mind_packets.(0) in
     
     let strippedPair = List.map strip_prod (Array.to_list oib.mind_nf_lc) in
     
     (* Create the new inductive entries *)
     let oie = { mind_entry_typename  = id_of_string mind_name ;
                 mind_entry_arity     = get_user_arity oib.mind_arity ; 
                 mind_entry_template  = false; (* LEO: not sure about this *)
                 mind_entry_consnames = List.map (fun i -> id_of_string (strip_last_char (string_of_id i))) (Array.to_list oib.mind_consnames) ;
                 mind_entry_lc = List.map snd strippedPair ;
               } in
     let mie = { mind_entry_record = None ; (* LEO: not a record *)
                 mind_entry_finite = mib.mind_finite ;
                 mind_entry_params = [] ;
                 mind_entry_inds   = [oie] ;             (* TODO: This currently works for non mutually recursive! *)
                 mind_entry_polymorphic = mib.mind_polymorphic ;
                 mind_entry_universes = mib.mind_universes ;
                 mind_entry_private = mib.mind_private ;
               } in

     (* Declare the mutual inductive *)
     ignore (declare_mind mie);

(*
     (* Construct kernel term closure *)
     let env = Global.env () in
     let evd = Evd.empty in
     let mk_kernel c = interp_constr evd env c in

     (* Helpers for return/bind in the Gen monad *)
     let returnGen c = 
       (* Not clear why this doesn't want a "QuickChick" qualifier... *)
       CApp (dummy_loc, (None, mk_ref "GenLow.returnGen"), [(c, None)]) in
     let mkEx p x pf = 
       CApp (dummy_loc, (None, mk_ref "exist"), [(p, None); (x, None); (pf, None)]) in

     ()
 *)
(*
     (* Start creating the generator *) 
     let const_body = mk_kernel (
       (* For the fixpoint "aux", structural recursion on "size" *)
       let aux  = fresh_name "aux" in 
       let size = fresh_name "size" in 
       let binderList = [LocalRawAssum ([(dummy_loc, Name size)], Default Explicit, mk_ref "nat")] in 

       let base = returnGen (mkEx (mk_ref "goodFoo") (mk_ref "Foo1") (mk_ref "Good1")) in

       let fix_body = 
         CCases (dummy_loc, Term.RegularStyle, None,
                 [(mk_c size, (None, None))],
                 [(dummy_loc, [dl [CPatCstr (dummy_loc, Ident (dl (id_of_string "O")), [])]], base);
                  (dummy_loc, [dl [CPatCstr (dummy_loc, Ident (dl (id_of_string "S")), [CPatAtom (dummy_loc, None)])]], base)]) in

       let fix_dcl = (dl aux, binderList, (None, CStructRec), fix_body, (dl None)) in

       G_constr.mk_fix (dummy_loc, true, dl aux, [fix_dcl]) 
     ) in

     (* Define the new constant *)
     ignore (
         declare_constant ~internal:KernelVerbose (id_of_string sg)
         (DefinitionEntry {
              const_entry_body = const_body;
              const_entry_secctx = None;
              const_entry_type = None;
              const_entry_opaque = false
            },
          Decl_kinds.IsDefinition Decl_kinds.Definition)
       )
 *)
  | _ -> msgerr (str "Not a valid identifier" ++ fnl ())

VERNAC COMMAND EXTEND DeriveGenerators
  | ["DeriveGenerators" constr(c) "as" string(s1) "and" string(s2)] -> [deriveGenerators c s1 s2]
END;;                                       
 *)
