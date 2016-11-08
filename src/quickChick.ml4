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
open GenericLib

let message = "QuickChick"
let mk_ref s = CRef (Qualid (Loc.ghost, qualid_of_string s), None)

(* Names corresponding to QuickChick's .v files *)
let show = mk_ref "QuickChick.Show.show"
let quickCheck = mk_ref "QuickChick.Test.quickCheck"
let quickCheckWith = mk_ref "QuickChick.Test.quickCheckWith"
let mutateCheck = mk_ref "QuickChick.MutateCheck.mutateCheck"
let mutateCheckWith = mk_ref "QuickChick.MutateCheck.mutateCheckWith"
let mutateCheckMany = mk_ref "QuickChick.MutateCheck.mutateCheckMany"
let mutateCheckManyWith = mk_ref "QuickChick.MutateCheck.mutateCheckManyWith"
let sample = mk_ref "QuickChick.GenLow.GenLow.sample"

(* Locate QuickChick's files *)
(* The computation is delayed because QuickChick's libraries are not available
when the plugin is first loaded. *)
(* For trunk and forthcoming Coq 8.5: *)
let qid = Libnames.make_qualid (DirPath.make [Id.of_string "QuickChick"]) (Id.of_string "QuickChick")
			       (*
let qid = qualid_of_string "QuickChick.QuickChick"
				*)
let path =
  lazy (let (_,_,path) = Library.locate_qualified_library ~warn:false qid in path)
let path = lazy (Filename.dirname (Lazy.force path))

(* Interface with OCaml compiler *)
let temp_dirname = Filename.get_temp_dir_name ()

let link_files = ["quickChickLib.cmx"]

(* TODO: in Coq 8.5, fetch OCaml's path from Coq's configure *)
let ocamlopt = "ocamlopt"
let ocamlc = "ocamlc"

let comp_mli_cmd fn =
  Printf.sprintf "%s -rectypes -I %s %s" ocamlc (Lazy.force path) fn

let comp_ml_cmd fn out =
  let path = Lazy.force path in
  let link_files = List.map (Filename.concat path) link_files in
  let link_files = String.concat " " link_files in
  Printf.sprintf "%s -rectypes -w a -I %s -I %s %s %s -o %s" ocamlopt
    temp_dirname path link_files fn out

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

(** [define c] introduces a fresh constant name for the term [c]. *)
let define c =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let (evd,_) = Typing.type_of env evd c in
  let uctxt = Evd.evar_context_universe_context (Evd.evar_universe_context evd) in
  let fn = fresh_name "quickchick" in
  (* TODO: Maxime - which of the new internal flags should be used here? The names aren't as clear :) *)
  ignore (declare_constant ~internal:InternalTacticRequest fn
      (DefinitionEntry (definition_entry ~univs:uctxt c),
       Decl_kinds.IsDefinition Decl_kinds.Definition));
  fn

(* TODO: clean leftover files *)
let runTest c =
  (** [c] is a constr_expr representing the test to run,
      so we first build a new constr_expr representing
      show c **)
  let c = CApp(Loc.ghost,(None,show), [(c,None)]) in
  (** Build the kernel term from the const_expr *)
  let env = Global.env () in
  let evd = Evd.from_env env in
  let (c,evd) = interp_constr env evd c in
  (** Extract the term and its dependencies *)
  let main = define c in
  let mlf = Filename.temp_file "QuickChick" ".ml" in
  let execn = Filename.chop_extension mlf in
  let mlif = execn ^ ".mli" in
  Flags.silently (full_extraction (Some mlf)) [Ident (Loc.ghost, main)];
  (** Add a main function to get some output *)
  let oc = open_out_gen [Open_append;Open_text] 0o666 mlf in
  Printf.fprintf oc
    "\nlet _ = print_string (QuickChickLib.string_of_coqstring (%s))\n"
    (string_of_id main);
  close_out oc;
  (** Compile the extracted code *)
  (** Extraction sometimes produces ML code that does not implement its interface.
      We circumvent this problem by erasing the interface. **)
  Sys.remove mlif;
  if Sys.command (comp_ml_cmd mlf execn) <> 0 then
    msgerr (str "Could not compile test program" ++ fnl ())
  (** Run the test *)
  else
    (** If we want to print the time spent in tests *)
    let execn = "time " ^ execn in
    if Sys.command execn <> 0 then
      msgerr (str "Could not run test" ++ fnl ())

let run f args =
  let args = List.map (fun x -> (x,None)) args in
  let c = CApp(Loc.ghost, (None,f), args) in
  runTest c

	  (*
let run_with f args p =
  let c = CApp(dummy_loc, (None,f), [(args,None);(p,None)]) in
  runTest c
	   *)

VERNAC COMMAND EXTEND QuickCheck
  | ["QuickCheck" constr(c)] ->     [run quickCheck [c]]
  | ["QuickCheckWith" constr(c1) constr(c2)] ->     [run quickCheckWith [c1;c2]]
END;;

VERNAC COMMAND EXTEND QuickChick
  | ["QuickChick" constr(c)] ->     [run quickCheck [c]]
  | ["QuickChickWith" constr(c1) constr(c2)] ->     [run quickCheckWith [c1;c2]]
END;;

VERNAC COMMAND EXTEND MutateCheck
  | ["MutateCheck" constr(c1) constr(c2)] ->     [run mutateCheck [c1;c2]]
  | ["MutateCheckWith" constr(c1) constr(c2) constr(c3)] ->     [run mutateCheckWith [c1;c2;c3]]
END;;

VERNAC COMMAND EXTEND MutateChick
  | ["MutateChick" constr(c1) constr(c2)] ->     [run mutateCheck [c1;c2]]
  | ["MutateChickWith" constr(c1) constr(c2) constr(c3)] ->     [run mutateCheckWith [c1;c2;c3]]
END;;

VERNAC COMMAND EXTEND MutateCheckMany
  | ["MutateCheckMany" constr(c1) constr(c2)] ->     [run mutateCheckMany [c1;c2]]
  | ["MutateCheckManyWith" constr(c1) constr(c2) constr(c3)] ->     [run mutateCheckMany [c1;c2;c3]]
END;;

VERNAC COMMAND EXTEND MutateChickMany
  | ["MutateChickMany" constr(c1) constr(c2)] ->     [run mutateCheckMany [c1;c2]]
  | ["MutateChickManyWith" constr(c1) constr(c2) constr(c3)] ->     [run mutateCheckMany [c1;c2;c3]]
END;;


VERNAC COMMAND EXTEND Sample
  | ["Sample" constr(c)] -> [run sample [c]]
END;;


(* LEO: Started playing with writing a derive generator plugin *)

let mk_constr (s : string) : Term.constr =
  let mp  = Names.MPfile (Names.make_dirpath [id_of_string "QuickChick"; id_of_string "QuickChick"]) in
  let dp  = Names.empty_dirpath in
  let lab = Names.label_of_id (id_of_string s) in
  Term.mkConst (Names.constant_of_kn (Names.make_kn mp dp lab))

type annotation = Size | Weight of int

(* Number of apps = int denotation. Only for nats! *)
let rec number_of_apps (c : Term.constr) : int =
  if Term.isApp c then
    let (_, cs) = Term.destApp c in
    1 + number_of_apps cs.(0)
  else 0
                                    
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

(* Utils: dl adds a dummy location, mk_c turns ident -> constr_expr *)
let dl x = (dummy_loc, x) 
let mk_c x = CRef (Ident (dl x), None)

let rec is_current_inductive c i = 
  (* i + 1 because of 0-indexing in variable names from List.mapi *)
  if Term.isRelN (i+1) c then true
  else if Term.isApp c then
    (msgerr (str "App" ++ fnl ()); 
     let (c', _) = Term.destApp c in
     is_current_inductive c' i)
  else false 

let mkInt n = CPrim (dummy_loc, Numeral (Bigint.of_int n))

let rec mk_list = function 
  | [] -> mk_ref "nil"
  | x::xs -> mkAppC (mk_ref "cons", [x; mk_list xs])

let rec mk_concat = function 
  | [] -> mk_ref "nil"
  | x::xs -> mkAppC (mk_ref "app", [x; mk_concat xs])

let mkAppExplC (f,l) =
  CAppExpl (dummy_loc, (None, f, None), l)

(* Qualify a name with a number *)
let mk_ni s i = Printf.sprintf "%s%d" s i

type derivable = Show | Arbitrary 

let debug_environ () =
  let env = Global.env () in
  let preEnv = Environ.pre_env env in
  let minds = preEnv.env_globals.env_inductives in
  Mindmap_env.iter (fun k _ -> msgerr (str (MutInd.debug_to_string k) ++ fnl())) minds

let rec replaceNth i x = function
  | [] -> []
  | y::ys -> if i = 0 then x::ys else y::(replaceNth (i-1) x ys)
                          
(* Generic derivation function *)
let derive (cn : derivable) (c : constr_expr) (instance_name : string) =
  match c with 
  | CRef (r,_) -> 
     (* Extract id/string representation - which to use? :/ *)
     let qidl = qualid_of_reference r in

     let env = Global.env () in
     
     let glob_ref = Nametab.global r in
     let ind = Globnames.destIndRef glob_ref in 
     let (mind, _) = ind in

     let mib = Environ.lookup_mind mind env in
     let oib = mib.mind_packets.(0) in

     let (ty_ctr, ty_params, ctrs) =
       match dt_rep_from_mib mib with
       | Some dt -> dt
       | None -> failwith "Not supported type"
     in

     let coqTyCtr = gTyCtr ty_ctr in
     let coqTyParams = List.map gTyParam ty_params in

     let full_dt = gApp coqTyCtr coqTyParams in

     let class_ref = match cn with 
       | Show -> mk_ref "QuickChick.Show.Show"
       | Arbitrary -> mk_ref "QuickChick.Arbitrary.Arbitrary" in

     let class_name = match cn with 
       | Show -> "QuickChick.Show.Show"
       | Arbitrary -> "QuickChick.Arbitrary.Arbitrary" in
     
     let hole = CHole (dummy_loc, None, Misctypes.IntroAnonymous, None) in

     (* Generate typeclass constraints. For each type parameter "A" we need `{_ : <Class Name> A} *)
     let instance_arguments =
       List.concat (List.map (fun tp ->
                              [ gArg ~assumName:tp ~assumImplicit:true ();
                                gArg ~assumType:(gApp (gInject class_name) [tp]) ~assumGeneralized:true ()]
                   ) coqTyParams) in

     (* The instance type *)
     let instance_type = gApp (gInject class_name) [full_dt] in

     (* Given a branch (constructor * types) and the number of type parameters, get constructor information *)
     let extract_branch_info num br = 
       let (ctr_id, ty') = br in
       let (_, ty) = Term.decompose_prod_n num ty' in
       let ctr_pats = 
         if Term.isConst ty then []
         else fst (Term.decompose_prod ty) in
       
       let pat_names, pat_types = List.split (List.rev ctr_pats) in
       
       let pat_ids = List.mapi (fun i pn -> fresh_name (mk_ni "p" i)) pat_names in
       (* Name the patterns: p0, p1, ... *)
       let pats = List.map (fun pid -> 
                            CPatAtom (dummy_loc, Some (Ident (dl (pid))))
                           ) pat_ids in
       (ctr_id, pat_ids, pats, pat_types) 
     in 

     msgerr (str "Success!" ++ fnl ());

     (* Create the instance record. Only need to extend this for extra instances *)
     let instance_record = 
         
       match cn with 
       | Show ->

         (* Create the function body by recursing on the structure of x *)
         let show_body x =

           let branch rec_name (ctr,ty) = 
             let rec branch_aux i = function
               | Arrow (ty1, ty2) -> 
                  let (params, f) = branch_aux (i+1) ty2 in
                  let useRec = match ty1 with 
                    | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
                    | _ -> false in
                  (("p" ^ string_of_int i) :: params,
                   fun (v :: vs) -> str_appends [ gStr "( "
                                                ; gApp (if useRec then gVar rec_name else gInject "show") [gVar v]
                                                ; gStr " )"
                                                ; f vs])
               | _ -> ([], fun _ -> emptyString) in
             let (params, f) = branch_aux 0 ty in 
             (ctr, params, fun vs -> str_appends [gStr (constructor_to_string ctr ^ " "); f vs])
           in 
            
           gRecFunIn "aux" ["x'"] 
                     (fun (aux, [x']) -> gMatch (gVar x') (List.map (branch aux) ctrs))
                     (fun aux -> gApp (gVar aux) [gVar x])
         in 

         let show_fun = gFun ["x"] (fun [x] -> show_body x) in
         gRecord [("show", show_fun)]

       | Arbitrary -> 
          (* Create the function body by recursing on the structure of x *)
          let arb_body = 
            let aux_arb   = fresh_name "aux_arb" in 
            let size  = fresh_name "size" in 
            let size' = fresh_name "size'" in 
            
            let binderList = [LocalRawAssum ([(dummy_loc, Name size)], Default Explicit, mk_ref "nat")] 
            in
       
            let is_base_branch num types = 
              not (List.mem true (List.mapi (fun i t -> is_current_inductive t (i+num)) types)) in

            (* Create a branch based on type information and number of parameters (to be ignored) *)
            let create_for_constructor num br = 
       
              let (ctr_id, pat_ids, pats, pat_types) = extract_branch_info num br in 
              
              let create_for_type i t = 
                if is_current_inductive t (i+num) then
                  (false, fresh_name (mk_ni "p" i), mkAppC (mk_c aux_arb, [mk_c size']))
                else (true, fresh_name (mk_ni "p" i), mk_ref "arbitrary") in

              let arbitraries = List.mapi create_for_type pat_types in

              let rec aux = function
                | [] -> (true , mkAppC (mk_ref "returnGen", [mkAppExplC (Ident (dl ctr_id),
                                                                     coqTyParams @
                                                                     (List.mapi (fun i _ ->  mk_c (fresh_name (mk_ni "p" i))) pats))]
                                       ))
                | (b, n, c)::arbs -> 
                   let (b', crec) = aux arbs in
                   (b && b', mkAppC (mk_ref "bindGen", [c; mkCLambdaN dummy_loc 
                                                                      [LocalRawAssum ([dummy_loc, Name n], Default Explicit, hole)] 
                                                                      crec]))
              in 

              aux arbitraries
            in
            
            let constructor_bodies = List.map (create_for_constructor mib.mind_nparams)
                                              (List.combine (Array.to_list oib.mind_consnames) (Array.to_list oib.mind_nf_lc)) in

            let bases = List.filter (fun x -> let (b, _) = x in b) constructor_bodies in

            msgerr (str (string_of_int (List.length bases)) ++ fnl ());
                      
            let mk_weighted bg = 
              let (b,g) = bg in 
              if b then mkAppC (mk_ref "pair", [mkInt 1; g])
              else mkAppC (mk_ref "pair", [mk_c size; g]) in

            let frequencify lst lst_weighted = 
              match lst with 
              | [] -> failwith "No base case" 
              | [(_, g)] -> g
              | ((_,g)::_) -> mkAppC (mk_ref "frequency", [g; mk_list lst_weighted])
            in 

            let base = frequencify bases (List.map mk_weighted bases) in
            let all  = frequencify constructor_bodies (List.map mk_weighted constructor_bodies) in
       
            (* Create the match on x' *)
            let fix_body = 
               CCases (dummy_loc, Term.RegularStyle, None (* return *), 
                      [(mk_c size, (None, None))] (* single discriminee - no as/in*),
                       [(dummy_loc, [dl [CPatCstr (dummy_loc, Ident (dl (id_of_string "O")), [], [])]], base);
                        (dummy_loc, [dl [CPatCstr (dummy_loc, Ident (dl (id_of_string "S")), [], 
                                                   [CPatAtom (dummy_loc, Some (Ident (dl size')))]
                                                  )]], all)]) in
       
            let fix_dcl = (dl aux_arb, binderList, (None, CStructRec), fix_body, (dl None)) in
            
            (* Package as a let_fix *)
            (* let fix size = ... in sized fix *)
            CLetIn (dummy_loc, dl (Name aux_arb), 
                    G_constr.mk_fix (dummy_loc, true, dl aux_arb, [fix_dcl]),
                    CApp (dummy_loc, (None, mk_c (id_of_string "sized")), [(mk_c aux_arb, None)]))
(*                           [(CApp (dummy_loc, (None, mk_c aux_arb), List.map (fun n -> (mk_c n, None)) param_names), None)]))*)
          in 

          (* Package the body to a function *)
          let arbitrary_decl = arb_body in
           
          (* Shrinking function *)
          let shrink_body x =  

            let create_branch aux_shrink (ctr, ty) = 
       
              let rec branch_aux i = function
                 | Arrow (ty1, ty2) -> 
                    let (params, f) = branch_aux (i+1) ty2 in
                    let isCurrent = match ty1 with 
                      | TyCtr (ty_ctr', _) -> ty_ctr = ty_ctr'
                      | _ -> false in
                    (("p" ^ string_of_int i) :: params,
                     fun allParams (v :: vs) -> 
                       let liftNth = gFun ["shrunk"] 
                                          (fun [shrunk] -> gApp ~explicit:true (gCtr ctr)
                                                                (coqTyParams @ (replaceNth i (gVar shrunk) (List.map gVar allParams)))) in
                       lst_appends ((if isCurrent then
                                      [ gLst (gVar v)
                                      ; gApp (gInject "List.map") [liftNth; gApp (gVar aux_shrink) [gVar v]]
                                      ]
                                    else
                                      [ gApp (gInject "List.map") [liftNth; gApp (gInject "shrink") [gVar v]]]
                                   ) @ [f allParams vs]))
                    
                 | _ -> ([], fun _ _ -> list_nil) in
               let (params, f) = branch_aux 0 ty in 
               (ctr, params, fun vs -> f vs vs)
            in
  
            let aux_shrink_body rec_fun x' = gMatch (gVar x') (List.map (create_branch rec_fun) ctrs) in
     
            gRecFunIn "aux_shrink" ["x'"]
                      (fun (aux_shrink, [x']) -> aux_shrink_body aux_shrink x')
                      (fun aux_shrink -> gApp (gVar aux_shrink) [gVar x])
          in

         let shrink_decl = gFun ["x"] (fun [x] -> shrink_body x) in

         gRecord [("arbitrary", arbitrary_decl); ("shrink", shrink_decl)]

     in 


     (* Declare the instance *)
     ignore (Classes.new_instance true 
                                  instance_arguments 
                                  (( (dummy_loc, (Name (id_of_string instance_name))), None)
                                    , Decl_kinds.Explicit, instance_type) 
                                  (Some (true, instance_record)) (* TODO: true or false? *)
                                  None
            )
  | _ -> msgerr (str "Not an Inductive identifier" ++ fnl ())

VERNAC COMMAND EXTEND DeriveShow
  | ["DeriveShow" constr(c) "as" string(s)] -> [derive Show c s]
END;;

VERNAC COMMAND EXTEND DeriveArbitrary
  | ["DeriveArbitrary" constr(c) "as" string(s)] -> [derive Arbitrary c s]
END;;

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
