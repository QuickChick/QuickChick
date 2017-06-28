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
open Error
open Constrarg

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

let comp_ml_cmd fn out =
  let path = Lazy.force path in
  let link_files = List.map (Filename.concat path) link_files in
  let link_files = String.concat " " link_files in
  Printf.sprintf "%s -rectypes -w a -I %s -I %s %s %s -o %s" ocamlopt
    temp_dirname path link_files fn out

(* 
let comp_mli_cmd fn =
  Printf.sprintf "%s -rectypes -I %s %s" ocamlc (Lazy.force path) fn
 *)

let comp_mli_cmd fn =
  let path = Lazy.force path in
  let link_files = List.map (Filename.concat path) link_files in
  let link_files = String.concat " " link_files in
  Printf.sprintf "%s -rectypes -w a -I %s -I %s %s %s" ocamlopt
    temp_dirname path link_files fn


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
  Flags.silently (Extraction_plugin.Extract_env.full_extraction (Some mlf)) [Ident (Loc.ghost, main)]; 
  (** Add a main function to get some output *)
  let oc = open_out_gen [Open_append;Open_text] 0o666 mlf in
  Printf.fprintf oc
    "\nlet _ = print_string (QuickChickLib.string_of_coqstring (%s))\n"
    (string_of_id main);
  close_out oc;
  (* Before compiling, remove stupid cyclic dependencies like "type int = int".
     TODO: Generalize (.) \g1\b or something *)
  let perl_cmd = "perl -i -p0e 's/type int =\\s*int/type tmptmptmp = int\\ntype int = tmptmptmp/s' " ^ mlf in
  if Sys.command perl_cmd <> 0 then msg_error (str ("perl script hack failed. Report: " ^ perl_cmd)  ++ fnl ());
  (** Compile the extracted code *)
  (** Extraction sometimes produces ML code that does not implement its interface.
      We circumvent this problem by erasing the interface. **)
  Sys.remove mlif;
  (* TODO: Maxime, thoughts? *)
  (** LEO: However, sometimes the inferred types are too abstract. So we touch the .mli to close the weak types. **)
  Sys.command ("touch " ^ mlif);
  (* 
  Printf.printf "Extracted ML file: %s\n" mlf;
  Printf.printf "Compile command: %s\n" (comp_ml_cmd mlf execn);
  flush_all ();
  *) 
  (* Compile the (empty) .mli *)
  if Sys.command (comp_mli_cmd mlif) <> 0 then msg_error (str "Could not compile mli file" ++ fnl ());
  if Sys.command (comp_ml_cmd mlf execn) <> 0 then
    msg_error (str "Could not compile test program" ++ fnl ())
  (** Run the test *)
  else
    (** If we want to print the time spent in tests *)
    (* let execn = "time " ^ execn in *)
    if Sys.command execn <> 0 then
      msg_error (str "Could not run test" ++ fnl ())

let run f args =
  begin match args with 
  | qc_text :: _ -> Printf.printf "QuickChecking %s\n" 
                      (Pp.string_of_ppcmds (Ppconstr.pr_constr_expr qc_text));
                      flush_all()
  | _ -> failwith "run called with no arguments"
  end;
  let args = List.map (fun x -> (x,None)) args in
  let c = CApp(Loc.ghost, (None,f), args) in
  runTest c

let setFlags s1 s2 = 
  let toggle = 
    match s2 with 
    | "On"  -> true
    | "Off" -> false in
  begin match s1 with 
  | "Debug" -> flag_debug := toggle
  | "Warn"  -> flag_warn  := toggle
  | "Error" -> flag_error := toggle    
  end

	  (*
let run_with f args p =
  let c = CApp(dummy_loc, (None,f), [(args,None);(p,None)]) in
  runTest c
	   *)

VERNAC COMMAND EXTEND QuickCheck CLASSIFIED AS SIDEFF
  | ["QuickCheck" constr(c)] ->     [run quickCheck [c]]
  | ["QuickCheckWith" constr(c1) constr(c2)] ->     [run quickCheckWith [c1;c2]]
END;;

VERNAC COMMAND EXTEND QuickChick CLASSIFIED AS SIDEFF
  | ["QuickChick" constr(c)] ->     [run quickCheck [c]]
  | ["QuickChickWith" constr(c1) constr(c2)] ->     [run quickCheckWith [c1;c2]]
END;;

VERNAC COMMAND EXTEND MutateCheck CLASSIFIED AS SIDEFF
  | ["MutateCheck" constr(c1) constr(c2)] ->     [run mutateCheck [c1;c2]]
  | ["MutateCheckWith" constr(c1) constr(c2) constr(c3)] ->     [run mutateCheckWith [c1;c2;c3]]
END;;

VERNAC COMMAND EXTEND MutateChick CLASSIFIED AS SIDEFF
  | ["MutateChick" constr(c1) constr(c2)] ->     [run mutateCheck [c1;c2]]
  | ["MutateChickWith" constr(c1) constr(c2) constr(c3)] ->     [run mutateCheckWith [c1;c2;c3]]
END;;

VERNAC COMMAND EXTEND MutateCheckMany CLASSIFIED AS SIDEFF
  | ["MutateCheckMany" constr(c1) constr(c2)] ->     [run mutateCheckMany [c1;c2]]
  | ["MutateCheckManyWith" constr(c1) constr(c2) constr(c3)] ->     [run mutateCheckMany [c1;c2;c3]]
END;;

VERNAC COMMAND EXTEND MutateChickMany CLASSIFIED AS SIDEFF
  | ["MutateChickMany" constr(c1) constr(c2)] ->     [run mutateCheckMany [c1;c2]]
  | ["MutateChickManyWith" constr(c1) constr(c2) constr(c3)] ->     [run mutateCheckMany [c1;c2;c3]]
END;;

VERNAC COMMAND EXTEND QuickChickDebug CLASSIFIED AS SIDEFF
  | ["QuickChickDebug" ident(s1) ident(s2)] -> [setFlags (Names.string_of_id s1) (Names.string_of_id s2)]
END;;

VERNAC COMMAND EXTEND Sample CLASSIFIED AS SIDEFF
  | ["Sample" constr(c)] -> [run sample [c]]
END;;


