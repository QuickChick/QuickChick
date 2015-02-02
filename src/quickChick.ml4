open Pp
open Names
open Extract_env

(* Locate QuickChick's files *)
(* The computation is delayed because QuickChick's libraries are not available
when the plugin is first loaded. *)
(* For trunk and forthcoming Coq 8.5:
let qid = Libnames.make_qualid (DirPath.make [Id.of_string "QuickChick"]) (Id.of_string "QuickChick")
*)
let qid = Libnames.make_qualid (make_dirpath [id_of_string "QuickChick"]) (id_of_string "QuickChick")
let path =
  lazy (let (_,_,path) = Library.locate_qualified_library false qid in path)
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

(* TODO: clean leftover files *)
let quickcheck c =
  let main = Libnames.string_of_reference c in
  let mlf = Filename.temp_file "QuickChick" ".ml" in
  let execn = Filename.chop_extension mlf in
  let mlif = execn ^ ".mli" in
  let modn = Filename.basename execn in
  Flags.silently (full_extraction (Some mlf)) [c];
  let oc = open_out_gen [Open_append;Open_text] 0o666 mlf in
  Printf.fprintf oc "\nlet _ = print_string (QuickChickLib.string_of_coqstring (%s))\n" main;
  close_out oc;
  (* We should check that the commands below succeed at each step *)
  if Sys.command (comp_mli_cmd mlif) <> 0 then
    msgerr (str "Could not compile test program interface" ++ fnl ())
  else if Sys.command (comp_ml_cmd mlf execn) <> 0 then
    msgerr (str "Could not compile test program" ++ fnl ())
  else if Sys.command execn <> 0 then
    msgerr (str "Could not run test" ++ fnl ())

VERNAC COMMAND EXTEND QuickCheck
  | ["QuickCheck" global(c)] ->     [quickcheck c]
END;;
