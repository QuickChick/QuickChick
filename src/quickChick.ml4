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

let comp_mli_cmd fn =
  Printf.sprintf "ocamlc -rectypes -I %s %s" (Lazy.force path) fn

let comp_ml_cmd fn out =
  let path = Lazy.force path in
  let link_files = List.map (Filename.concat path) link_files in
  let link_files = String.concat " " link_files in
  Printf.sprintf "ocamlopt -rectypes -I %s -I %s %s %s -o %s" temp_dirname 
    path link_files fn out

(* Commands are truncated, they do not include the file name on which they *)
(* operate. *)

let cmds main = [
"sed -i '1s/^/open QuickChickLib\\\n/'";
(*
  "let s = String.create (List.length l) in\\\n"^
  "let rec copy i = function\\\n"^
  "| [] -> s\\\n"^
  "| c :: l -> s.[i] <- c; copy (i+1) l\\\n"^
  "in copy 0 l\\\n\\\n"^

"let coqstring_of_string s =\\\n"^
"  let rec copy acc i =\\\n"^
"    if i < 0 then acc else copy (s.[i] :: acc) (i-1)\\\n"^
"  in copy [] (String.length s - 1)\\\n/'";
*)
(* The main function should be a MiniML AST *)

"echo \"let main = print_string (string_of_coqstring (" ^ main ^ "))\" >> "]

let quickcheck c =
  let main = Libnames.string_of_reference c in
  let mlf = Filename.temp_file "QuickChick" ".ml" in
  let execn = Filename.chop_extension mlf in
  let mlif = execn ^ ".mli" in
  let modn = Filename.basename execn in
  full_extraction (Some mlf) [c];
  (* We should check that the commands below succeed at each step *)
  List.iter (fun cmd -> ignore (Sys.command (cmd ^ " " ^ mlf))) (cmds main);
  Sys.command (comp_mli_cmd mlif);
  Sys.command (comp_ml_cmd mlf execn);
  let _ = Sys.command execn in ()

VERNAC COMMAND EXTEND QuickCheck
  | ["QuickCheck" global(c)] ->     [quickcheck c]
END;;
