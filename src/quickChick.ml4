open Names
open Extract_env

(* Interface with OCaml compiler *)
let comp_mli_cmd fn =
  Printf.sprintf "ocamlc -rectypes -I %s %s" (Filename.get_temp_dir_name ()) fn

let comp_ml_cmd fn out =
  Printf.sprintf "ocamlopt -rectypes -I %s /tmp/camlCoq.cmx %s -o %s" (Filename.get_temp_dir_name ()) fn out

(* Commands are truncated, they do not include the file name on which they *)
(* operate. *)

let cmds main = [
(* TODO: move these functions to a separate file *)
"sed -i '1s/^/let string_of_coqstring (l : char list) =\\\n"^
  "let s = String.create (List.length l) in\\\n"^
  "let rec copy i = function\\\n"^
  "| [] -> s\\\n"^
  "| c :: l -> s.[i] <- c; copy (i+1) l\\\n"^
  "in copy 0 l\\\n\\\n"^

"let coqstring_of_string s =\\\n"^
"  let rec copy acc i =\\\n"^
"    if i < 0 then acc else copy (s.[i] :: acc) (i-1)\\\n"^
"  in copy [] (String.length s - 1)\\\n/'";

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
