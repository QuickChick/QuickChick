open Names
open Extract_env

let ghc_cmd fn modn = Printf.sprintf "ocamlc %s" fn
  
(*   Printf.sprintf "ghc %s -main-is %s" fn modn *)

(* Commands are truncated, they do not include the file name on which they *)
(* operate. *)

let cmds main = [
(*
"sed -i 's/#ifdef __GLASGOW_HASKELL__//'";
"sed -i 's/import qualified GHC.Base//'";
"sed -i 's/#else//'";
"sed -i 's/-- HUGS//'";
"sed -i 's/import qualified IOExts//'";
"sed -i 's/unsafeCoerce = IOExts.unsafeCoerce//'";
"sed -i 's/#endif//'";

"sed -i '1i\
{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}'";

"sed -i 's/^import qualified Prelude/"^
"import qualified Prelude\\\n"^
"import qualified System.Random as SR\\\n"^
"import qualified Debug.Trace as DT\\\n"^
"import qualified Data.Bits as DB\\\n"^
"import qualified Data.Char as DC\\\n"^
"import Text.Show.Functions\\\n"^
"import System.IO.Unsafe\\\n"^
"import qualified Control.DeepSeq as DS\\\n"^
"import qualified GHC.Base/'";

"sed -i 's/import qualified GHC.Base/import qualified GHC.Base\\\n\\\n"^
"deriving instance Prelude.Show Result0/' "; (* FIXME *)
*)
(* The main function should be a MiniML AST *)

"echo \"let main = print_string " ^ main ^ "\" >> "]

let quickcheck c =
  let main = Libnames.string_of_reference c in
  let fn = Filename.temp_file "QuickChick" ".ml" in
  let execn = Filename.chop_extension fn in
  let modn = Filename.basename execn in
  full_extraction (Some fn) [c];
  (* We should check that the commands below succeed at each step *)
  List.iter (fun cmd -> ignore (Sys.command (cmd ^ " " ^ fn))) (cmds main);
  Sys.command (ghc_cmd fn modn);
  let _ = Sys.command execn in ()

VERNAC COMMAND EXTEND QuickCheck
  | ["QuickCheck" global(c)] ->     [quickcheck c]
END;;
