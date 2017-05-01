{
open Lexing
open QuickChickToolParser
open QuickChickToolTypes

}

let white    = [' ' '\t' '\r' '\n']
let nonwhite = [^ ' ' '\t' '\r' '\n']

(* Main Parsing match *)
rule lexer = parse
  (* Skip initial whitespace *)
  | white+ as s  { T_White s }
    
  | "(*! Section"     { T_StartSec }
  | "(*! QuickChick"  { T_StartQC  }
  | "(*!\nQuickChick" { T_StartQC  }
  | "(*! *)"          { T_StartMutant }
  | "(*!"             { T_StartMutantVariant }

  (* Regular comments need to be handled to play with termination specials *)
  | "(*"         { nested_comment 0 lexbuf }
  | "*)"         { T_EndComment }

  | nonwhite+ as word 
                 { T_Word(word) }
  | eof          { T_Eof }

and nested_comment n = parse
  |"*)"       {if n==0 then lexer lexbuf else nested_comment (n-1) lexbuf}
  |"(*"       {nested_comment (n+1) lexbuf}
  |_          {nested_comment n lexbuf}

