{
open Lexing
open QuickChickToolParser
open QuickChickToolTypes
}

let white    = [' ' '\t' '\r' '\n']
let nonwhite = [^ ' ' '\t' '\r' '\n']

(* Main Parsing match *)
rule lexer = parse
    
  | "(*! Section"     { T_StartSec }
  | "(*! QuickChick"  { T_StartQC  }
  | "(*!\nQuickChick" { T_StartQC  }
  | "(*! *)"          { T_StartMutant }
  | "(*!"             { T_StartMutantVariant }

  (* Regular comments need to be handled to play with termination specials *)
  | "*)"         { T_EndComment }

  (* Skip initial whitespace *)
  | white+ as s  { T_White s }

  | nonwhite+ as word 
                 { print_endline ("Nonwhite: " ^ word); T_Word(word) }
  | eof          { T_Eof }



