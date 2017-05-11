{
open Lexing
open QuickChickToolParser
open QuickChickToolTypes
}

let white    = [' ' '\t' '\r' '\n']
let nonwhite = [^ ' ' '\t' '\r' '\n']

(* Main Parsing match *)
rule lexer = parse
    
  | "Section"         { T_Section }
  | "extends"         { T_Extends }
  | "QuickChick"      { T_QuickChick  }
  | "(*"              { T_StartComment  }
  | "(*!"             { T_StartQCComment  }
  | "*)"              { T_EndComment }

  | white+ as s       { T_White s }
  | nonwhite as c     { T_Char (String.make 1 c) }
  | eof               { T_Eof }



