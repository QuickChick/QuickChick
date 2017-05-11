{
open Lexing
open QuickChickToolParser
open QuickChickToolTypes

(* Function to increase line count in lexbuf *)
let line_incs s lexbuf =
  let splits = Str.split_delim (Str.regexp "\n") s in 
  let pos = lexbuf.Lexing.lex_curr_p in
  lexbuf.Lexing.lex_curr_p <- {
    pos with 
      Lexing.pos_lnum = pos.Lexing.pos_lnum + (List.length splits - 1);
      Lexing.pos_bol = if List.length splits > 1 then pos.Lexing.pos_cnum - (String.length (List.hd (List.rev splits))) else pos.Lexing.pos_bol
  }
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

  | white+ as s       { line_incs s lexbuf; T_White s }
  | nonwhite as c     { T_Char (String.make 1 c) }
  | eof               { T_Eof }



