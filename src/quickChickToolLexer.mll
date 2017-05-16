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
    
  | (white* as s) "Section"         { line_incs s lexbuf; T_Section s }
  | (white* as s) "extends"         { line_incs s lexbuf; T_Extends s }
  | (white* as s) "QuickChick"      { line_incs s lexbuf; T_QuickChick s }

  | (white* as s) "(*!"             { line_incs s lexbuf; T_StartQCComment s }
  | (white* as s) "(*?"             { line_incs s lexbuf; T_StartMutant s }
  | (white* as s) "(*"              { line_incs s lexbuf; T_StartComment s }

  | (white* as s) "*)"              { line_incs s lexbuf; T_EndComment s }

  | (white* as s) (nonwhite as c)   { line_incs s lexbuf; T_Char ((String.make 1 c)^s) }
  | (white* as s) eof               { line_incs s lexbuf; T_Eof s }



