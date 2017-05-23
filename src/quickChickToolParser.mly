%{

open Lexing
open Parsing
open QuickChickToolTypes

(*
type node =
    (* Base chunk of text *)
  | Text of string 
    (* Sections: identifier + a bunch of nodes + extend? *)
  | Section of string * node list * string option
    (* Commented out QuickChick call *)
  | QuickChick of string
    (* Mutant: list of +/- idents, base, list of mutants *)
  | Mutant of (bool * string) list * string * string list 
*)

(* Uncomment for more debugging... *)

%}

%token<string> T_Char 

%token<string> T_Extends

%token<string> T_StartSection
%token<string> T_StartQuickChick
%token<string> T_StartMutant
%token<string> T_StartMutants
%token<string> T_StartComment
%token<string> T_EndComment
%token<string> T_Eof

%start program
%type <QuickChickToolTypes.node list> program
%type <QuickChickToolTypes.node> section
%type <QuickChickToolTypes.node list> sections
%type <QuickChickToolTypes.node list> section_contents
%type <QuickChickToolTypes.node> section_content
%type <string list> mutants
%type <string> mutant
%type <string list> code
%type <string list> extends

%% 
program:              default_section T_Eof { [$1] }
                    | default_section sections T_Eof { $1 :: $2 }
/*                    | error T_Eof { 
                        let pos = Parsing.symbol_start_pos () in
                        failwith (Printf.sprintf "Error in line %d, position %d" 
                                                 pos.pos_lnum (pos.pos_cnum - pos.pos_bol)) }  */

default_section:      section_contents { Section ("default", $1, []) }

section_contents:     { [] } 
                    | section_content section_contents { $1 :: $2 }

section_content:      T_Char 
                            {  Text $1 }
                      | T_StartQuickChick code T_EndComment
                            { QuickChick $3 }
                      | T_StartMutants code mutants
                            { Mutant ([], String.concat "" $2, $3) }
                      | T_StartComment section_contents T_EndComment
                            { Text (Printf.sprintf "(* %s *)"
                                      (String.concat "" (List.map output_plain $2))) }

code:                 T_Char { [$1] } 
                      | T_Char code { $1 :: $2 }
 /*                     | error { let pos = Parsing.symbol_start_pos () in
                                failwith (Printf.sprintf "Error in line %d, position %d" 
                                                         pos.pos_lnum (pos.pos_cnum - pos.pos_bol)) 
                              } */


mutants:              mutant { [$1] }
                    | mutant mutants { $1 :: $2 }

mutant:               T_StartMutant code T_EndComment { String.concat "" $2 }

sections:             section { [$1] }
                    | section sections { $1 :: $2 }
                      
section:              T_StartSection code T_EndComment extends section_contents
                           { Section (String.concat "" $2, $5, $4) }

extends:              { [] }
                    | T_Extends code T_EndComment { $2 }

