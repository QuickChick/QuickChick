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
%token<string> T_White

%token<string> T_Section
%token<string> T_Extends
%token<string> T_QuickChick

%token T_StartQCComment
%token T_StartMutant
%token T_StartComment
%token T_EndComment

%token T_Eof

%start program
%type <QuickChickToolTypes.node list> program
%type <QuickChickToolTypes.node> section
%type <QuickChickToolTypes.node list> sections
%type <QuickChickToolTypes.node list> section_contents
%type <QuickChickToolTypes.node> section_content
%type <string list> mutants
%type <string> mutant
%type <string list> code
%type <string> word
%type <string list> sec_names
%type <string list> extends

%% 
/* INVARIANT: All trailing whitespace is handled by the environment */
w:                    T_White { $1 }
                      | { "" } 

program:              default_section w sections w T_Eof { $1 :: $3 }
/*                       | error T_Eof { 
                        let pos = Parsing.symbol_start_pos () in
                        failwith (Printf.sprintf "Error in line %d, position %d" 
                                                 pos.pos_lnum (pos.pos_cnum - pos.pos_bol)) } */

default_section:      section_contents { Section ("default", $1, []) }

section_contents:     { [ (* Intentionally empty *) ] }
                      | section_content w section_contents { $1 :: $3 }

section_content:      code {  Text (String.concat "" $1)  }
                      | T_StartQCComment w T_QuickChick w code w T_EndComment { QuickChick (String.concat "" $5) }
                      | T_StartQCComment w T_EndComment w code w mutants { Mutant ([], String.concat "" $5, $7) }
                      | T_StartComment w section_contents w T_EndComment { Text (Printf.sprintf "(* %s *)" (String.concat "" (List.map output_plain $3))) }

code:                 word { [ $1 ] }
                      | word T_White code { $1 :: $2 :: $3 }

word:                 chars { String.concat "" $1 }
                      | T_QuickChick { "QuickChick " }
                      | T_Section { "Section " }
                      | T_Extends { "extends " }

chars:                T_Char { [$1] }
                      | T_Char chars { $1 :: $2 } 

mutants:              mutant { [$1] }
                      | mutant w mutants { $1 :: $3 }

mutant:               T_StartMutant w code w T_EndComment { String.concat "" $3 }

sections:             section w sections { $1 :: $3 }
                      | { [ (* Empty on purpose *) ] }
                      
section:              T_StartQCComment w T_Section w word w extends w T_EndComment section_contents { Section ($5, $10, $7) }

extends:              { [] }
                      | T_Extends w sec_names { $3 }

sec_names:            word { [$1] }
                      | word w sec_names { $1 :: $3 }
