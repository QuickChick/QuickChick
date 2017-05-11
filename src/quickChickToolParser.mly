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

%token T_Section
%token T_Extends
%token T_QuickChick

%token T_StartQCComment
%token T_StartComment
%token T_EndComment

%token T_Eof

%start program
%type <QuickChickToolTypes.node list> program
%type <QuickChickToolTypes.node> section
%type <QuickChickToolTypes.node list> sections
%type <QuickChickToolTypes.node list> contents
%type <QuickChickToolTypes.node> content
%type <string list> mutants
%type <string> mutant
%type <string list> code
%type <string> word
%type <string list> sec_names
%type <string list> extends

%% 
program:              code sections T_Eof { Text (String.concat "" $1) :: $2 }

sections:             section sections { $1 :: $2 }
                      | { [ (* Empty on purpose *) ] }

white:                T_White { $1 }
                      | { "" } 

chars:                T_Char { [$1] }
                      | T_Char chars { $1 :: $2 } 

word:                 chars { String.concat "" $1 }
                      
section:              T_StartQCComment white T_Section white word white extends white T_EndComment contents { Section ($5, $10, $7) }

extends:              { [] }
                      | T_Extends white sec_names { $3 }

sec_names:            word { [$1] }
                      | word white sec_names { $1 :: $3 }

contents:             content { [$1] }
                      | content contents { $1 :: $2 }

content:              code {  Text (String.concat "" $1)  }
                      | T_StartQCComment white T_QuickChick code T_EndComment { QuickChick (String.concat "" $4) }
                      | T_StartQCComment white T_EndComment code mutants { Mutant ([], String.concat "" $4, $5) }
                      | T_StartComment content T_EndComment { Text "(*" :: $2 :: Text "*)" }

mutants:              | { [] }
                      | mutant white mutants { $1 :: $3 }

mutant:               | T_StartQCComment code T_EndComment { String.concat "" $2 }

code:                 word { [ $1 ] }
                      | word white code { $1 :: $2 :: $3 }

word:                 word  { $1 }
                      | T_QuickChick { "QuickChick" }
                      | T_Section { "Section" }
                      | T_Extends { "extends" }

