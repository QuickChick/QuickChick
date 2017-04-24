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

%token<string> T_Word

%token<string> T_White
%token T_NLine
%token T_StartQC
%token T_EndComment
%token T_Section
%token T_QuickChick

%token T_Eof

%start program
%type <QuickChickToolTypes.node list> program
%type <QuickChickToolTypes.node> section
%type <QuickChickToolTypes.node list> sections
%type <QuickChickToolTypes.node list> content
%type <string list> code

%% 
program:              code sections T_Eof { Text (String.concat "" $1) :: $2 }

sections:             section sections { $1 :: $2 }
                      | { [ (* Empty on purpose *) ] }

section:              T_StartQC T_White T_Section T_White T_Word T_White T_EndComment content  { Section ($5, $8, None) }

content:              code { [ Text (String.concat "" $1) ] }

code:                 T_White  { [ $1 ] }
                      | T_Word { [ $1 ] }
                      | T_White code { $1 :: $2 }
                      | T_Word  code { $1 :: $2 }
