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
%token T_StartSec
%token T_StartQC
%token T_StartMutant
%token T_StartMutantVariant
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

%% 
program:              code sections T_Eof { Text (String.concat "" $1) :: $2 }

sections:             section sections { $1 :: $2 }
                      | { [ (* Empty on purpose *) ] }

section:              T_StartSec T_White T_Word T_White T_EndComment contents { Section ($3, $6, None) }

contents:             content { [$1] }
                      | content contents { $1 :: $2 }

content:              code {  Text (String.concat "" $1)  }
                      | T_StartQC code T_EndComment { QuickChick (String.concat "" $2) }
                      | T_StartMutant code mutants { Mutant ([], String.concat "" $2, $3) }

mutants:              | { [] }
                      | mutant T_White mutants { $1 :: $3 }

mutant:               | T_StartMutantVariant code T_EndComment { String.concat "" $2 }

code:                 word { [ $1 ] }
                      | word code { $1 :: $2 }

word:                 T_White  { $1 }
                      | T_Word { $1 }

