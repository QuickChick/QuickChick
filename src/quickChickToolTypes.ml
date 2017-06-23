type mutant = string * string * string

type node =
  (* Base chunk of text *)
  | Text of string 
  (* Commented out QuickChick call *)
  | QuickChick of (string * string * string)
  (* Mutant: start of mutant, base, list of mutants *)
  | Mutants of string * string * mutant list

type extend = (string * string list * string)

type section = 
  (* Sections: Start comment, section name, end comment, extends, contents *)
  | Section of string * string * string * extend option * node list 

let rec output_mutant (a,b,c) = a ^ b ^ c

let rec output_node = function
  | Text s -> s 
  | QuickChick (s1,s2,s3) -> (s1 ^ s2 ^ s3)
  | Mutants (start,base,variations) -> 
     Printf.sprintf "%s%s%s" start base (String.concat "" (List.map output_mutant variations))

let output_extends = function
  | Some (st, exts, en) -> st ^ String.concat "" exts ^ en
  | None -> ""

let output_section = function
  | Section (start, id, endc, extends, ns) -> 
     let qual s = if id.[0] = '_' then "" else s in
     Printf.sprintf "%s%s%s%s%s" (qual start) (qual id) (qual endc) (output_extends extends) (String.concat "" (List.map output_node ns))


