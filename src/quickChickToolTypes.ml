type node =
  (* Base chunk of text *)
  | Text of string 
  (* Sections: identifier + a bunch of nodes + extend? *)
  | Section of string * node list * string option
  (* Commented out QuickChick call *)
  | QuickChick of string
  (* Mutant: list of +/- idents, base, list of mutants *)
  | Mutant of (bool * string) list * string * (string list)

let rec node_to_string = function
  | Text s -> s 
  | Section (id, ns, m) -> Printf.sprintf "Section: %s\n%s" id (String.concat "\n" (List.map node_to_string ns))
  | QuickChick s -> Printf.sprintf "QC: QuickChick %s" s
  | Mutant (_,base,vars) -> Printf.sprintf "Mutant:\nOriginal:%sVariants:%s" base (String.concat "\n" vars)

let rec output_plain = function
  | Text s -> s 
  | Section (id, ns, m) -> Printf.sprintf "%s" (String.concat "\n" (List.map output_plain ns))
  | QuickChick s -> "" (* Commented out *)
  | Mutant (_,base,vars) -> Printf.sprintf "%s" base 


