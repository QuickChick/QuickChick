open QuickChickToolLexer
open QuickChickToolParser
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
  | Mutant of (bool * string) list * string * (string list)
*)

type mode = Test | Mutate
     
let rec cartesian (lists : 'a list list) : 'a list list = 
  match lists with
  | [ x ] -> List.map (fun y -> [y]) x
  | h::t -> List.concat (List.map (fun l -> (List.map (fun x -> x :: l) h))
                                  (cartesian t))

let test_out handle_section input = 
  let rec go = function 
    | Text s -> s 
    | Section (sn, nodes, _) -> 
       if handle_section sn then 
         let rec walk_nodes nodes = 
           match nodes with 
           | [] -> []
           | (Text s) :: rest -> 
              s :: (walk_nodes rest)
           | (Mutant (opts, base, muts) :: rest) ->
              base :: walk_nodes rest 
           | (QuickChick s) :: rest ->
              Printf.sprintf "QuickChick %s" s :: walk_nodes rest 
         in String.concat "\n" (walk_nodes nodes)
       else String.concat "\n" (List.map output_plain nodes)
    | _ -> failwith "Toplevel QuickChick/Mutant" in
  String.concat "\n" (List.map go input)

let main = 
  let mode = ref Test in
  let input_channel = ref stdin in
  let set_mode = function 
    | "test"   -> mode := Test
    | "mutate" -> mode := Mutate in
  let sec_name = ref None in
  let speclist = 
    [ ("-m", (Arg.Symbol (["test"; "mutate"], set_mode)), "Sets the mode of operation") 
    ; ("-s", Arg.String (fun name -> sec_name := Some name), "Which section's properties to test")
    ]
  in
  let usage_msg = "quickChick <input_file> options\nTest a file or evaluate your testing using mutants." in
  Arg.parse speclist (fun anon -> input_channel := open_in anon) usage_msg;

  let handle_section = 
    match !sec_name with
    | Some sn -> fun sn' -> sn = sn'
    | None    -> fun _ -> true in

  let lexbuf = Lexing.from_channel !input_channel in
  let result = program lexer lexbuf in

  let coqc_cmd vf = Printf.sprintf "coqc -w none %s" vf in

  match !mode with
  | Test ->
     let out_data = test_out handle_section result in
     let vf = Filename.temp_file "QuickChick" ".v" in
     let out_channel = open_out vf in
     output_string out_channel out_data;
     close_out out_channel;
     if Sys.command (coqc_cmd vf) <> 0 then
       failwith "Could not compile mutated program"
     else ()
  | Mutate -> failwith "Mutate not implemented yet"
