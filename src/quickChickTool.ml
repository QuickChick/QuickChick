open QuickChickToolLexer
open QuickChickToolParser
open QuickChickToolTypes

type mode = Test | Mutate

let rec add_heads accs lists = 
  match lists with 
  | [] -> List.map List.rev accs
  | ((h::_)::rest) -> add_heads (List.map (fun acc -> h :: acc) accs) rest
  | _ -> failwith "Doesn't have a head"

let rec combinations (acc : 'a list) (lists : 'a list list) : 'a list list = 
  match lists with 
  | [] -> [List.rev acc]
  | [x] :: t -> combinations (x::acc) t
  | (x::xs) :: t -> 
    combinations (x::acc) t @ add_heads (List.map (fun x' -> x' :: acc) xs) t
  | _ -> failwith "Empty inner list"

let rec non_mutants acc muts = 
  match muts with 
  | [] -> [List.rev acc]
  | (start, code, endc) :: rest ->
     non_mutants  (Printf.sprintf "%s%s%s" start code endc :: acc) rest 

let rec all_mutants' acc (muts : mutant list) : string list list = 
  match muts with 
  | [] -> [List.rev acc]
  | (start, code, endc) :: rest -> 
     all_mutants' (Printf.sprintf "%s%s%s" start code endc :: acc) rest @
     non_mutants  (Printf.sprintf "%s *) %s (* %s" start code endc :: acc) rest 

  
let all_mutants muts = 
  List.map (String.concat "") (all_mutants' [] muts)

let rec cartesian (lists : 'a list list) : 'a list list = 
  match lists with
  | [ x ] -> List.map (fun y -> [y]) x
  | h::t -> List.concat (List.map (fun l -> (List.map (fun x -> x :: l) h)) (cartesian t))
  | [] -> []

let test_out handle_section input = 
  let rec go = function 
    | Section (startSec, sn, endSec, extends, nodes) as s -> 
       if handle_section sn then  
         let rec walk_nodes nodes = 
           match nodes with 
           | [] -> []
           | (Text s) :: rest -> 
              s :: (walk_nodes rest)
           | (Mutants (start, base, muts) :: rest) ->
              (Printf.sprintf "%s%s%s" start base (String.concat "" (List.map output_mutant muts))) :: walk_nodes rest 
           | (QuickChick (s1,s2,s3)) :: rest ->
              (Printf.sprintf "%s*) QuickChick %s (*%s" s1 s2 s3) :: walk_nodes rest
         in Printf.sprintf "%s%s%s%s%s" startSec sn endSec (output_extends extends) (String.concat "" (walk_nodes nodes))
       else output_section s 
  in String.concat "" (List.map go input)

let mutate_outs handle_section input = 
  let rec go = function
    | Section (_, sn, _, _, nodes) ->
       if handle_section sn then 
         let handle_node = function
           | Text s -> [s]
           | Mutants (start, base, muts) ->
              let (non_mutated, mutants) = 
                match all_mutants muts with
                | non_mutated :: mutants -> (non_mutated, List.rev mutants) 
                | [] -> failwith "Internal error" in
(*              Printf.printf "DEBUG:\nBASE: %s\nMUTS:\n%s\n" non_mutated (String.concat "\n\n\n" mutants); *)
              (Printf.sprintf "%s%s%s" start base non_mutated) ::
              (List.map (fun s -> Printf.sprintf "%s (* %s *) %s" start base s) mutants)
           | QuickChick (s1,s2,s3) -> [Printf.sprintf "%s*) QuickChick %s (*%s" s1 s2 s3] (* Add all tests *) in
         List.map (String.concat "") (cartesian (List.map handle_node nodes)) 
       else [String.concat "" (List.map output_node nodes)]
  in List.map (String.concat "") (cartesian (List.map go input))

module SS = Set.Make(String)

let main = 
(*  Parsing.set_trace true; *)

  let mode = ref Mutate in
  let input_channel = ref stdin in
  let set_mode = function 
    | "test"   -> mode := Test
    | "mutate" -> mode := Mutate 
    | _ -> failwith "Expected 'test' or 'mutate'" in
  let sec_name = ref None in

  let verbose = ref false in
  let speclist = 
    [ ("-m", (Arg.Symbol (["test"; "mutate"], set_mode)), "Sets the mode of operation") 
    ; ("-s", Arg.String (fun name -> sec_name := Some name), "Which section's properties to test")
    ; ("-v", Arg.Unit (fun _ -> verbose := false), "Silent mode")
    ; ("+v", Arg.Unit (fun _ -> verbose := true), "Verbose mode")
    ]
  in
  let usage_msg = "quickChick <input_file> options\nTest a file or evaluate your testing using mutants." in
  Arg.parse speclist (fun anon -> input_channel := open_in anon) usage_msg;

  let lexbuf = Lexing.from_channel !input_channel in
  let result = program lexer lexbuf in

  (* Step 1: fix extends *)
  let fix_extends extends = 
    Str.split (Str.regexp "[ \r\n\t]") (String.concat "" extends) in 

  let result = List.map (fun (Section (a,b,c,exts,e)) ->
                              Section (a,b,c,
                                       (match exts with 
                                       | Some (start, names, endc) -> Some (start, fix_extends names, endc)
                                       | None -> None),
                                       e)
                        ) result in                            
  
  let trim s = 
    match Str.split (Str.regexp "[ \r\n\t]") s with
    | [] -> ""
    | h :: _ -> h in

  (* Create a table of section *)
  let sec_graph = Hashtbl.create (List.length result) in 
  let sec_find s = try Hashtbl.find sec_graph (trim s) 
                   with Not_found -> failwith (Printf.sprintf "Didn't find: %s\n" s) in
  let rec populate_hashtbl (sections : section list) = 
    match sections with
    | [] -> ()
    | Section (_, sn, _, extopt, _) :: rest -> 
       let extends = match extopt with 
         | Some (_, x, _) -> x 
         | None -> [] in
       let base = List.map trim (sn :: extends) in
       Hashtbl.add sec_graph (trim sn) (List.fold_left (fun acc sec_name -> SS.union acc (sec_find sec_name)) (SS.of_list base) extends);
       populate_hashtbl rest  in

  populate_hashtbl result;

(*   Hashtbl.iter (fun a b -> Printf.printf "%s -> %s\n" a (String.concat ", " (SS.elements b))) sec_graph;  *)

  let handle_section = 
    match !sec_name with
    | Some sn -> fun sn' -> SS.mem (trim sn') (sec_find sn)
    | None    -> fun _ -> true in

  let write_tmp_file data = 
    let vf = Filename.temp_file "QuickChick" ".v" in
    if !verbose then (Printf.printf "Writing to file: %s\n" vf; flush_all()) else ();
    let out_channel = open_out vf in
    output_string out_channel data;
    close_out out_channel;
    vf
  in

  let coqc_cmd vf = Printf.sprintf "coqc -w none -Q . Top %s" vf in

  let compile_and_run vf =
    (* TODO: Capture/parse output *)
    (* Printf.printf "coqc_cmd = %s\n" (coqc_cmd vf); *)
    if Sys.command (coqc_cmd vf) <> 0 then
      failwith "Could not compile mutated program"
    else () in

  match !mode with
  | Test ->
     let out_data = test_out handle_section result in
     let vf = write_tmp_file out_data in
     compile_and_run vf
  | Mutate -> 
     let (base,muts) = match mutate_outs handle_section result with
       | base :: muts -> (base, muts)
       | _ -> failwith "empty mutants" in
     (* BCP: I think we should not test the base when testing mutants 
     if !verbose then print_endline "Testing original (no mutants)..." else ();
     let base_file = write_tmp_file base in 
     compile_and_run base_file; *)
     List.iteri (fun i m ->
       (if i > 1 then Printf.printf "\n");
       Printf.printf "Handling Mutant %d.\n" i; flush_all ();
       compile_and_run (write_tmp_file m)
                ) muts
