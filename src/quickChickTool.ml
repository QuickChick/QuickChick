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

type 'a file_structure = File of string * 'a list
                       | Dir of string * 'a file_structure list

let main = 
(*  Parsing.set_trace true; *)

  let mode = ref Mutate in
  let compile_command = ref "make" in
  let input_name = ref "" in
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
    ; ("-c", Arg.String (fun name -> compile_command := name), "Compile command for entire directory")
    ]
  in
  let usage_msg = "quickChick <input_file> options\nTest a file or evaluate your testing using mutants." in
  Arg.parse speclist (fun anon -> input_name := anon) usage_msg;

  let rec parse_file_or_dir file_name = 
    try if Sys.is_directory file_name 
        then failwith "Implement directory"
        else begin
          let lexbuf = Lexing.from_channel (open_in file_name) in
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
          File (file_name, result)
        end
    with Sys_error _ -> failwith "Given file does not exist" in

  let fs = parse_file_or_dir !input_name in

  let rec section_length_of_fs fs = 
    match fs with 
    | File (_, ss) -> List.length ss
    | Dir (_, fss) -> List.fold_left (+) 0 (List.map section_length_of_fs fss) in

  let trim s = 
    match Str.split (Str.regexp "[ \r\n\t]") s with
    | [] -> ""
    | h :: _ -> h in

  (* Create a table of sections *)
  let sec_graph = Hashtbl.create (section_length_of_fs fs) in 
  let sec_find s = try Hashtbl.find sec_graph (trim s) 
                   with Not_found -> failwith (Printf.sprintf "Didn't find: %s\n" s) in

  (* Populate a based on a single list of sections *)
  let rec populate_hashtbl_sections (sections : section list) = 
    match sections with
    | [] -> ()
    | Section (_, sn, _, extopt, _) :: rest -> 
       let extends = match extopt with 
         | Some (_, x, _) -> x 
         | None -> [] in
       let base = List.map trim (sn :: extends) in
       Hashtbl.add sec_graph (trim sn) (List.fold_left (fun acc sec_name -> SS.union acc (sec_find sec_name)) (SS.of_list base) extends);
       populate_hashtbl_sections rest in

  (* Populate based on an entire file structure *)
  let rec populate_hashtbl (fs : section file_structure) = 
    match fs with 
    | File (_, ss) -> populate_hashtbl_sections ss
    | Dir (_, fss) -> List.iter populate_hashtbl fss in

  (* Actually fill the hashtable *)
  populate_hashtbl fs;

(*   Hashtbl.iter (fun a b -> Printf.printf "%s -> %s\n" a (String.concat ", " (SS.elements b))) sec_graph;  *)

  (* Function that tells you whether to handle a section (mutate/uncomment quickChicks) or not *)
  let handle_section = 
    match !sec_name with
    | Some sn -> fun sn' -> SS.mem (trim sn') (sec_find sn)
    | None    -> fun _ -> true in

  let write_file out_file out_data = 
    if !verbose then (Printf.printf "Writing to file: %s\n" out_file; flush_all()) else ();
    let out_channel = open_out out_file in
    output_string out_channel out_data;
    close_out out_channel;
    out_file
  in

  let write_tmp_file out_data = 
    let vf = Filename.temp_file "QuickChick" ".v" in 
    write_file vf out_data in


  (* Creates a temporary directory at /tmp and returns its name *)
  let mk_tmp_dir () = 
    let s = Filename.temp_file "QuickChick" ""  in
    Sys.remove s;
    Unix.mkdir s 0o775;
    s in

  let coqc_single_cmd vf = Printf.sprintf "coqc -w none -Q . Top %s" vf in

  let compile_and_run vf =
    (* TODO: Capture/parse output *)
    (* Printf.printf "coqc_cmd = %s\n" (coqc_cmd vf); *)
    if Sys.command (coqc_single_cmd vf) <> 0 then
      failwith "Could not compile mutated program"
    else () in

  match !mode with
  | Test -> begin
     match fs with 
     | File (s, ss) -> 
         let out_data = test_out handle_section ss in
         let vf = write_tmp_file out_data in
         compile_and_run vf
     | Dir (s, fss) -> failwith "Implement dir"
    end 
  | Mutate -> begin
     match fs with 
     | File (s, ss) ->
       let (base,muts) = match mutate_outs handle_section ss with
         | base :: muts -> (base, muts)
         | _ -> failwith "empty mutants" in
       (* BCP: I think we should not test the base when testing mutants *)
       (* LEO: Really? I think it's a good baseline. Bug in base -> No point in testing mutants... *)
       (* 
       if !verbose then print_endline "Testing original (no mutants)..." else ();
       let base_file = write_tmp_file base in 
       compile_and_run base_file; 
        *)
       List.iteri (fun i m ->
         (if i > 0 then Printf.printf "\n");
         Printf.printf "Handling Mutant %d.\n" i; flush_all ();
         compile_and_run (write_tmp_file m)
                  ) muts
     | Dir (s, fss) -> failwith "Implement dir"
     end
