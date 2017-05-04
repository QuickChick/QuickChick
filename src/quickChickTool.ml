open QuickChickToolLexer
open QuickChickToolParser
open QuickChickToolTypes

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

let mutate_outs handle_section input = 
  let rec go = function
    | Text s -> [s] 
    | Section (sn, nodes, _) ->
       if handle_section sn then 
         let handle_node = function
           | Text s -> [s]
           | Mutant (opts, base, muts) ->
               base :: muts (* Base followed by mutants *)
           | QuickChick s -> ["QuickChick " ^ s] (* Add all tests *) in
         List.map (String.concat "\n") (cartesian (List.map handle_node nodes))
       else [String.concat "\n" (List.map output_plain nodes)]
  in List.map (String.concat "\n") (cartesian (List.map go input))

module SS = Set.Make(String)

let main = 
(*  Parsing.set_trace true; *)

  let mode = ref Test in
  let input_channel = ref stdin in
  let set_mode = function 
    | "test"   -> mode := Test
    | "mutate" -> mode := Mutate in
  let sec_name = ref None in

  let verbose = ref true in
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

  let sec_graph = Hashtbl.create (List.length result) in 
  let sec_find s = try Hashtbl.find sec_graph s 
                   with Not_found -> failwith (Printf.sprintf "Didn't find: %s\n" s) in
  let rec populate_hashtbl = function 
    | [] -> ()
    | Text _ :: rest -> populate_hashtbl rest 
    | Section (sn, _, extends) :: rest -> 
       Hashtbl.add sec_graph sn (List.fold_left (fun acc sec_name -> SS.union acc (sec_find sec_name)) (SS.of_list (sn :: extends)) extends);
       populate_hashtbl rest  in

  populate_hashtbl result;
(*  Hashtbl.iter (fun a b -> Printf.printf "%s -> %s\n" a (String.concat ", " (SS.elements b))) sec_graph; *)
  let handle_section = 
    match !sec_name with
    | Some sn -> fun sn' -> SS.mem sn' (sec_find sn)
    | None    -> fun _ -> true in

  let coqc_cmd vf = Printf.sprintf "coqc -w none %s" vf in

  let write_tmp_file data = 
    let vf = Filename.temp_file "QuickChick" ".v" in
    if !verbose then (Printf.printf "Writing to file: %s\n" vf; flush_all()) else ();
    let out_channel = open_out vf in
    output_string out_channel data;
    close_out out_channel;
    vf
  in

  let compile_and_run vf =
    (* TODO: Capture/parse output *)
    if Sys.command (coqc_cmd vf) <> 0 then
      failwith "Could not compile mutated program"
    else () in

  match !mode with
  | Test ->
     let out_data = test_out handle_section result in
     let vf = write_tmp_file out_data in
     compile_and_run vf
  | Mutate -> 
     let (base :: muts) = mutate_outs handle_section result in
     if !verbose then print_endline "Testing original (no mutants)..." else ();
     let base_file = write_tmp_file base in 
     compile_and_run base_file;
     List.iteri (fun i m ->
       Printf.printf "Handling Mutant %d.\n" i; flush_all ();
       compile_and_run (write_tmp_file m)
                ) muts
