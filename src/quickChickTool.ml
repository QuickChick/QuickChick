open QuickChickToolLexer
open QuickChickToolParser
open QuickChickToolTypes

type mode = Test | Mutate

let ansi = ref false

type highlight_style = Header | Failure

let highlight style s : unit =
  if !ansi then begin
    begin match style with
    | Header ->
      print_string "\027[31m"; (* red *)
      print_string "\027[43m"; (* on yellow *)
    | Failure ->
      print_string "\027[37m"; (* white *)
      print_string "\027[41m"; (* on red *)
    end;
    print_string "\027[1m"; (* bold *)
    print_string s;
    print_string "\027[m"
  end else begin
    print_string s;
  end;
  print_newline ();
  flush_all ()

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
       (*Printf.printf "Inside go for %s. Handle? %b\n" sn (handle_section sn); *)
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
         in Printf.sprintf "%s%s%s%s%s" 
                           (if sn = "" || sn.[0] = '_' then "" else startSec)
                           (if sn = "" || sn.[0] = '_' then "" else sn) (* __default... -> don't print it *)
                           (if sn = "" || sn.[0] = '_' then "" else endSec)
                           (output_extends extends) 
                           (String.concat "" (walk_nodes nodes))
       else output_section s 
  in String.concat "" (List.map go input)

let combine_mutants (bms : ('a * 'a list) list) = 
  let rec combine_aux bms =
    match bms with 
    | [] -> [[]]
    | (b,ms)::bms' ->
       let non_mutant_rest = List.map fst bms' in
       let mutated_now = 
         List.map (fun m -> m :: non_mutant_rest) ms in
       let mutated_later = 
         List.map (fun ms' -> b :: ms') (combine_aux bms') in 
       mutated_now @ mutated_later in
  List.rev (combine_aux bms)

let from_cons (l : 'a list) : 'a * 'a list =
  match l with
    [] -> failwith "Not expecting empty list!"
  | h::t -> (h,t)

let from_Some (o : 'a option) : 'a =
  match o with
    None -> failwith "Not expecting None!"
  | Some x -> x

let mutate_outs handle_section input = 
  let rec go = function
    | Section (_, sn, _, _, nodes) ->
       (* Printf.printf "Handling section: %s. Handle? %b\n" sn (handle_section sn); *)
       if handle_section sn then 
         let handle_node = function
           | Text s -> (s, [])
           | Mutants (start, base, muts) ->
              let (non_mutated, mutants) = 
                match all_mutants muts with
                | non_mutated :: mutants -> (non_mutated, List.rev mutants) 
                | [] -> failwith "Internal error" in
(*              Printf.printf "DEBUG:\nBASE: %s\nMUTS:\n%s\n" non_mutated (String.concat "\n\n\n" mutants); *)
              (Printf.sprintf "%s%s%s" start base non_mutated, 
               List.map (fun s -> Printf.sprintf "%s (* %s *) %s" start base s) mutants)
           | QuickChick (s1,s2,s3) -> (Printf.sprintf "%s*) QuickChick %s (*%s" s1 s2 s3, []) (* Add all tests *) in
         from_cons (List.map (String.concat "") (combine_mutants (List.map handle_node nodes)))
       else (String.concat "" (List.map output_node nodes), [])
  in List.map (String.concat "") (combine_mutants (List.map go input))

module SS = Set.Make(String)

type 'a file_structure = File of string * 'a 
                       | Dir of string * 'a file_structure list

(* Not sure we need this one, but keeping the code for now, for reference 
let collect_process_output' = fun command -> 
  let chan = Unix.open_process_in command in
  let res = ref ([] : string list) in
  let rec process_otl_aux () =  
    let e = input_line chan in
    res := e::!res;
    process_otl_aux() in
  try process_otl_aux ()
  with End_of_file ->
    let stat = Unix.close_process_in chan in
    match stat with
      WEXITED 0 -> List.rev !res
    | WEXITED i -> List.rev (Printf.sprintf "Exited with status %d\n" i :: !res)
    | WSIGNALED i -> List.rev (Printf.sprintf "Killed (%d)\n" i :: !res)
    | WSTOPPED i -> List.rev (Printf.sprintf "Stopped (%d)\n" i :: !res)
*)

let is_prefix pre s =
  String.length s >= String.length pre
  && String.sub s 0 (String.length pre) = pre

type test_result =
  { mutable passed: int;
    mutable failed: int;
    mutable inconclusive: int }

let test_results = {passed=0; failed=0; inconclusive=0}

let reset_test_results () =
  test_results.passed <- 0;
  test_results.failed <- 0;
  test_results.inconclusive <- 0

type expected_results = ExpectOnlySuccesses | ExpectSomeFailure

let something_failed = ref false
let fail_eagerly = ref false

let confirm_results e =
  let failed s =
    highlight Failure (Printf.sprintf "Error: %s" s);
    if !fail_eagerly then
      exit 1
    else
      something_failed := true  in
  if test_results.inconclusive > 0 then 
    failed "Inconclusive test"
  else match e with
  | ExpectOnlySuccesses -> 
    if test_results.failed > 0 then 
      failed "Test failed"
  | ExpectSomeFailure -> 
    failed "No tests failed for this mutant"

let compile_and_run command e : unit =
  reset_test_results();
  let chan = Unix.open_process_in command in
  let rec process_otl_aux () =  
    (* BCP: If we ever have long-running tests that do things like printing
       a . every once in a while, we'll need to change this so that they don't
       get buffered for too long: *)
    let e = input_line chan in
    print_string e; print_newline();
    if is_prefix "+++ Passed" e then
      test_results.passed <- test_results.passed+1
    else if is_prefix "+++ Failed (as expected)" e then
      test_results.passed <- test_results.passed+1
    else if is_prefix "*** Failed" e then
      test_results.failed <- test_results.failed+1;
    process_otl_aux() in
  try process_otl_aux ()
  with End_of_file ->
    let stat = Unix.close_process_in chan in
    begin match stat with
    | Unix.WEXITED 0 ->
      ()
    | Unix.WEXITED i ->
      highlight Failure (Printf.sprintf "Exited with status %d" i);
      test_results.inconclusive <- test_results.inconclusive + 1
    | Unix.WSIGNALED i ->
      highlight Failure (Printf.sprintf "Killed (%d)" i); 
      test_results.inconclusive <- test_results.inconclusive + 1
    | Unix.WSTOPPED i ->
      highlight Failure (Printf.sprintf "Stopped (%d)" i);
      test_results.inconclusive <- test_results.inconclusive + 1
    end;
  confirm_results e

(* BCP: This function is too big! And there's too much duplication. *)
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
    ; ("+faileagerly", Arg.Unit (fun _ -> fail_eagerly := true), "Stop as soon as a problem is detected")
    ; ("+color", Arg.Unit (fun _ -> ansi := true), "Use colors on an ANSI-compatible terminal")
    ; ("-c", Arg.String (fun name -> compile_command := name), "Compile command for entire directory")
    ]
  in
  let usage_msg = "quickChick <input_file> options\nTest a file or evaluate your testing using mutants." in
  Arg.parse speclist (fun anon -> input_name := anon) usage_msg;

  let rec catMaybes = function
    | [] -> []
    | Some x :: t -> x :: catMaybes t
    | None :: t -> catMaybes t in

  let rec parse_file_or_dir file_name = 
    try if Sys.is_directory file_name 
        then begin
          if Filename.basename file_name = "_qc" then None else begin 
          let ls = Sys.readdir file_name in
(*           Array.iter (fun s -> Printf.printf "  %s\n" s) ls;*)
          let parsed = List.map (fun s -> parse_file_or_dir (file_name ^ "/" ^ s)) (Array.to_list ls) in
          Some (Dir (file_name, catMaybes parsed))
          end
        end
        else begin
          let handle = (Filename.basename file_name = "_CoqProject"  || 
                        Filename.basename file_name = "Makefile"     || 
                        Filename.check_suffix file_name "v") in
          if handle then begin 
  (*           Printf.printf "In file: %s\n" file_name;*)
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
            let fixed_default = 
              match result with 
              | (Section (a,b,c,exts,e) :: ss ) ->
                 Section ("(*", "__default_" ^ file_name, "*)\n", exts, e) :: ss
              | _ -> failwith "Empty section list?" in
               
            Some (File (file_name, fixed_default))
                      end
          else None
        end
    with Sys_error _ -> failwith (file_name ^ " does not exist?") in

  let fs = from_Some (parse_file_or_dir !input_name) in

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
       Hashtbl.add sec_graph (trim sn) extends;
       populate_hashtbl_sections rest in

  (* Populate based on an entire file structure *)
  let rec populate_hashtbl (fs : section list file_structure) = 
    match fs with 
    | File (_, ss) -> populate_hashtbl_sections ss
    | Dir (_, fss) -> List.iter populate_hashtbl fss in

  (* Actually fill the hashtable *)
  populate_hashtbl fs;

(*  Hashtbl.iter (fun a b -> Printf.printf "%s -> %s\n" a (String.concat ", " b)) sec_graph; flush_all (); *)

  (* Function that tells you whether to handle a section (mutate/uncomment quickChicks) or not *)
  let rec handle_section' current_section starting_section = 
    let current_section  = trim current_section in
    let starting_section = trim starting_section in
    current_section = starting_section || 
      List.exists (fun starting_section' -> handle_section' current_section starting_section') (sec_find starting_section) in
  
  let rec handle_section sn' =
    (* Printf.printf "Asking for %s\n" sn'; flush_all (); *)
    let sn' = trim sn' in
    match !sec_name with
    | Some sn -> handle_section' sn' sn
    | None    -> true in

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

  let coqc_single_cmd vf = Printf.sprintf "coqc -w none -Q . Top %s" vf in

  let load_file f =
    let ic = open_in f in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    (s) in

  match !mode with
  | Test -> begin
     match fs with 
     | File (s, ss) -> 
         let out_data = test_out handle_section ss in
         let vf = write_tmp_file out_data in
         compile_and_run (coqc_single_cmd vf) ExpectOnlySuccesses
     | Dir (s, fss) -> begin
         let tmp_dir = 
           ignore (Sys.command "mkdir -p _qc");
           "_qc" in
         let rec output_test_dir fs =
           match fs with 
           | File (s, ss) -> 
              let out_data = test_out handle_section ss in
              let out_file = tmp_dir ^ "/" ^ s in 
              if Sys.file_exists out_file && load_file out_file = out_data then ()
              else ignore (write_file (tmp_dir ^ "/" ^ s) out_data)
           | Dir (s, fss) -> begin 
                let dir_name = tmp_dir ^ "/" ^ s in
                if Sys.command (Printf.sprintf "mkdir -p %s" dir_name) <> 0 then
                  failwith ("Could not create directory: " ^ dir_name)
                else List.iter output_test_dir fss
             end in
         (* Entire file structure is copied *)
         output_test_dir fs;
         (* Execute make at tmp_dir *)
         compile_and_run ("make -C " ^ tmp_dir ^ "/" ^ s) ExpectOnlySuccesses
       end
    end 
  | Mutate -> begin
     match fs with 
     | File (s, ss) ->
       let (base,muts) = match mutate_outs handle_section ss with
         | base :: muts -> (base, muts)
         | _ -> failwith "empty mutants" in
       (* BCP: I think we should not test the base when testing mutants *)
       (* LEO: Really? I think it's a good baseline. Bug in base -> No point
          in testing mutants... *)
       (* BCP: OK, doing it first is fine.  But we also want to be able to
          run a single mutant by name. *)
       highlight Header "Testing base version...";
       let base_file = write_tmp_file base in 
       compile_and_run (coqc_single_cmd base_file) ExpectOnlySuccesses;
       List.iteri (fun i m ->
         (if i > 0 then Printf.printf "\n");
         highlight Header (Printf.sprintf "Testing mutant %d..." i); 
         reset_test_results();
         compile_and_run (coqc_single_cmd (write_tmp_file m)) ExpectSomeFailure
       ) muts
     | Dir (s, fss) -> begin
       let rec calc_dir_mutants fs
           : (string file_structure * string file_structure list) = 
          match fs with 
          | File (s, ss) ->
             (* Printf.printf "Calc mutants for file: %s\n" s; flush_all (); *)
             begin match mutate_outs handle_section ss with 
             | base :: muts -> 
                (* Printf.printf "Number of mutants: %d\n" (List.length muts); *)
                (File (s, base), List.map (fun m -> File (s, m)) muts)
             | _ -> failwith "no base mutant"
             end
          | Dir (s, fss) -> begin 
              (* Printf.printf "Calc mutants for dir: %s\n" s; flush_all (); *)
              let bmfs = List.map calc_dir_mutants fss in
              let rec all_mutant_fs (bmfs : ('a * 'a list) list) = 
                match bmfs with 
                | [] -> [[]]
                | (b,mfs)::bmfs' ->
                   let non_mutant_rest = List.map fst bmfs' in
                   let mutated_now = 
                     List.map (fun mf -> mf :: non_mutant_rest) mfs in
                   let mutated_later = 
                     List.map (fun mfs' -> b :: mfs') (all_mutant_fs bmfs') in 
                   mutated_now @ mutated_later in
              begin match List.rev (all_mutant_fs bmfs) with 
              | base :: muts -> (Dir (s, base), List.map (fun m -> Dir (s, m)) muts)
              | [] -> failwith "no base dir mutant"
              end
            end in

        let (base, dir_mutants) = calc_dir_mutants fs in

(*
        let rec debug_string_fs = function
          | File (s, t) -> Printf.printf "@@%s:\n%s\n\n" s t
          | Dir (s, ts) -> Printf.printf "**%s:\n" s; List.iter debug_string_fs ts in

        Printf.printf "Base:\n"; debug_string_fs base;
        List.iteri (fun i fs -> Printf.printf "%d:\n" i; debug_string_fs fs) dir_mutants;
 *)

        (* LEO: Again, nothing/something for base? *)
        let rec output_mut_dir tmp_dir fs =
           match fs with 
           | File (s, plaintext) -> 
              let out_data = plaintext in
              let out_file = tmp_dir ^ "/" ^ s in 
              if Sys.file_exists out_file && load_file out_file = out_data then
                ()
              else ignore (write_file (tmp_dir ^ "/" ^ s) out_data)
           | Dir (s, fss) -> begin 
                let dir_name = tmp_dir ^ "/" ^ s in
                if Sys.command (Printf.sprintf "mkdir -p %s" dir_name) <> 0 then
                  failwith ("Could not create directory: " ^ dir_name)
                else List.iter (output_mut_dir tmp_dir) fss
             end in
        (* Base mutant *)
        highlight Header "Testing base version..."; 
        let tmp_dir = 
           ignore (Sys.command "mkdir -p _qc");
           "_qc" in
        (* Entire file structure is copied *)
        output_mut_dir tmp_dir base;
        (* Execute make at tmp_dir *)
        compile_and_run ("make -C " ^ tmp_dir ^ "/" ^ s) ExpectOnlySuccesses;
        
        (* For each mutant structure *)
        List.iteri (fun i m ->
         (if i > 0 then Printf.printf "\n");
         highlight Header (Printf.sprintf "Testing mutant %d..." i);
         let tmp_dir = 
           ignore (Sys.command "mkdir -p _qc");
           "_qc" in
         (* Entire file structure is copied *)
         output_mut_dir tmp_dir m;
         (* Execute make at tmp_dir *)
         let dir = tmp_dir ^ "/" ^ s in
         reset_test_results();
         compile_and_run ("make -C " ^ dir) ExpectSomeFailure
        ) dir_mutants

       end
  end;

  if !something_failed then exit 1
      

