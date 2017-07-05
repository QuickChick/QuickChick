open QuickChickToolLexer
open QuickChickToolParser
open QuickChickToolTypes

(* ----------------------------------------------------------------- *)
(* Command-line *)

let compile_command = ref "make"
let top = ref "" (* Leo: or "Top"? *)
let ocamlbuild_args = ref ""

let sec_name = ref None
let verbose = ref false
let ansi = ref false
let fail_fast = ref false

let speclist =
  [ ("-s", Arg.String (fun name -> sec_name := Some name), "Which section's properties to test")
  ; ("-v", Arg.Unit (fun _ -> verbose := true), "Verbose mode")
  ; ("-failfast", Arg.Unit (fun _ -> fail_fast := true), "Stop as soon as a problem is detected")
  ; ("-color", Arg.Unit (fun _ -> ansi := true), "Use colors on an ANSI-compatible terminal")
  ; ("-cmd", Arg.String (fun name -> compile_command := name), "Compile command for entire directory")
  ; ("-top", Arg.String (fun name -> top := name), "Name of top-level logical module")
  ; ("-ocamlbuild", Arg.String (fun name -> ocamlbuild_args := name), "Arguments given to ocamlbuild")
  ]

let usage_msg = "quickChick options\nMutation testing for current directory"

;; Arg.parse speclist (fun anon -> Printf.fprintf stderr "Warning: Anonymous argument %s\n" anon) usage_msg

(* ----------------------------------------------------------------- *)
(* Infrastructure *)

let debug fmt =
  if !verbose then Printf.fprintf stdout (fmt ^^ "%!")
  else Printf.ifprintf stdout fmt

let tmp_dir = "../_qc_" ^ Filename.basename (Unix.getcwd ()) ^ ".tmp"

let ensure_dir_exists d = Sys.command ("mkdir -p " ^ d)

let ensure_tmpdir_exists () =
  ignore (ensure_dir_exists tmp_dir)

type highlight_style = Header | Failure

let highlight style s =
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
  let things_to_check = ref [] in
  let rec go = function
    | Section (_, sn, _, _, nodes) ->
      if handle_section sn then begin
        debug "Handling section: %s\n" sn;
        let handle_node = function
          | Text s -> (s, [])
          | Mutants (start, base, muts) ->
            let (non_mutated, mutants) =
              match all_mutants muts with
              | non_mutated :: mutants -> (non_mutated, List.rev mutants)
              | [] -> failwith "Internal error" in
            (Printf.sprintf "%s%s%s" start base non_mutated,
             List.map
               (fun s -> Printf.sprintf "%s (* %s *) %s" start base s)
               mutants)
          | QuickChick (s1,s2,s3) ->
            things_to_check := s2 :: !things_to_check;
            (Printf.sprintf "%s QuickChick %s %s" s1 s2 s3, []) (* Add all tests *)
        in
        from_cons (List.map (String.concat "")
                     (combine_mutants (List.map handle_node nodes)))
      end
      else (String.concat "" (List.map output_node nodes), [])
  in
  let result = List.map (String.concat "") (combine_mutants (List.map go input)) in
  (result, !things_to_check)

module SS = Set.Make(String)

type 'a file_structure = File of string * 'a
                       | Dir of string * 'a file_structure list

let gather_all_vs fs =
  let all_vs = ref [] in
  let rec loop fs =
    match fs with
    | File (s, _) ->
       if Filename.check_suffix s ".v" then
         all_vs := (Filename.chop_suffix s ".v") :: !all_vs
    | Dir (s, fss) ->
       List.iter loop fss
  in loop fs;
  !all_vs

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

let confirm_results e =
  let failed s =
    highlight Failure (Printf.sprintf "Unexpected result: %s" s);
    if !fail_fast then
      exit 1
    else
      something_failed := true  in
  if test_results.inconclusive > 0 then
    failed "Inconclusive test"
  else match e with
  | ExpectOnlySuccesses ->
    if test_results.failed > 0 then
      failed "Test failed in base"
  | ExpectSomeFailure ->
    if test_results.failed = 0 then
      failed "No tests failed for this mutant"

let temporary_file = "QuickChickTop.v"

let run_and_show_output_on_failure command msg =
  let chan = Unix.open_process_in command in
  let res = ref ([] : string list) in
  let rec process_otl_aux () =
    let e = input_line chan in
    res := e::!res;
    process_otl_aux() in
  try process_otl_aux ()
  with End_of_file ->
    let stat = Unix.close_process_in chan in
    let result =
      match stat with
        Unix.WEXITED 0 -> List.rev !res
      | Unix.WEXITED i -> List.rev (Printf.sprintf "Exited with status %d" i :: !res)
      | Unix.WSIGNALED i -> List.rev (Printf.sprintf "Killed (%d)" i :: !res)
      | Unix.WSTOPPED i -> List.rev (Printf.sprintf "Stopped (%d)" i :: !res) in
    if stat <> (Unix.WEXITED 0) || !verbose then
      List.iter (fun s -> (print_string s; print_newline())) result;
    if stat = Unix.WEXITED 0 then
      ()
    else
      failwith msg

let perl_hack () =
  let perl_cmd = "perl -i -p0e 's/type int =\\s*int/type tmptmptmp = int\\ntype int = tmptmptmp/sg' " in
  let hack_mli = perl_cmd ^ "*.mli" in
  let hack_ml = perl_cmd ^ "*.ml" in
  if Sys.command hack_mli <> 0 || Sys.command hack_ml <> 0 then
    debug "perl script hack failed. Report: %s" perl_cmd

let compile_and_run where e : unit =
  let here = Sys.getcwd() in
  Sys.chdir where;

  run_and_show_output_on_failure
    (!compile_command)
    (Printf.sprintf "Executing '%s' failed" (!compile_command));

  perl_hack ();

  let ocamlbuild_cmd =
    Printf.sprintf "ocamlbuild %s %s.native"
      !ocamlbuild_args
      (Filename.chop_suffix temporary_file ".v") in
  run_and_show_output_on_failure
    ocamlbuild_cmd "Ocamlbuild failure";

  reset_test_results();

  let run_command =
    Printf.sprintf "./%s.native" (Filename.chop_suffix temporary_file ".v") in
  let chan = Unix.open_process_in run_command in
  let found_result = ref false in
  let rec process_otl_aux () =
    (* BCP: If we ever have long-running tests that do things like printing
       a . every once in a while, we'll need to change this so that they don't
       get buffered for too long: *)
    let e = input_line chan in
    print_string e; print_newline();
    begin if is_prefix "+++ Passed" e then
      (test_results.passed <- test_results.passed+1; found_result := true)
    else if is_prefix "+++ Failed (as expected)" e then
      (test_results.passed <- test_results.passed+1; found_result := true)
    else if is_prefix "*** Failed" e then
      (test_results.failed <- test_results.failed+1; found_result := true) end;
    process_otl_aux() in
  try process_otl_aux ()
  with End_of_file ->
    if not !found_result then begin
      highlight Failure "Test neither 'Passed' nor 'Failed'";
      test_results.inconclusive <- test_results.inconclusive + 1
      end;
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
  Sys.chdir here;
  confirm_results e

let remove_vo v =
  if Filename.check_suffix v ".v" then
    let vo = Filename.chop_suffix v ".v" ^ ".vo" in
    if Sys.file_exists vo then begin
      debug "Removing %s\n" vo;
      ignore (Sys.command ("rm " ^ vo))
    end

let write_file out_file out_data =
  debug "Writing to file: %s\n" out_file;
  let out_channel = open_out out_file in
  output_string out_channel out_data;
  close_out out_channel;
  remove_vo out_file;
  out_file

let write_tmp_file out_data =
  let vf = Filename.temp_file "QuickChick" ".v" in
  write_file vf out_data

let coqc_single_cmd vf = Printf.sprintf "coqc -w none -Q . Top %s" vf

let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  s

let rec catMaybes = function
  | [] -> []
  | Some x :: t -> x :: catMaybes t
  | None :: t -> catMaybes t

(* ----------------------------------------------------------------- *)
(* Parsing *)

let is_dir f =
  (* This is just in case the file has disappeared between the time we
     listed the outer directory and the time we need to test whether one
     of its members is a subdirectory.  Surprisingly, this can happen
     pretty often with emacs temp files... *)
  try Sys.is_directory f
  with Sys_error _ -> false

let rec parse_file_or_dir file_name =
  try
    debug "[parse_file_or_dir %s]\n" file_name;
    if is_dir file_name then begin
      if is_prefix tmp_dir (Filename.basename file_name)
      then None else begin
        let ls = Sys.readdir file_name in
        if !verbose then begin
          Printf.printf "Directory contains: \n";
          Array.iter (fun s -> Printf.printf "  %s\n" s) ls
        end;
        let parsed = List.map (fun s -> parse_file_or_dir
          (file_name ^ "/" ^ s)) (Array.to_list ls) in
        Some (Dir (file_name, catMaybes parsed))
      end
    end
    else if Filename.basename file_name = "Makefile" || Filename.basename file_name = "_CoqProject" then
      let s = load_file file_name in
      Some (File (file_name, [Section ("(*", "__default__" ^ file_name, "*)", None, [Text s])]))
    else
      let handle = Filename.check_suffix file_name "v" in
      if handle then begin
        debug "In file: %s\n" file_name;
        let lexbuf = Lexing.from_channel (open_in file_name) in
        let result = try program lexer lexbuf
                     with exn -> (Printf.printf "Parse error when reading file: %s\n" file_name; raise exn) in
        let collapse l =
          let rec loop acc acc_text l =
            match l with
            | Text s :: l' -> loop acc (s :: acc_text) l'
            | n :: l' ->
               let text_acc_node = Text (String.concat "" (List.rev acc_text)) in
               loop (n :: text_acc_node :: acc) [] l'
            | [] ->
               let text_acc_node = Text (String.concat "" (List.rev acc_text)) in
               text_acc_node :: acc

          in List.rev (loop [] [] l) in

        let result = List.map (fun (Section (a,b,c,d,e)) -> Section (a,b,c,d,collapse e)) result in

        let fix_extends extends =
          Str.split (Str.regexp "[ \r\n\t]") (String.concat "" extends) in
        let result = List.map
          (fun (Section (a,b,c,exts,e)) ->
            Section (a,b,c,
                     (match exts with
                     | Some (start, names, endc) -> Some (start, fix_extends names, endc)
                     | None -> None),
                     e)
          ) result in
        let fixed_default =
          match result with
          | (Section (a,b,c,exts,e) :: ss) ->
            Section ("(*", "__default__" ^ file_name, "*)", exts, e) :: ss
          | _ -> failwith "Empty section list?" in

        Some (File (file_name, fixed_default))
      end
      else None
  with Sys_error e -> failwith ("Sys_error " ^ e)

(* ----------------------------------------------------------------- *)
(* Main function *)

let rec section_length_of_fs fs =
  match fs with
  | File (_, ss) -> List.length ss
  | Dir (_, fss) -> List.fold_left (+) 0
    (List.map section_length_of_fs fss)

let trim s =
  match Str.split (Str.regexp "[ \r\n\t]") s with
  | [] -> ""
  | h :: _ -> h

(* Create a table of sections *)
let sec_find sec_graph s =
  try Hashtbl.find sec_graph (trim s)
  with Not_found -> failwith (Printf.sprintf "Didn't find: %s\n" s)

let build_sec_graph fs =
  let sec_graph = Hashtbl.create (section_length_of_fs fs) in

  let rec populate_hashtbl_sections (sections : section list) =
    match sections with
    | [] -> ()
    | Section (_, sn, _, extopt, _) :: rest ->
      let extends = match extopt with
        | Some (_, x, _) -> x
        | None -> [] in
      Hashtbl.add sec_graph (trim sn) extends;
      populate_hashtbl_sections rest in

  let rec populate_hashtbl (fs : section list file_structure) =
    (* Populate based on an entire file structure *)
    begin match fs with
      | File (_, ss) -> populate_hashtbl_sections ss
      | Dir (_, fss) -> List.iter populate_hashtbl fss
    end in

  populate_hashtbl fs;
  sec_graph

(* Decide whether to handle a section (mutate/uncomment quickChicks) *)
let rec handle_section' sec_graph current_section starting_section =
  let current_section  = trim current_section in
  let starting_section = trim starting_section in
  current_section = starting_section
  || List.exists
    (fun starting_section' ->
      handle_section' sec_graph current_section starting_section')
    (sec_find sec_graph starting_section)

let rec handle_section sec_graph sn' =
  (* Printf.printf "Asking for %s\n" sn'; flush_all (); *)
  let sn' = trim sn' in
  match !sec_name with
  | Some sn -> handle_section' sec_graph sn' sn
  | None    -> true

let calc_dir_mutants sec_graph fs =
  let all_things_to_check = ref [] in
  let rec loop fs =
    match fs with
    | File (s, ss) ->
      (* Printf.printf "Calc mutants for file: %s\n" s; flush_all (); *)
      begin match mutate_outs (handle_section sec_graph) ss with
      | base :: muts, things_to_check ->
        (* Printf.printf "Number of mutants: %d\n" (List.length muts); *)
        all_things_to_check := (List.map (fun x -> (s,x)) things_to_check)
                               @ !all_things_to_check;
        (* debug "Number of tests: %d\n%s\n" (List.length things_to_check) (String.concat "\n" things_to_check); *)
        (File (s, base), List.map (fun m -> File (s, m)) muts)
      | _ -> failwith "no base mutant"
      end
    | Dir (s, fss) -> begin
      (* Printf.printf "Calc mutants for dir: %s\n" s; flush_all (); *)
      let bmfs = List.map loop fss in
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
      | base :: muts ->
        (Dir (s, base), List.map (fun m -> Dir (s, m)) muts)
      | [] ->
        failwith "no base dir mutant"
      end
    end in
  let result = loop fs in
  (result, !all_things_to_check)

(* BCP: This function is too big! And there's too much duplication. *)
let main =
  (*  Parsing.set_trace true; *)
  let fs = from_Some (parse_file_or_dir ".") in

  (* Fill the hashtable *)
  let sec_graph = build_sec_graph fs in

  (* Hashtbl.iter (fun a b -> Printf.printf "%s -> %s\n" a
      (String.concat ", " b)) sec_graph; flush_all ();  *)

  match fs with
  | File (s, ss) ->
     failwith ". can never be a file. Right?"
(*
    let (base,muts) = match mutate_outs (handle_section sec_graph) ss with
      | (base :: muts), _ -> (base, muts)
      | _ -> failwith "empty mutants" in
    (* BCP: I think we should not test the base when testing mutants *)
    (* LEO: Really? I think it's a good baseline. Bug in base -> No point
       in testing mutants... *)
    (* BCP: OK, doing it first is fine.  But we also want to be able to
       run a single mutant by name. *)
    highlight Header "Testing base...";
    let base_file = write_tmp_file base in
    compile_and_run "." (coqc_single_cmd base_file) ExpectOnlySuccesses;
    List.iteri (fun i m ->
      (if i > 0 then Printf.printf "\n");
      highlight Header (Printf.sprintf "Testing mutant %d..." i);
      reset_test_results();
      compile_and_run "." (coqc_single_cmd (write_tmp_file m)) ExpectSomeFailure
    ) muts
 *)
  | Dir (s, fss) -> begin
    let ((base, dir_mutants), all_things_to_check) = calc_dir_mutants sec_graph fs in
    (* List.iter (fun (s1,s2) -> Printf.printf "To test: %s - %s\n" s1 s2) all_things_to_check;*)
    let rec output_mut_dir tmp_dir fs =
      match fs with
      | File (s, out_data) ->
        let out_data =
          if Filename.basename s = "_CoqProject" then
            out_data ^ "\n" ^ temporary_file ^ "\n"
          else out_data in
        let out_file = tmp_dir ^ "/" ^ s in

        if not (Sys.file_exists out_file) || load_file out_file <> out_data then
          ignore (write_file out_file out_data)

      | Dir (s, fss) -> begin
        let dir_name = tmp_dir ^ "/" ^ s in
        if (ensure_dir_exists dir_name) <> 0 then
          failwith ("Could not create directory: " ^ dir_name)
        else List.iter (output_mut_dir tmp_dir) fss
      end in

    let all_vs = gather_all_vs (Dir (s, fss)) in
    let extractions = List.map (fun s -> Filename.basename s) all_vs in
    let mk_import s =
      let splits = List.tl (Str.split (Str.regexp "/") s) in
      String.concat "." splits in

    let imports = List.map (fun s -> (if !top = "" then "" else !top ^ ".") ^ (mk_import s)) all_vs in

    let (test_names, tests) =
      let make_test i (f, s) : string * string =
        let s = let s = trim s in String.sub s 0 (String.length s - 1) in
        let testname =
          (* Leo: better qualification *)
          trim (Filename.basename (Filename.chop_suffix f ".v")) ^ "." ^ s in
        (Printf.sprintf "test%d" i,
         Printf.sprintf "Definition test%d := print_extracted_coq_string (\"Checking %s...\" ++ newline ++ show (quickCheck %s))%%string.\n"
           i testname testname) in
      List.split (List.mapi make_test all_things_to_check) in

    let tmp_file_data =
      "Set Warnings \"-extraction-opaque-accessed,-extraction\".\n\n" ^
      "Require Import String.\n"^
      "From QuickChick Require Import QuickChick.\n\n"^
      "Require " ^ (String.concat " " imports) ^ ".\n\n" ^

      (String.concat "\n" tests) ^ "\n" ^

      "Separate Extraction " ^ (String.concat " " extractions) ^ " " ^ (String.concat " " test_names) ^  ".\n" in

    ensure_tmpdir_exists();
    ignore (write_file (tmp_dir ^ "/" ^ temporary_file) tmp_file_data);

    (* Base mutant *)
    highlight Header "Testing base...";
    (* Entire file structure is copied *)
    output_mut_dir tmp_dir base;
    let dir = tmp_dir ^ "/" ^ s in
    compile_and_run dir ExpectOnlySuccesses;

    (* For each mutant structure *)
    List.iteri
      (fun i m ->
        begin
          Printf.printf "\n";
          highlight Header (Printf.sprintf "Testing mutant %d..." i);
          ensure_tmpdir_exists();
          (* Entire file structure is copied *)
          output_mut_dir tmp_dir m;
          reset_test_results();
          compile_and_run dir ExpectSomeFailure
        end)
      dir_mutants
  end;

  if !something_failed then begin
    highlight Failure "[Unexpected result for at least one test. Exiting with status 1...]";
    exit 1
  end
