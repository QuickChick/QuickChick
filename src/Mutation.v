Require Extraction.

(* Simple mutation testing framework for Coq.

   A Gallina expression [a] with one or more mutants [b] or
   [b1 .. bn] can be written as follows:

       mutant! a b
       mutants! a (b1, .. , bn)

   In an interactive session, [mutant! a b] and
   [mutants! a (b1, .. , bn)] both reduce to [a] (mutations
   are ignored).

   In extracted OCaml code however, those mutations can be
   selected via the environment variable [QC_MUTANT]. *)

(* - If [QC_MUTANT] is empty, the program executes normally,
     without mutations.
   - If [QC_MUTANT=DISCOVERY], the program executes normally,
     but also writes identifiers for reachable mutants into
     a file [./qc-mutants].
   - If [QC_MUTANT=(mutantid)] where [(mutantid)] is one of those
     identifiers, the program executes using that mutation.

   A typical usage is to run the program once with [DISCOVERY]:

       $ QC_MUTANT=DISCOVERY ./MyTestProgram

   Then we can test each mutant using [xargs]:

       $ cat qc-mutants|xargs -I {} -n 1 env QC_MUTANT={} ./MyTestProgram

   Mutants can also be enumerated statically by looking for the
   [__POS__] token in the extracted OCaml source code.

   The script [quickchick-expectfailure] (under [scripts/]) can be used to
   ensure a QuickChick test fails.

       $ cat qc-mutants|xargs -I {} -n 1 env quickchick-expectfailure ./MyTestProgram {}

   Note that definitions should not be simplified using [Eval] for
   this to work...
 *)

(** * Implementation. *)

Module Magic.

Parameter loc : Type.
Parameter HERE : loc.

Definition mutation : loc -> bool := fun _ => false.

Definition mutate : forall a, loc -> (unit -> a) -> (unit -> a) -> a :=
  fun _ l f g => if mutation l then g tt else f tt.

Extract Constant loc => "string * int * int * int".

Extract Inlined Constant HERE => "__POS__".

Extract Constant mutation =>
  "let serialize_loc (locf,locl,locc,_) =
     Printf.sprintf ""%s:%d:%d"" locf locl locc in 
   match Sys.getenv_opt ""QC_MUTANT"" with
   | None -> fun _ -> false
   | Some ""DISCOVERY"" ->
     let mutant_log = open_out ""qc-out/qc-mutants"" in
     let mutants = Hashtbl.create 10 in
     fun loc ->
        begin match Hashtbl.find_opt mutants loc with
        | None ->
            Hashtbl.add mutants loc ();
            output_string mutant_log (serialize_loc loc);
            output_char mutant_log '\n';
            flush mutant_log
        | Some () -> ()
        end; false
   | Some this_mutant ->
     (* print_string this_mutant; *) (* Debugging *)
     fun loc -> serialize_loc loc = this_mutant".

End Magic.

Notation "'mutant!' a b" :=
  (Magic.mutate _ Magic.HERE (fun _ => a) (fun _ => b))
(at level 1, a at level 1, no associativity).

Notation "'mutants!' a ( b1 , .. , bn )" :=
  (mutant!
     ( .. (mutant! a bn) .. )
     b1)
(at level 1, a at level 1, no associativity).
