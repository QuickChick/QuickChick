From Coq Require Import Bool ZArith Ascii String List.
Import ListNotations.

From ExtLib Require Import
     Structures.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

From SimpleIO Require Import SimpleIO.

From QuickChick Require Import RoseTrees RandomQC Generators Producer SemChecker.
From QuickChick Require Import Show Checker State Classes.

Definition gte n m := Nat.leb m n.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Record Args := MkArgs {
  replay     : option (RandomSeed * nat);
  maxSuccess : nat;
  maxDiscard : nat;
  maxShrinks : nat;
  maxSize    : nat;
  chatty     : bool;
  analysis   : bool
}.

Definition updMaxSize (a : Args) (x : nat) : Args := 
  let '(MkArgs r msc md msh msz c an) := a in 
  MkArgs r msc md msh x c an.

Definition updMaxSuccess (a : Args) (x : nat) : Args := 
  let '(MkArgs r msc md msh msz c an) := a in 
  MkArgs r x md msh msz c an.

Definition updAnalysis (a : Args) (b : bool) : Args := 
  let '(MkArgs r msc md msh msz c an) := a in 
  MkArgs r msc md msh msz c b.


Inductive Result :=
  | Success : nat -> nat -> list (string * nat) -> string -> Result
  | GaveUp  : nat -> list (string * nat) -> string -> Result
  | Failure : nat -> nat -> nat -> RandomSeed -> nat -> string ->
              list (string * nat) -> string -> Result
  | NoExpectedFailure : nat -> list (string * nat) -> string -> Result.

Definition isSuccess (r : Result) : bool :=
  match r with
    | Success _ _ _ _ => true
    | _         => false
  end.

(* Representing large constants in Coq is not a good idea... :) *)
Axiom defNumTests    : nat.
Extract Constant defNumTests    => "10000".
Axiom defNumDiscards : nat.
Extract Constant defNumDiscards => "(2 * defNumTests)".
Axiom defNumShrinks  : nat.
Extract Constant defNumShrinks  => "1000".
Axiom defSize        : nat.
Extract Constant defSize        => "7".
Definition doAnalysis       := false.

Definition stdArgs := MkArgs None defNumTests defNumDiscards
                             defNumShrinks defSize true doAnalysis.

Definition roundTo n m := (n / m) * m.

(* This matches the formula in Haskell QuickCheck *)
Definition computeSize'' (maxSize_ maxSuccess_ n d : nat) : nat :=
  if (roundTo n maxSize_ + maxSize_ <=? maxSuccess_)
  || (maxSuccess_ <=? n)
  || (maxSuccess_ mod maxSize_ =? 0)
  then
    min (n mod maxSize_ + d / 10) maxSize_
  else
    min ((n mod maxSize_) * maxSize_ /
      (maxSuccess_ mod maxSize_ + d / 10)) maxSize_.

Definition computeSize' (a : Args) (n : nat) (d : nat) : nat :=
  computeSize'' (maxSize a) (maxSuccess a) n d.

Definition at0 (f : nat -> nat -> nat) (s : nat) (n d : nat) :=
  if andb (Nat.eqb n 0) (Nat.eqb d 0) then s
  else f n d.

Fixpoint prependToAll {A : Type} (sep : A) (ls : list A) : list A :=
  match ls with
    | nil => nil
    | h :: t => sep :: h :: prependToAll sep t
  end.

Definition intersperse {A : Type} (sep : A) (ls : list A) : list A :=
  match ls with
    | nil => nil
    | h :: t => h :: prependToAll sep t
  end.

Definition notNull (ls : list string) : bool :=
  match ls with
    | nil => false
    | _ => true
  end.

Fixpoint insertBy A (compare : A -> A -> bool) (x : A) (l : list A) : list A :=
  match l with
    | nil => x :: nil
    | h :: t => if compare x h then x :: l else h :: insertBy compare x t
  end.

Fixpoint insSortBy A (compare : A -> A -> bool) (l : list A) : list A :=
  match l with
    | nil => nil
    | h :: t => insertBy compare h (insSortBy compare t)
  end.

Fixpoint concatStr (l : list string) : string :=
  match l with
    | nil => ""
    | (h :: t) => h ++ concatStr t
  end%string.

Definition summary (st : State) : list (string * nat) :=
  let res := Map.fold (fun key elem acc => (key,elem) :: acc) (labels st) nil
  in insSortBy (fun x y => snd y <=? snd x) res.

Definition doneTesting (st : State) : Result :=
 if expectedFailure st then
    Success (numSuccessTests st + 1) (numDiscardedTests st) (summary st)
            (
              if (stDoAnalysis st) 
                then ("""result"": ""success"", ""tests"": " ++ (show (numSuccessTests st)) ++ ", ""discards"": " ++ (show (numDiscardedTests st)))
                else ("+++ Passed " ++ (show (numSuccessTests st)) ++ " tests (" ++ (show (numDiscardedTests st)) ++ " discards)" ++ newline)
            )

  else
    NoExpectedFailure (numSuccessTests st) (summary st)
                  (
                    if (stDoAnalysis st) 
                      then ("""result"": ""expected_failure"", ""tests"": " ++ (show (numSuccessTests st)))
                      else ("*** Failed! Passed " ++ (show (numSuccessTests st))++ " tests (expected Failure)" ++ newline)
                  ).
  (* TODO: success st - labels *)

Definition giveUp (st : State) : Result :=
  GaveUp (numSuccessTests st) (summary st)
          (
            if (stDoAnalysis st) 
              then ("""result"": ""gave_up"", ""tests"":" ++ (show (numSuccessTests st)) ++ ", ""discards"": " ++ (show (numDiscardedTests st)))
              else ("*** Gave up! Passed only " ++ (show (numSuccessTests st)) ++ " tests" ++ 
                    newline ++ "Discarded: " ++ (show (numDiscardedTests st)) ++ newline)
          ).
Definition callbackPostTest (st : State) (res : Checker.Result) : nat :=
  match res with
  | MkResult o e r i s c t =>
    fold_left (fun acc callback =>
                 match callback with
                 | PostTest _ call =>
                   (call st (MkSmallResult o e r i s t)) + acc
                 | _ => acc
                 end) c 0
  end.
  

Definition callbackPostFinalFailure (st : State) (res : Checker.Result)
: nat :=
match res with
  | MkResult o e r i s c t =>
  fold_left (fun acc callback =>
               match callback with
                 | PostFinalFailure _ call =>
                   (call st (MkSmallResult o e r i s t)) + acc
                 | _ => acc
               end) c 0
end.

Fixpoint localMin (st : State) (r : Rose Checker.Result)
         {struct r} : (nat * Checker.Result) :=
  match r with
  | MkRose res ts =>
    let fix localMin' st ts {struct ts} :=
        match ts return (nat * Checker.Result) with
        | nil =>
          let zero := callbackPostFinalFailure st res in
          (numSuccessShrinks st + zero, res)
        | cons ((MkRose res' _) as r') ts' =>
          let zero := callbackPostTest st res in 
          match ok res' with
            | Some x =>
              let consistent_tags := 
                match result_tag res, result_tag res' with 
                | Some t1, Some t2 => if string_dec t1 t2 then true else false
                | None, None => true
                | _, _ => false
                end in
              if andb (negb x) consistent_tags then
                localMin (updSuccessShrinks st (fun x => x + 1 + zero))
                         r'
              else
                localMin' (updTryShrinks st (fun x => x + 1)) ts'
            | None =>
              localMin' (updTryShrinks st (fun x => x + 1)) ts'
          end
        end in
    localMin' st (force ts)
  end.

Fixpoint runATest (st : State) (f : nat -> RandomSeed -> QProp) (maxSteps : nat) :=
  match maxSteps with
  | S maxSteps' =>
    let size := (computeSize st) (numSuccessTests st) (numDiscardedTests st) in
    let (rnd1, rnd2) := randomSplit (randomSeed st) in
    let test (st : State) :=
        if (gte (numSuccessTests st) (maxSuccessTests st)) then
          doneTesting st
        else if (gte (numDiscardedTests st) (maxDiscardedTests st)) then
               giveUp st
             else runATest st f maxSteps'
    in
    match st with
    | MkState mst mdt ms cs nst ndt ls e r nss nts ana stime =>
      match f size rnd1 with
      | MkProp (MkRose res ts) =>
        (* TODO: CallbackPostTest *)
        let res_cb := callbackPostTest st res in
        match res with
        | MkResult (Some x) e reas _ s _ t =>
          if x then (* Success *)
            let ls' := 
                match s with 
                | nil => ls 
                | _ => 
                  let s_to_add := 
                      ShowFunctions.string_concat 
                        (ShowFunctions.intersperse " , "%string s) in
                  match Map.find s_to_add ls with 
                    | None   => Map.add s_to_add (res_cb + 1) ls
                    | Some k => Map.add s_to_add (k+1) ls
                  end 
                end in
(*                  
            let ls' := fold_left (fun stamps stamp =>
                                    let oldBind := Map.find stamp stamps in
                                    match oldBind with
                                    | None   => Map.add stamp 1 stamps
                                    | Some k => Map.add stamp (k+1) stamps
                                    end
                                 ) s ls in*)
            test (MkState mst mdt ms cs (nst + 1) ndt ls' e rnd2 nss nts ana stime)
          else (* Failure *)
            let tag_text := 
                match t with 
                | Some s => "Tag: " ++ s ++ nl
                | _ => "" 
                end in 
            let pre : string := (
                                  if ana 
                                    then (
                                      if expect res then """result"": ""failed"", "
                                      else """result"": ""expected_failure"" "
                                    )
                                    else (
                                      if expect res then "*** Failed "
                                      else "+++ Failed (as expected) "
                                    )
                                 )%string in
            let (numShrinks, res') := localMin st (MkRose res ts) in
            let suf := (
                        if ana 
                          then (
                              """tests"": " ++ (show (S nst)) ++ ", ""shrinks"": "
                              ++ (show numShrinks) ++ ", ""discards"": "
                              ++ (show ndt)
                            )
                          else (
                              "after " ++ (show (S nst)) ++ " tests and "
                              ++ (show numShrinks) ++ " shrinks. ("
                              ++ (show ndt) ++ " discards)"
                            )
                        )%string in
            (* TODO: Output *)
            if (negb (expect res)) then
              Success (nst + 1) ndt (summary st) (tag_text ++ pre ++ suf)
            else
              Failure (nst + 1) numShrinks ndt r size (tag_text ++ pre ++ suf) (summary st) reas
        | MkResult None e reas _ s _ t =>
          (* Ignore labels of discarded tests? *)
          let ls' :=
              match s with
              | nil => ls
              | _ =>
                let s_to_add :=
                    "(Discarded) " ++ ShowFunctions.string_concat
                                    (ShowFunctions.intersperse " , "%string s) in
                match Map.find s_to_add ls with
                | None   => Map.add s_to_add (res_cb + 1) ls
                | Some k => Map.add s_to_add (k+1) ls
                end
              end in
          test (MkState mst mdt ms cs nst (S ndt) ls' e rnd2 nss nts ana stime)
        end
      end
    end
  | 0 => giveUp st
  end%string.

Definition test (st : State) (f : nat -> RandomSeed -> QProp) : Result :=
  if (gte (numSuccessTests st) (maxSuccessTests st)) then
    doneTesting st
  else if (gte (numDiscardedTests st) (maxDiscardedTests st)) then
    giveUp st
  else
    let maxSteps := maxSuccessTests st + maxDiscardedTests st in
    runATest st f maxSteps.

Axiom getCurrentTime : unit -> Z.
Extract Constant getCurrentTime => "(fun tt -> let start = Unix.gettimeofday () in Big_int_Z.big_int_of_int (Float.to_int start))".

(* ZP: This was quickCheckResult before but since we always return result
       return result there is no reason for such distinction *)
Definition quickCheckWith {prop : Type} {_ : Checkable prop}
           (a : Args) (p : prop) : Result :=
  (* ignore terminal - always use trace :D *)
  let (rnd, computeFun) :=
      match replay a with
        | Some (rnd, s) => (rnd, at0 (computeSize' a) s)
        | None          => (newRandomSeed, computeSize' a)
        (* make it more random...? need IO action *)
      end in
  let start_time := getCurrentTime tt in
  test (MkState (maxSuccess a)  (* maxSuccessTests   *)
                (maxDiscard a)  (* maxDiscardTests   *)
                (maxShrinks a)  (* maxShrinks        *)
                computeFun      (* computeSize       *)
                0               (* numSuccessTests   *)
                0               (* numDiscardTests   *)
                (Map.empty nat) (* labels            *)
                false           (* expectedFailure   *)
                rnd             (* randomSeed        *)
                0               (* numSuccessShrinks *)
                0               (* numTryShrinks     *)
                (analysis a)  (* analysisFlag      *)
                start_time
       ) (run (checker p)).

Fixpoint showCollectStatistics (l : list (string * nat)) : string :=
  match l with
    | nil => ""
    | cons (s,n) l' =>
      show n ++ " : " ++ s ++ newline ++ showCollectStatistics l'
  end.

#[global]
Instance showResult : Show Result := Build_Show _ (fun r =>
  match r with
  | Success _ _ l s => showCollectStatistics l ++ s
  | GaveUp _ l s => showCollectStatistics l ++ s
  | Failure _ _ _ _ _ s l _ => showCollectStatistics l ++ s
  | NoExpectedFailure _ l s => showCollectStatistics l ++ s
  end)%string.

Definition quickCheck {prop : Type} {_ : Checkable prop}
           (p : prop) : Result :=
  quickCheckWith stdArgs p.

(* A named test property with parameters. *)
Inductive Test : Type :=
| QuickChickTest : string -> Args -> Checker -> Test.

(* Make a named test property with explicit parameters. *)
Definition qc_ {prop : Type} {_ : Checkable prop}
           (name : string) (a : Args) (p : prop) : Test :=
  QuickChickTest name a (checker p).

(* Make a named test property with implicit default parameters. *)
Definition qc {prop : Type} {_ : Checkable prop}
           (name : string) (p : prop) : Test :=
  qc_ name stdArgs (checker p).

(* IO action that runs the tests. *)
Fixpoint testRunner (tests : list Test) : IO unit :=
  match tests with
  | [] => ret tt
  | QuickChickTest name args test :: tests =>
    print_endline ("Checking " ++ name ++ "...");;
    print_endline (show (quickCheckWith args test));;
    testRunner tests
  end%string.

(* Actually run the tests. (Only meant for extraction.) *)
Definition runTests (tests : list Test) : io_unit :=
  IO.unsafe_run (testRunner tests).

(* Fuzzing parts *)

Definition fuzzCheck {prop : Type} {_ : Checkable prop} (p : prop) : Result :=
  quickCheckWith (MkArgs None 1 1 0 defSize true false) p.

(* HACK! This will be implemented by appending it to the beginning of the file...*)
Axiom withInstrumentation : (unit -> option bool) -> (option bool * (bool * nat)).
Extract Constant withInstrumentation => "withInstrumentation".

(* After this many random consecutive tests, control flow returns to saved seeds. *)
Axiom random_fuel : nat.
Extract Constant random_fuel => "1000".

Fixpoint pick_next_aux pick_fuel {A} (gen : G A) (fuzz : A -> G A) fs ds fsq dsq randoms saved :=
  match pick_fuel with
  | O => (gen, fs, ds, fsq, dsq, randoms, saved)
  | S pick_fuel =>
    match fs with
    (* First pick: something from the favorite queue.
       If its weight is 0, try the next one. *)
    | ((O, fav)::fs') =>
      pick_next_aux pick_fuel gen fuzz fs' ds fsq dsq randoms saved
    | ((S n, fav)::fs') =>
      (fuzz fav, (n, fav)::fs', ds, fsq, dsq, randoms, saved)
    | [] =>
      (* Then: If no favorites exist, check if there are still favorites in the queue. *)
      match fsq with
      (* If not, go to the discards. *)
      | [] => 
        match ds with
        (* If we have fuzzed this (discarded) seed to completion, randomly generate a new test. *)
        | ((O, _)::ds') => (gen, fs, ds', fsq, dsq, randoms, saved)
        | ((S n, dis)::ds') => (fuzz dis, fs, ((n, dis):: ds'), fsq, dsq, randoms, saved)
        | [] =>
          (* If no discards, look at the queue. *)
          match dsq with
          (* No queue -> Random generation *)
          | [] =>
            (* Check if we've exhausted the random fuel *)
            match randoms with
            (* If we run out of random fuel, try restoring the saved queue *)
            | O => pick_next_aux pick_fuel gen fuzz saved [] [] [] random_fuel saved
            | S randoms' => (gen, [], [], [], [], randoms', saved)
            end
          (* Discarded in queue: update queue. *)
          | _  => pick_next_aux pick_fuel gen fuzz [] dsq [] [] randoms saved
          end
        end
      (* If yes, updated the favored list. *)
      | _ => pick_next_aux pick_fuel gen fuzz fsq ds [] dsq randoms saved
      end
    end
  end.

Definition pick_next := @pick_next_aux 7.

Axiom printnvb : unit -> nat.
Extract Constant printnvb => "(fun u -> Printf.printf ""%d\n"" (count_non_virgin_bytes u); 42)".
Definition doneTestingFuzz (x : nat) st := doneTesting st.

Axiom clear_queues : nat -> bool.
Extract Constant clear_queues => "(fun n -> n land 1023 == 0)".

(* Keep two lists for seeds: 
   favored  : contains _successful_ runs and their energy.
   discards : contains _discarded_ runs and their energy (lower priority)

   Always fuzz a favored one if it exists.
   If not, interleave fuzzing a discard or generating randomly.
*)
Fixpoint fuzzLoopAux {A} (fuel : nat) (st : State)
         (favored : list (nat * A)) (discards : list (nat * A))
         (favored_queue : list (nat * A)) (discard_queue : list (nat * A))
         (randoms : nat) (saved : list (nat * A))
         (gen : G A) (fuzz : A -> G A) (print : A -> string)
         (prop : A -> option bool) : Result :=
  match fuel with
  | O => giveUp st 
  | S fuel' => 
    if (gte (numSuccessTests st) (maxSuccessTests st)) then
      let x : nat := printnvb tt in
      doneTestingFuzz (trace (show x) x) st
    else if (gte (numDiscardedTests st) (maxDiscardedTests st)) then
      giveUp st
    else 
    let size := (computeSize st) (numSuccessTests st) (numDiscardedTests st) in
    let (rnd1, rnd2) := randomSplit (randomSeed st) in
    (* How to decide between generation and fuzzing? *)
    (* For now, if there is a succesful seed, use it.
       If there is not, pick the first discarded one, fuzz it until
       you run out of energy, and then generate a random test again.
     *)
    let '(g,favored',discards',favored_queue', discard_queue', randoms', saved') :=
        pick_next gen fuzz favored discards favored_queue discard_queue randoms saved in
    let a := run g size rnd1 in
    (* TODO: These recursive calls are a place to hold depth/handicap information as well.*)
    let '(res, (is_interesting, energy)) := withInstrumentation (fun _ : unit => prop a) in
    let zero_0 := 0 in (* trace (show res ++ nl) 0 in*)
    match res with                                                     
    | Some true =>
      match clear_queues fuel with
      | true => fuzzLoopAux fuel' (updSuccTests st S) nil nil nil nil randoms' nil gen fuzz print prop
      | _ => 
        if is_interesting then
          (* Successful and interesting, keep in favored queue and save! *)
          fuzzLoopAux fuel' (updSuccTests st S) favored' discards' ((energy, a)::favored_queue') discard_queue' randoms' ((energy,a) :: saved') gen fuzz print prop
        else
          (* Successful but no new paths, don't keep. *)
          fuzzLoopAux fuel' (updSuccTests st S) favored' discards' favored_queue' discard_queue' randoms' saved' gen fuzz print prop
      end
    | Some false =>
        let '(MkState mst mdt ms cs nst ndt ls e r nss nts ana stime) := st in
        let zero := trace (print a ++ nl) zero_0 in
        let pre : string := "*** Failed " in
        (* TODO: shrinking *)
        (*         let (numShrinks, res') := localMin rnd1_copy st (MkRose res ts) in *)
        let numShrinks := 0 in
        let suf := ("after " ++ (show (S nst)) ++ " tests and "
                                 ++ (show numShrinks) ++ " shrinks. ("
                                 ++ (show ndt) ++ " discards)")%string in
        Failure (nst + 1 + zero) numShrinks ndt r size (pre ++ suf) (summary st) "Falsified!"
    | None =>
      match clear_queues fuel with
      | true => fuzzLoopAux fuel' (updDiscTests st S) nil nil nil nil randoms' nil gen fuzz print prop
      | _ => 
        if is_interesting then
          (* Interesting (new path), but discard. Put in discard queue *)
          fuzzLoopAux fuel' (updDiscTests st S) favored' discards' favored_queue' ((energy, a)::discard_queue') randoms' saved' gen fuzz print prop 
          (* fuzzLoopAux fuel' (updDiscTests st S) favored' discards' favored_queue' discard_queue' gen fuzz print prop  *)
        else
          (* Not interesting + discard. Throw away. *)
          fuzzLoopAux fuel' (updDiscTests st S) favored' discards' favored_queue' discard_queue' randoms' saved' gen fuzz print prop
      end
    end
  end%string.

Definition fuzzLoopWith {A} (a : Args)
         (gen : G A) (fuzz : A -> G A) (print : A -> string)
         (prop : A -> option bool) :=
  let compFun maxSuccess maxSize n d := maxSize in
  let (rnd, computeFun) := (newRandomSeed, compFun (maxSize a) (maxSuccess a)) in
  let start_time := getCurrentTime tt in  
  let st := MkState (maxSuccess a)  (* maxSuccessTests   *)
                    (maxDiscard a)  (* maxDiscardTests   *)
                    (maxShrinks a)  (* maxShrinks        *)
                    computeFun      (* computeSize       *)
                    0               (* numSuccessTests   *)
                    0               (* numDiscardTests   *)
                    (Map.empty nat) (* labels            *)
                    true            (* expectedFailure   *)
                    rnd             (* randomSeed        *)
                    0               (* numSuccessShrinks *)
                    0               (* numTryShrinks     *)
                    false           (* analysis          *)
                    start_time      (* start time        *)
  in fuzzLoopAux (maxSuccess a + maxDiscard a) st [] [] [] [] random_fuel [] gen fuzz print prop.

Definition fuzzLoop {A} := @fuzzLoopWith A stdArgs.
