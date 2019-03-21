Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import Omega.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrnat ssrbool eqtype div.

(* N.B.: this pulls in [ExtrOcamlString] (ExtractionQC also does) *)

From QuickChick Require Import RoseTrees RandomQC GenLow GenHigh SemChecker.
From QuickChick Require Import Show Checker State Classes.

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import List.
Import ListNotations.

Require Import Recdef.

Require Import Arith.EqNat.

Import GenLow GenHigh.

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
  compFun    : nat -> nat -> nat -> nat -> nat
}.

Definition updMaxSize (a : Args) (x : nat) : Args := 
  let '(MkArgs r msc md msh msz c cf) := a in 
  MkArgs r msc md msh x c cf.

Definition updMaxSuccess (a : Args) (x : nat) : Args := 
  let '(MkArgs r msc md msh msz c cf) := a in 
  MkArgs r x md msh msz c cf.

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

Definition roundTo n m := mult (Nat.div n m) m.

Definition computeSizeFun maxSize maxSuccess (n : nat) (d : nat) : nat :=
  if (roundTo n (maxSize) <= maxSuccess) || (n >= maxSuccess)
     || (maxSuccess %| (maxSize))
  then
    minn (n %% (maxSize) + d %/ 10) (maxSize)
  else
    minn ((n %% (maxSize)) * maxSize %/
      ((maxSuccess) %% (maxSize) + d %/ 10)) (maxSize).

Definition computeSize' a n d := computeSizeFun (maxSize a) (maxSuccess a) n d.

Definition stdArgs := MkArgs None defNumTests defNumDiscards
                             defNumShrinks defSize true computeSizeFun.

Definition at0 (f : nat -> nat -> nat) (s : nat) (n d : nat) :=
  if andb (beq_nat n 0) (beq_nat d 0) then s
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

Local Open Scope string.
Fixpoint concatStr (l : list string) : string :=
  match l with
    | nil => ""
    | (h :: t) => h ++ concatStr t
  end.

Definition summary (st : State) : list (string * nat) :=
  let res := Map.fold (fun key elem acc => (key,elem) :: acc) (labels st) nil
  in insSortBy (fun x y => snd y <= snd x) res .

Definition doneTesting (st : State) : Result :=
 if expectedFailure st then
    Success (numSuccessTests st + 1) (numDiscardedTests st) (summary st)
            ("+++ Passed " ++ (show (numSuccessTests st)) ++ " tests (" ++ (show (numDiscardedTests st)) ++ " discards)")
  else
    NoExpectedFailure (numSuccessTests st) (summary st)
                      ("*** Failed! Passed " ++ (show (numSuccessTests st))
                                             ++ " tests (expected Failure)").
  (* TODO: success st - labels *)

Definition giveUp (st : State) : Result :=
  GaveUp (numSuccessTests st) (summary st)
         ("*** Gave up! Passed only " ++ (show (numSuccessTests st)) ++ " tests"
          ++  newline ++ "Discarded: " ++ (show (numDiscardedTests st))).

Definition callbackPostTest (rs: RandomSeed) (st : State) (res : Checker.Result) : nat :=
  match res with
  | MkResult o e r i s c t =>
    fold_left (fun acc callback =>
                 match callback with
                 | PostTest _ call =>
                   (call st rs (MkSmallResult o e r i s t)) + acc
                 | _ => acc
                 end) c 0
  end.
  

Definition callbackPostFinalFailure (rs: RandomSeed) (st : State) (res : Checker.Result)
: nat :=
match res with
  | MkResult o e r i s c t =>
  fold_left (fun acc callback =>
               match callback with
                 | PostFinalFailure _ call =>
                   (call st rs (MkSmallResult o e r i s t)) + acc
                 | _ => acc
               end) c 0
end.

Fixpoint localMin (rs : RandomSeed) (st : State) (r : Rose Checker.Result)
         {struct r} : (nat * Checker.Result) :=
  match r with
  | MkRose res ts =>
    let fix localMin' st ts {struct ts} :=
        match ts return (nat * Checker.Result) with
        | nil =>
          let zero := callbackPostFinalFailure rs st res in
          (numSuccessShrinks st + zero, res)
        | cons ((MkRose res' _) as r') ts' =>
          let zero := callbackPostTest rs st res in 
          match ok res' with
            | Some x =>
              let consistent_tags := 
                match result_tag res, result_tag res' with 
                | Some t1, Some t2 => if string_dec t1 t2 then true else false
                | None, None => true
                | _, _ => false
                end in
              if andb (negb x) consistent_tags then
                localMin rs (updSuccessShrinks st (fun x => x + 1 + zero))
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
  if maxSteps is maxSteps'.+1 then
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
    | MkState mst mdt ms cs nst ndt ls e r nss nts =>
      let rnd1_copy := copySeed rnd1 in
      match f size rnd1 with
      | MkProp (MkRose res ts) =>
        (* TODO: CallbackPostTest *)
        let res_cb := callbackPostTest rnd1_copy st res in
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
            test (MkState mst mdt ms cs (nst + 1) ndt ls' e rnd2 nss nts)
          else (* Failure *)
            let tag_text := 
                match t with 
                | Some s => "Tag: " ++ s ++ nl
                | _ => "" 
                end in 
            let pre : string := (if expect res then "*** Failed "
                                 else "+++ Failed (as expected) ")%string in
            let (numShrinks, res') := localMin rnd1_copy st (MkRose res ts) in
            let suf := ("after " ++ (show (S nst)) ++ " tests and "
                                 ++ (show numShrinks) ++ " shrinks. ("
                                 ++ (show ndt) ++ " discards)")%string in
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
          test (MkState mst mdt ms cs nst ndt.+1 ls' e rnd2 nss nts)
        end
      end
    end
  else giveUp st.

Definition test (st : State) (f : nat -> RandomSeed -> QProp) : Result :=
  if (gte (numSuccessTests st) (maxSuccessTests st)) then
    doneTesting st
  else if (gte (numDiscardedTests st) (maxDiscardedTests st)) then
         giveUp st
  else
    let maxSteps := maxSuccessTests st + maxDiscardedTests st in
    runATest st f maxSteps.

Require Import ZArith.

(* ZP: This was quickCheckResult before but since we always return result
       return result there is no reason for such distinction *)
Definition quickCheckWith {prop : Type} {_ : Checkable prop}
           (a : Args) (p : prop) : Result :=
  (* ignore terminal - always use trace :D *)
  let (rnd, computeFun) :=
      match replay a with
        | Some (rnd, s) => (rnd, at0 (computeSize' a) s)
        | None          => (newRandomSeed, compFun a (maxSize a) (maxSuccess a))
        (* make it more random...? need IO action *)
      end in
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
       ) (run (checker p)).

Fixpoint showCollectStatistics (l : list (string * nat)) :=
  match l with
    | nil => ""
    | cons (s,n) l' =>
      show n ++ " : " ++ s ++ newline ++ showCollectStatistics l'
  end.

Instance showResult : Show Result := Build_Show _ (fun r =>
  match r with
  | Success _ _ l s => showCollectStatistics l ++ s
  | GaveUp _ l s => showCollectStatistics l ++ s
  | Failure _ _ _ _ _ s l _ => showCollectStatistics l ++ s
  | NoExpectedFailure _ l s => showCollectStatistics l ++ s
  end ++ newline).

Definition quickCheck {prop : Type} {_ : Checkable prop}
           (p : prop) : Result :=
  quickCheckWith stdArgs p.

Definition computeSizeFuzz (maxSize maxSuccess n d : nat) := maxSize.

Definition fuzzCheck {prop : Type} {_ : Checkable prop} (p : prop) : Result :=
  quickCheckWith (MkArgs None 1 1 0 defSize true computeSizeFuzz) p.


(* HACK! This will be implemented by appending it to the beginning of the file...*)
Axiom withInstrumentation : (unit -> option bool) -> (option bool * (bool * nat)).
Extract Constant withInstrumentation => "withInstrumentation".

Fixpoint pick_next_aux pick_fuel {A} (gen : G A) (fuzz : A -> G A) fs ds fsq dsq :=
  match pick_fuel with
  | O => (gen, fs, ds, fsq, dsq)
  | S pick_fuel =>
    match fs with
    (* First pick: something from the favorite queue.
       If its weight is 0, try the next one. *)
    | ((O, fav)::fs') =>
      pick_next_aux pick_fuel gen fuzz fs' ds fsq dsq
    | ((S n, fav)::fs') =>
      (fuzz fav, (n, fav)::fs', ds, fsq, dsq)
    | [] =>
      (* Then: If no favorites exist, check if there are still favorites in the queue. *)
      match fsq with
      (* If not, go to the discards. *)
      | [] => 
        match ds with
        (* If we have fuzzed this (discarded) seed to completion, randomly generate a new test. *)
        | ((O, _)::ds') => (gen, fs, ds', fsq, dsq)
        | ((S n, dis)::ds') => (fuzz dis, fs, ((n, dis):: ds'), fsq, dsq)
        | [] =>
          (* If no discards, look at the queue. *)
          match dsq with
          (* No queue -> Random generation *)
          | [] => (gen, [], [], [], [])
          (* Discarded in queue: update queue. *)
          | _  => pick_next_aux pick_fuel gen fuzz [] dsq [] []
          end
        end
      (* If yes, updated the favored list. *)
      | _ => pick_next_aux pick_fuel gen fuzz fsq ds [] dsq
      end
    end
  end.

Definition pick_next := @pick_next_aux 4.

Axiom printnvb : unit -> nat.
Extract Constant printnvb => "(fun u -> Printf.printf ""%d\n"" (count_non_virgin_bytes u); 42)".
Definition doneTestingFuzz (x : nat) st := doneTesting st.

(* Keep two lists for seeds: 
   favored  : contains _successful_ runs and their energy.
   discards : contains _discarded_ runs and their energy (lower priority)

   Always fuzz a favored one if it exists.
   If not, interleave fuzzing a discard or generating randomly.
*)
Fixpoint fuzzLoopAux {A} (fuel : nat) (st : State)
         (favored : list (nat * A)) (discards : list (nat * A))
         (favored_queue : list (nat * A)) (discard_queue : list (nat * A))
         (gen : G A) (fuzz : A -> G A) (print : A -> string)
         (prop : A -> option bool) :=
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
    let '(g,favored',discards',favored_queue', discard_queue') :=
        pick_next gen fuzz favored discards favored_queue discard_queue in
    let a := run g size rnd1 in
    (* TODO: These recursive calls are a place to hold depth/handicap information as well.*)
    let '(res, (is_interesting, energy)) := withInstrumentation (fun _ : unit => prop a) in
    let zero_0 := 0 in (* trace (show res ++ nl) 0 in*)
    match res with                                                     
      | Some true =>
        if is_interesting then
          (* Successful and interesting, keep in favored queue! *)
          fuzzLoopAux fuel' (updSuccTests st S) favored' discards' ((energy, a)::favored_queue') discard_queue' gen fuzz print prop
        else
          (* Successful but no new paths, don't keep. *)
          fuzzLoopAux fuel' (updSuccTests st S) favored' discards' favored_queue' discard_queue' gen fuzz print prop
      | Some false =>
        let '(MkState mst mdt ms cs nst ndt ls e r nss nts) := st in
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
        if is_interesting then
          (* Interesting (new path), but discard. Put in discard queue *)
          fuzzLoopAux fuel' (updDiscTests st S) favored' discards' favored_queue' ((energy, a)::discard_queue') gen fuzz print prop 
          (* fuzzLoopAux fuel' (updDiscTests st S) favored' discards' favored_queue' discard_queue' gen fuzz print prop  *)
        else
          (* Not interesting + discard. Throw away. *)
          fuzzLoopAux fuel' (updDiscTests st S) favored' discards' favored_queue' discard_queue' gen fuzz print prop
    end
  end.

Definition fuzzLoopWith {A} (a : Args)
         (gen : G A) (fuzz : A -> G A) (print : A -> string)
         (prop : A -> option bool) :=
  let (rnd, computeFun) := (newRandomSeed, compFun a (maxSize a) (maxSuccess a)) in
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
  in fuzzLoopAux (maxSuccess a + maxDiscard a) st [] [] [] [] gen fuzz print prop.

Definition fuzzLoop {A} := @fuzzLoopWith A stdArgs.
