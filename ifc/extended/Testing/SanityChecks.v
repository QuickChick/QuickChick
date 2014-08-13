Require Import QuickChick.

Require Import Reachability.
Require Import Printing.
Require Import SingleStateArb.
Require Import Indist.
Require Import Shrinking.
Require Import Generation.

Require Import Machine.
Import Mem.

Require Import List.
Require Import Common.
Require Import String.

Require Import ssreflect ssrbool eqtype.

Local Open Scope string.

(* Sanity check for stamp generation *)
Definition prop_stamp_generation (st : State) : Property Gen.Gen :=
  whenFail (show st) (well_formed st).

(*
Definition propStampGeneration (st : State) :=
  let stamps := generateStamps st in
  whenFail (Property.trace ("Generated: " ++ nl ++
                           (showStamps (allocated (st_mem st)) stamps)))
           (wellFormed st stamps).
*)

Definition prop_generate_indist : Property Gen.Gen :=
  forAllShrink show gen_variation_state (fun _ => []) (* shrinkVState *)
               (fun v => let '(Var lab st1 st2) := v in
                property (indist lab st1 st2) : Gen.Gen QProp).

Section Checkers.
  Context {Gen : Type -> Type}
          {H : GenMonad Gen}.

  Definition prop_exec_preserves_well_formed (t : table)
  : Property Gen :=
    forAllShrink show arbitrary (fun _ => []) (fun st =>
    (if well_formed st then
      match exec t st with
      | Some (_, st') =>
        whenFail ("Initial: " ++ show st ++ nl ++
                  "Step to: " ++ show st' ++ nl)
                 (well_formed st')
      | _ => property rejected
      end
    else property false) : Gen QProp).

End Checkers.

Definition exec_preserves_well_formed t : Prop := forall st x st',
  well_formed st ->
  exec t st = Some (x, st') ->
  well_formed st'.

Require Import EndToEnd SetOfOutcomes.

(* One direction of this (soundness) checked by prop_stamp_generation above;
   this is the high-level spec we need for genState *)
Lemma genState_well_formed : forall st,
  @genState Pred _ st <-> well_formed st.
Admitted.

Lemma prop_exec_preserves_well_formed_equiv:
  forall (t : table),
    semProperty (@prop_exec_preserves_well_formed Pred _ t) <->
    exec_preserves_well_formed t.
Proof.
  move => t.
  rewrite /prop_exec_preserves_well_formed /exec_preserves_well_formed
    semForAllShrink /arbitrary /arbState. setoid_rewrite semPredQProp.
  split => [H st tr st' wf ex | H st arb].
  - assert (@genState Pred _ st) as gs by (by rewrite genState_well_formed).
    specialize (H st gs).
    rewrite wf ex in H. by move /semWhenFail_idemp /semBool in H.
  - move /genState_well_formed in arb. rewrite arb. specialize (H st).
    move : H. case (exec t st) => [ [tr st'] | ] H.
    + specialize (H tr st' arb Logic.eq_refl). rewrite H.
      rewrite semWhenFail_idemp. by rewrite <- semBool.
    + fold (semTestable rejected). rewrite <- semResult. reflexivity.
Qed.
