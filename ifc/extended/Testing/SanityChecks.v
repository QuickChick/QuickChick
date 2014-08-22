Require Import QuickChick.

Require Import Reachability.
Require Import Printing.
Require Import SingleStateArb.
Require Import Indist.
Require Import Shrinking.
Require Import Generation.
Require Import Machine.

Require Import List. Import ListNotations.
Require Import Common.
Require Import String.

Require Import ssreflect ssrbool eqtype.

Local Open Scope string.

Section Checkers.
  Context {Gen : Type -> Type}
          {H : GenMonad Gen}.

  Definition prop_stamp_generation (st : State) : Property Gen :=
    (* whenFail (show st) *) (property (well_formed st)).

  (*
  Definition propStampGeneration (st : State) :=
    let stamps := generateStamps st in
    whenFail (Property.trace ("Generated: " ++ nl ++
                             (showStamps (allocated (st_mem st)) stamps)))
             (wellFormed st stamps).
  *)

  Definition prop_generate_indist : Property Gen :=
    forAllShrink show gen_variation_state (fun _ => []) (* shrinkVState *)
                 (fun v => let '(Var lab st1 st2) := v in
                  property (indist lab st1 st2) : Gen QProp).

  Definition prop_fstep_preserves_well_formed (t : table) : Property Gen :=
    forAllShrink (* show *)(fun _ => ""%string) arbitrary (fun _ => []) (fun st =>
    (if well_formed st then
      match fstep t st with
      | Some st' =>
(*
        whenFail ("Initial: " ++ show st ++ nl ++
                  "Step to: " ++ show st' ++ nl)
*)
                 (property (well_formed st'))
      | _ => property rejected
      end
    else property false) : Gen QProp).

End Checkers.

(* Q: Split off into a separate file with Proofs? *)
Require Import EndToEnd SetOfOutcomes.

(* This is trivial, but it was mentioned below so I've proved it *)
Lemma prop_stamp_generation_equiv :
  semTestable (prop_stamp_generation : State -> Pred QProp) <->
  (forall st, @genState Pred _ st -> well_formed st).
Proof.
  rewrite /prop_stamp_generation /semTestable /property /testFun.
  rewrite semForAllShrink. split => H st gen.
  - specialize (H st gen). by move /semPredQProp/semBool in H.
  - rewrite semPredQProp. apply /semBool. apply H. exact gen.
Qed.

(* One more rather trivial one;
   TODO both these would become more interesting if we had declarative
        variants of well_formed and indist *)
Lemma prop_generate_indist_equiv :
  semTestable (prop_generate_indist : Pred QProp) <->
  (forall lab st1 st2,
     @gen_variation_state Pred _ (Var lab st1 st2) -> indist lab st1 st2).
Proof.
  rewrite /prop_generate_indist. rewrite semPredQProp.
  setoid_rewrite semForAllShrink.
  split => [H lab st1 st2 gen | H [lab st1 st2] gen].
  - specialize (H (Var lab st1 st2) gen). red in H.
    by move /semPredQProp/semBool in H.
  - rewrite semPredQProp. apply semBool. by apply H.
Qed.

(* One direction of this (soundness) is checked by prop_stamp_generation above;
   this is the high-level spec we need for genState
   TODO: move this to GenerationProofs? *)
Lemma genState_well_formed : forall st,
  @genState Pred _ st <-> well_formed st.
Admitted.

Definition fstep_preserves_well_formed t : Prop := forall st st',
  well_formed st ->
  fstep t st = Some st' ->
  well_formed st'.

Lemma prop_fstep_preserves_well_formed_equiv :
  forall (t : table),
    semProperty (@prop_fstep_preserves_well_formed Pred _ t) <->
    fstep_preserves_well_formed t.
Proof.
  move => t.
  rewrite /prop_fstep_preserves_well_formed /fstep_preserves_well_formed
    semForAllShrink /arbitrary /arbState. setoid_rewrite semPredQProp.
  split => [H st st' wf ex | H st arb].
  - assert (@genState Pred _ st) as gs by (by rewrite genState_well_formed).
    specialize (H st gs).
    rewrite wf ex in H.
    (* by move /semWhenFail_id /semBool in H. *)    
    by apply semBool in H.
  - move /genState_well_formed in arb. rewrite arb. specialize (H st).
    move : H. case (fstep t st) => [ st' | ] H.
    + specialize (H st' arb Logic.eq_refl). rewrite H.
      (* rewrite semWhenFail_id. by rewrite <- semBool. *)
      by apply <- semBool.
    + fold (semTestable rejected). rewrite semResult. reflexivity.
Qed.
