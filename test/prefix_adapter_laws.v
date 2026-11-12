(* Algebraic adapter laws for the typed prefix scheduler. This models the
   concat-map converter and the block-wise unconstrained-step normalizer.
   OCaml's fresh names are considered modulo alpha-renaming. *)
From Coq Require Import List Arith.
Import ListNotations.

Section StepwiseConversion.
  Context {PreStep Step : Type}.
  Variable emit : PreStep -> list Step.

  Definition convert (steps : list PreStep) := flat_map emit steps.

  Theorem convert_app : forall prefix suffix,
    convert (prefix ++ suffix) = convert prefix ++ convert suffix.
  Proof.
    intros. unfold convert. now rewrite flat_map_app.
  Qed.
End StepwiseConversion.

Inductive step :=
| Unconstrained : nat -> step
| Solid : nat -> step.

Section BlockNormalization.
  Variable sort_block : list step -> list step.
  Hypothesis sort_empty : sort_block [] = [].

  Fixpoint normalize_acc (steps block : list step) : list step :=
    match steps with
    | [] => sort_block block
    | Unconstrained n :: rest =>
        normalize_acc rest (Unconstrained n :: block)
    | Solid n :: rest =>
        sort_block block ++ Solid n :: normalize_acc rest []
    end.

  Definition normalize steps := normalize_acc steps [].

  (* The last converted step of a processed hypothesis is a producer, check,
     or match. Only terminal completion may add unconstrained steps afterward. *)
  Inductive closed_prefix : list step -> Prop :=
  | closed_one : forall n, closed_prefix [Solid n]
  | closed_cons : forall head tail,
      closed_prefix tail -> closed_prefix (head :: tail).

  Lemma closed_after_chunk : forall prefix chunk,
    closed_prefix chunk -> closed_prefix (prefix ++ chunk).
  Proof.
    intros prefix chunk Hclosed.
    induction prefix as [|head rest IH]; simpl; auto.
    now constructor.
  Qed.

  Lemma normalize_acc_app_closed : forall prefix suffix,
    closed_prefix prefix -> forall block,
    normalize_acc (prefix ++ suffix) block =
    normalize_acc prefix block ++ normalize_acc suffix [].
  Proof.
    intros prefix suffix Hclosed.
    induction Hclosed as [n|head tail Htail IH]; intros block.
    - simpl. rewrite sort_empty. now rewrite <- app_assoc.
    - destruct head as [n|n]; simpl.
      + apply IH.
      + rewrite IH. now rewrite <- app_assoc.
  Qed.

  Theorem normalize_app_closed : forall prefix suffix,
    prefix = [] \/ closed_prefix prefix ->
    normalize (prefix ++ suffix) = normalize prefix ++ normalize suffix.
  Proof.
    intros prefix suffix [Hempty|Hclosed].
    - subst. unfold normalize. simpl. now rewrite sort_empty.
    - unfold normalize. now apply normalize_acc_app_closed.
  Qed.
End BlockNormalization.

(* When a converted prefix is closed, the stepwise converter and normalizer
   jointly preserve it under later pre-schedule choices. *)
Theorem adapter_prefix_law : forall (PreStep : Type)
    (emit : PreStep -> list step) (sort_block : list step -> list step)
    (prefix suffix : list PreStep),
  sort_block [] = [] ->
  flat_map emit prefix = [] \/
    closed_prefix (flat_map emit prefix) ->
  normalize sort_block (flat_map emit (prefix ++ suffix)) =
    normalize sort_block (flat_map emit prefix) ++
    normalize sort_block (flat_map emit suffix).
Proof.
  intros PreStep emit sort_block prefix suffix Hsort Hclosed.
  rewrite flat_map_app.
  apply normalize_app_closed; assumption.
Qed.

(* Variable-use counts compare names for equality. Injective renaming of
   every binder and occurrence therefore preserves the count, including the
   running environment of earlier bindings. *)
Section AlphaVariableUses.
  Context {Name : Type}.
  Variable equal_dec : forall x y : Name, {x = y} + {x <> y}.
  Variable rename : Name -> Name.
  Hypothesis rename_injective : forall x y,
    rename x = rename y -> x = y.

  Fixpoint uses (bound reads : list Name) : nat :=
    match reads with
    | [] => 0
    | name :: rest =>
        (if in_dec equal_dec name bound then 1 else 0) + uses bound rest
    end.

  Lemma renamed_membership : forall name bound,
    In (rename name) (map rename bound) <-> In name bound.
  Proof.
    intros name bound; split.
    - intros H.
      apply in_map_iff in H as [original [Heq Hin]].
      apply rename_injective in Heq. subst. exact Hin.
    - apply in_map.
  Qed.

  Lemma uses_renaming : forall bound reads,
    uses (map rename bound) (map rename reads) = uses bound reads.
  Proof.
    intros bound reads; induction reads as [|name rest IH]; simpl; auto.
    rewrite IH.
    destruct (in_dec equal_dec name bound) as [Hin|Hnot];
      destruct (in_dec equal_dec (rename name) (map rename bound))
        as [Hrenamed|Hmissing]; try reflexivity.
    - exfalso. apply Hmissing. now apply renamed_membership.
    - exfalso. apply Hnot. now apply renamed_membership.
  Qed.

  Record use_step := {
    reads : list Name;
    binds : list Name
  }.

  Definition rename_step step := {|
    reads := map rename (reads step);
    binds := map rename (binds step)
  |}.

  Fixpoint scan_uses (bound : list Name) (steps : list use_step) : nat :=
    match steps with
    | [] => 0
    | step :: rest =>
        uses bound (reads step) +
        scan_uses (binds step ++ bound) rest
    end.

  Theorem scan_uses_alpha_invariant : forall bound steps,
    scan_uses (map rename bound) (map rename_step steps) =
    scan_uses bound steps.
  Proof.
    intros bound steps; revert bound.
    induction steps as [|step rest IH]; intros bound; simpl; auto.
    rewrite uses_renaming.
    rewrite <- map_app.
    now rewrite IH.
  Qed.
End AlphaVariableUses.
