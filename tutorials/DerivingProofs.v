From Coq Require Import Bool Lia.
From QuickChick Require Import QuickChick CheckerProofs EnumProofs.

(** * Reasoning about generators, enumerators, and checkers

QuickChick retains its semantic definitions, correctness classes, and
combinator lemmas. They can be used to prove properties of handwritten
implementations. QuickChick 3.0 does not provide automatic correctness
proofs for scheduled derivations. The old derivation proof tactics depended
on the old engine's generated terms.

The semantics [semGen g] describes the possible results of a generator,
without describing their probabilities. For example, [returnGen x] can
only produce [x]. This follows from the retained combinator lemma: *)

Example return_nat_sound (x y : nat) : semGen (returnGen x) y -> y = x.
Proof.
  intro H. apply semReturnGen in H. symmetry. exact H.
Qed.

(** [bindPf], documented as [bindGen'] for generators, passes both a
generated value and evidence that it belongs to the first generator's
semantics to its continuation. This allows the continuation to construct
data carrying a proof about the generated value. The evidence establishes
membership in the generator's outcomes; a separate correctness argument
connects those outcomes to the intended specification. *)

Definition witnessed_result {A : Type} (g : G A) : G {x : A | semGen g x} :=
  bindPf g (fun x H => returnGen (exist _ x H)).

(** ** Enumerator semantics and size

[semEnumSize e s] is the set of values in the lazy list obtained by running
[e] at size [s]. An [EnumSized] implementation has an additional explicit
size argument, commonly used to bound recursive calls. These are two
distinct bounds. [SizeMonotonic] concerns the underlying producer's size;
[SizedMonotonic] concerns the explicit argument of the sized family.

[CorrectSized] says that the union of outcomes over sizes contains every
value of the result type. [CorrectSizedST P] says that the successful
outcomes of a constrained producer are exactly the values satisfying [P].
The latter includes both soundness and completeness. These classes express
proof obligations; deriving an executable instance does not prove them.

** Checker fuel, soundness, and completeness

A [DecOpt P] supplies a function [nat -> option bool]. [None] represents
an inconclusive result. [DecOptSoundPos] says that acceptance implies [P];
[DecOptCompletePos] says that [P] is eventually accepted at some fuel.
[DecOptSizeMonotonic] says that increasing fuel preserves a conclusive
decision. Negative soundness and completeness have corresponding classes.

Here is a handwritten checker with direct proofs of these properties.
It waits for positive fuel before deciding whether a Boolean is true. *)

#[local] Instance true_checker (b : bool) : DecOpt (b = true) :=
  {| decOpt := fun fuel => match fuel with 0 => None | S _ => Some b end |}.

#[local] Instance true_checker_sound (b : bool) : DecOptSoundPos (b = true).
Proof.
  intros fuel H. destruct fuel; simpl in H; [discriminate |].
  inversion H. reflexivity.
Qed.

#[local] Instance true_checker_complete (b : bool) : DecOptCompletePos (b = true).
Proof. intro H. exists 1. simpl. now rewrite H. Qed.

#[local] Instance true_checker_monotonic (b : bool) : DecOptSizeMonotonic (b = true).
Proof.
  intros s1 s2 answer Hle Hanswer.
  destruct s1; simpl in Hanswer; [discriminate |].
  destruct s2; [lia | exact Hanswer].
Qed.

(** These proofs use the public definitions and ordinary Rocq tactics.
They do not inspect a derivation engine's generated term shape. The
libraries [GenProofs], [EnumProofs], [CheckerProofs], [Classes], and
[DependentClasses] remain available for further manual proofs. *)
