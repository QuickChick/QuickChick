(* QuickChick Prelude *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String List. Open Scope string.

From QuickChick Require Import QuickChick Tactics.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

Require Import ZoeStuff.
(* End prelude *)

Require Export Tactics.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Admitted. (* OUT-OF-SCOPE *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Admitted. (* Leo: TODO *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Admitted. (* Leo: TODO *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Admitted. (* Higher Order *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Admitted. (* Higher Order *)  

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Admitted. (* Higher Order *)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Admitted. (* Leo: TODO *)

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Admitted. (* Higher Order *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Admitted. (* QuickChick zero_or_succ. *)

Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Admitted. (* OUT-OF-SCOPE *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Admitted. (* Higher Order *)

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Admitted. (* Higher Order *)

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Admitted. (* Higher Order *)

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Admitted. (* Higher Order *)

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Admitted. (* Higher Order *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Admitted. (* QuickChick not_true_is_false. *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Admitted. (* QuickChick not_true_is_false'. *)

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Admitted. (* Higher Order *) 

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Admitted. (* Leo: TODO *) 

Theorem iff_refl : forall P : Prop,
  P <-> P.
Admitted. (* Higher Order *)

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Admitted. (* Higher Order *)

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Admitted. (* Higher Order *)

Require Import Coq.Setoids.Setoid.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Admitted. (* OUT-OF-SCOPE *)

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Admitted. (* Higher Order *)

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Admitted. (* OUT-OF-SCOPE *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Admitted. (* Existential *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Admitted. (* Existential *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Admitted. (* Existential *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Admitted. (* Existential *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Admitted. (* Leo: TODO *)

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Admitted. (* Existential *)

Lemma in_app_iff : forall A l l' (a:A),
  In a (app l l') <-> In a l \/ In a l'.
Admitted. (* Leo: TODO *)

Lemma plus_comm3 :
  forall n m p, n + (m + p) = (p + m) + n.
Admitted. (* QuickChick plus_comm3. *)

Lemma plus_comm3_take2 :
  forall n m p, n + (m + p) = (p + m) + n.
Admitted. (* QuickChick plus_comm3_take2. *)

Lemma plus_comm3_take3 :
  forall n m p, n + (m + p) = (p + m) + n.
Admitted. (* QuickChick plus_comm3_take3. *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Admitted. (* Higher Order *)

Theorem evenb_double : forall k, evenb (double k) = true.
Admitted.  (* QuickChick evenb_double. *)

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Admitted. (* Existential *) 

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Admitted. (* Existential *)

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Admitted. (* Prop *)

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Admitted. (* Prop *)

Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false <-> x <> y.
Admitted. (* Prop *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Admitted. (* Higher Order *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Admitted. (* QuickChick restricted_excluded_middle_eq. *)

Theorem excluded_middle_irrefutable:  forall (P:Prop),
  ~ ~ (P \/ ~ P).
Admitted. (* Higher Order *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Admitted. (* Existential *)
