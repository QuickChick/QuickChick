From QuickChick Require Import QuickChick.
Require Import List Arith Lia.

(* quickchick on goals about functions such as List.In (issue #109). A
   premise defined by a function is checked once its variables are
   generated; conclusions combine Dec instances, including <-> and True. *)
Definition union (A B : list nat) : list nat :=
  fold_left (fun res a => if in_dec Nat.eq_dec a res then res else a :: res) A B.

Lemma union_spec : forall (x : nat) (A B : list nat),
    In x (union A B) <-> In x A \/ In x B.
Proof. quickchick. Abort.

Lemma app_spec : forall (x : nat) (A B : list nat), In x (A ++ B) -> In x A \/ In x B.
Proof. quickchick. Abort.

Lemma nested : forall (x : nat) (A B : list nat), In x A \/ In x B \/ True.
Proof. quickchick. Abort.

(* After intros, the goal is tested with the variables it mentions and the
   hypotheses about them quantified again. *)
Lemma union_spec' : forall (x : nat) (A B : list nat),
    In x (union A B) <-> In x A \/ In x B.
Proof. intros. quickchick. Abort.

Lemma app_spec' : forall (x : nat) (A B : list nat), In x (A ++ B) -> In x A \/ In x B.
Proof. intros x A B H. quickchick. Abort.

Lemma lt_weaken : forall n : nat, n < 3 -> n < 5.
Proof. intros n H. quickchick. quickchick. lia. Qed.
