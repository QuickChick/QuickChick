From QuickChick Require Import QuickChick.
From QuickChick Require Import Test State Checker RoseTrees RandomQC.
From Coq Require Import List.
Import ListNotations.

(* Shrinking stops after maxShrinks successful shrinks (issue #293). A chain
   of three failing shrinks is followed as far as the limit allows. *)
Definition chain : Rose Checker.Result :=
  MkRose failed (lazy [MkRose failed (lazy [MkRose failed (lazy
    [MkRose failed (lazy nil)])])]).

Definition state (limit : nat) : State :=
  MkState 100 100 limit (fun _ _ => 0) 0 0 (Map.empty nat) false newRandomSeed 0 0 false.

Example no_shrinks : fst (localMin (state 0) chain) = 0.
Proof. vm_compute. reflexivity. Qed.
Example two_shrinks : fst (localMin (state 2) chain) = 2.
Proof. vm_compute. reflexivity. Qed.
Example all_shrinks : fst (localMin (state 1000) chain) = 3.
Proof. vm_compute. reflexivity. Qed.

(* updMaxShrinks sets the limit in a test's arguments. *)
Example upd_max_shrinks : maxShrinks (updMaxShrinks stdArgs 7) = 7.
Proof. reflexivity. Qed.
