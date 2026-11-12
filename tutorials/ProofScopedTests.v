From QuickChick Require Import QuickChick.

(** [quickchick] prepares and runs a test of the current goal. It leaves the
    prepared test in the proof context as [theorem], or a fresh variant if that
    name is taken. Testing does not discharge the goal. *)
Extract Constant defNumTests => "3".
Goal forall n : nat, n = n.
  quickchick 2.
  Check theorem.

  (** Give the test a descriptive local name. Rerunning it does not repeat
      schedule search or derivation. The argument controls generation size. *)
  pose (reflexivity_test := theorem).
  QuickChick (reflexivity_test 4).

  (** Existing execution settings work on saved tests too. *)
  QuickChickWith (updMaxSuccess stdArgs 2) (reflexivity_test 3).
  intros; reflexivity.
Qed.
Fail Check theorem.
Fail Check reflexivity_test.

(** Helpers and dictionaries are local definitions. They follow the proof
    context through undo and tactic backtracking and disappear when that
    context ends. A proof can retain their bodies without leaving global helper
    names behind. Explicit [Derive Inductive Schedule] commands remain global.

    A saved test keeps its original property, schedule, and selected instances.
    Changing the goal or registering another instance does not update it. Run
    [quickchick] again to prepare a test for the changed goal or context; both
    tests can coexist under different names. Local computational assumptions
    still need concrete values before extraction can execute a test. *)

(** Testing and saved-test reruns work inside ordinary and nested modules.
    Tests inside an unapplied module functor cannot run. Instantiate the functor
    first, then test its exported property from outside the functor. *)
