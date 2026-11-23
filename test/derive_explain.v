From QuickChick Require Import QuickChick.

(* QuickChick Derive Explain derives the same instances as QuickChick Derive
   and prints the schedules it chose. *)
Inductive le' : nat -> nat -> Prop :=
| le_n' n : le' n n
| le_S' n m : le' n m -> le' n (S m).
Inductive between : nat -> nat -> nat -> Prop :=
| Btw lo x hi : le' lo x -> le' x hi -> between lo x hi.

QuickChick Derive Explain Generator for (fun x => between lo x hi).
Definition explained_generator : GenSizedSuchThat nat (fun x => between 1 x 3) :=
  ltac:(typeclasses eauto).
QC Derive Explain Checker for (between lo x hi).
Example explained_checker : decOpt (P := between 1 2 3) 10 = Some true.
Proof. reflexivity. Qed.
QuickChick Derive Explain (GenSized, EnumSized) for nat.

(* Explain is not a reserved word. *)
Definition Explain := 0.
