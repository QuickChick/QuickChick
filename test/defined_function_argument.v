From QuickChick Require Import QuickChick.

Definition mg (a x : nat) := a + x.

(* The second hypothesis passes a defined function application to R. It is a
   value argument, not an applied type: the generator checks it with R's
   checker and derives no EnumSized instance for [mg a x]. *)
Inductive R : nat -> nat -> bool -> Prop :=
| R0 : forall a, R a a true
| RC : forall a x t,
    R a x t -> R (mg a x) x t -> R a (S x) t.

QCDerive Generator for (fun x => R a x t).

Goal True.
  lazymatch (eval unfold GenSizedSuchThatR in GenSizedSuchThatR) with
  | context [mg] => exact I
  | _ => fail "the generator does not check R (mg a x) x t"
  end.
Qed.
