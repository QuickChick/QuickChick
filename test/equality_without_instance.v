(* An equality check compiles to a Dec_Eq instance. When a type has none,
   QuickChick derives one with dec_eq and reports it
   (quickchick-derived-instance); when it cannot, the check is unavailable
   and that is reported (quickchick-missing-instance). *)
From QuickChick Require Import QuickChick.
Extract Constant defNumTests => "3".
Inductive opaque := Opaque : nat -> opaque.
QuickChick Derive (Arbitrary, Show) for opaque.
Inductive wrapped : opaque -> Prop := Wrapped : forall n, wrapped (Opaque n).
Inductive same : opaque -> opaque -> Prop := Same : forall x, same x x.
Definition unwrap (o : opaque) := match o with Opaque n => n end.

(* The derived instance belongs to the derivation: none is left behind. *)
QuickChick Derive Checker for (same x y).
Example same_accepts : decOpt (P := same (Opaque 1) (Opaque 1)) 3 = Some true.
Proof. reflexivity. Qed.
Example same_rejects : decOpt (P := same (Opaque 1) (Opaque 2)) 3 = Some false.
Proof. reflexivity. Qed.
Fail Definition leaked : Dec_Eq opaque := _.

(* Four theorem schedules, including one that checks same x y. *)
Goal forall x y, wrapped x -> wrapped y -> same x y -> unwrap x = unwrap y.
  quickchick_schedules.
  quickchick 2 0.
  quickchick 2 3.
  Fail quickchick 2 4.
Abort.
Fail Definition leaked_local : Dec_Eq opaque := _.

(* dec_eq cannot decide equality on functions. *)
Inductive fn_box := FnBox : (nat -> nat) -> fn_box.
Inductive same_fn : fn_box -> fn_box -> Prop := SameFn : forall x, same_fn x x.
Fail QuickChick Derive Checker for (same_fn x y).
