From QuickChick Require Import QuickChick.

Derive EnumSizedSuchThat for (fun n => eq x n).

Inductive nostutter {X:Type} : list X -> Prop :=
  | nostutter0: nostutter nil
  | nostutter1 n : nostutter (n::nil)
  | nostutter2 a b r :  a <> b -> nostutter (b::r) -> nostutter (a::b::r).

Derive DecOpt for (nostutter l).
Derive EnumSizedSuchThat for (fun l => nostutter l).
Derive ArbitrarySizedSuchThat for (fun l => nostutter l).
