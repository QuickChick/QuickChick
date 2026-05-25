From QuickChick Require Import QuickChick.

QCDerive EnumSizedSuchThat for (fun n => eq x n).

Inductive nostutter {X:Type} : list X -> Prop :=
  | nostutter0: nostutter nil
  | nostutter1 n : nostutter (n::nil)
  | nostutter2 a b r :  a <> b -> nostutter (b::r) -> nostutter (a::b::r).

QCDerive DecOpt for (nostutter l).
QCDerive EnumSizedSuchThat for (fun l => nostutter l).
QCDerive ArbitrarySizedSuchThat for (fun l => nostutter l).
