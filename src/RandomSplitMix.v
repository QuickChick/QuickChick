From QuickChick Require Import SplitMix.
From QuickChick Require Export Random.

Definition seed := SplitMix.state.

CoFixpoint generate (s : seed) : random :=
  {| split := fun _ => let '(s1, s2) := SplitMix.split s in (generate s1, generate s2)
  ;  bits := fun _ => SplitMix.bits s
  |}.
Definition split_seed : seed -> seed * seed := SplitMix.split.
Parameter new_seed : unit -> seed.
