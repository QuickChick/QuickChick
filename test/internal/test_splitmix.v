(** Test SplitMix implementation against some hardcoded result *)

From Coq Require Import List ZArith.
From QuickChick Require Import SplitMix QuickChick.

Import CoqInt64.
Import ListNotations.

Definition next (s : state) : int64 * state :=
  let g := gamma s in
  let s1 := (seed s + g)%int64 in
  (mix64_variant13 s1, SplitMix.MkState s1 g).

Definition example : list int64 :=
  let split := SplitMix.split in
  let g0 := of_seed 33 in
  let '(n0, g0) := next g0 in
  let '(n1, g0) := next g0 in
  let '(g1, _g0) := split g0 in
  let '(n2, g1) := next g1 in
  let '(g2, g1) := split g1 in
  let '(n3, g1) := next g1 in
  let '(g3, g2) := split g2 in
  let '(n4, g2) := next g2 in
  let '(n5, g2) := next g2 in
  let '(n6, g3) := next g3 in
  let '(n7, g3) := next g3 in
  let '(n8, g3) := next g3 in
  (* Run mix_gamma many times to trigger the gamma-fixing branch. *)
  let g3' := Z.iter 300 (fun g => let '(g, _) := split g in g) g3 in
  let '(n9, _g3) := next g3' in
  [n0; n1; n2; n3; n4; n5; n6; n7; n8; n9].

Lemma example_correct : example =
  [ 3174492301114349736
  ; 1387786489429541378
  ; 2612135949649290519
  ; -6594435460564017959
  ; 6114845654480584590
  ; -3434961282303982149
  ; -4710980162942128616
  ; -5883331640739962744
  ; 7437753320184232638
  ; -2875907909505887564 ]%int64.
Proof. cbv. reflexivity. Qed.
