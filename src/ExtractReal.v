Require Import String.
Require Export Reals.
From QuickChick Require Import QuickChick.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.

Extract Constant R => "float".
Extract Constant Rplus => "(+.)".
Extract Constant Rminus => "(-.)".
Extract Constant Rabs => "abs_float".
Extract Constant Rmult => "(fun r1 r2 -> r1 *. r2)".
Extract Constant Rdiv => "(fun r1 r2 -> r1 /. r2)".
Extract Constant Ropp => "(fun r -> 0.0 -. r)".
Extract Constant Rinv => "(fun r -> 1.0 /. r)".
Extract Constant Rsqrt => "(fun r -> sqrt r)".

Extract Constant cos => "(fun r -> cos r)".
Extract Constant sin => "(fun r -> sin r)".

(* This needs to be a bool option, which is a weird type. *)
(* I think this is the result it wants for the triple option
   based on usage in the extraction *)
Extract Constant total_order_T =>
  "(fun r1 r2 -> if r1 < r2 then Some true 
                 else if r1 > r2 then None
                 else Some false)".

(* Take an arbitrary large limit...? Epsilon-delta? *)
(*
Extract Constant growing_cv => "(fun un -> un 100)".
Extract Constant Alembert_C1 => "(fun an -> an 100)".
*)

(* Ordering *)
Axiom Rleb : R -> R -> bool.
Extract Constant Rleb => "(<=)".
Axiom Rleb_refl : ssrbool.reflexive Rleb.
Axiom Rleb_trans : ssrbool.transitive Rleb.
Axiom Rleb_antisym : ssrbool.antisymmetric Rleb.
Instance ordR : OrdType R :=
  { leq := Rleb
  ; refl := Rleb_refl
  ; trans := Rleb_trans
  ; antisym := Rleb_antisym
  }.

(* Equality: HACKS! QuickChick should provide a non-proving version  of Dec *)
Axiom Reqb : R -> R -> bool.
Extract Constant Reqb => "(fun r1 r2 -> let eps = 0.000001 in r1 <= r2 +. eps && r2<= r1 +. eps)".
Axiom Reqb_refl : ssrbool.reflexive Reqb.
Axiom Reqb_trans : ssrbool.transitive Reqb.
Axiom Reqb_sym : ssrbool.symmetric Reqb.
Axiom Reqb_eq : forall (r1 r2 : R), Reqb r1 r2 = true <-> r1 = r2.

Instance Req_dec (r1 r2 : R) : Dec (r1 = r2) := {}.
Proof.
  destruct (Reqb r1 r2) eqn:Eq.
  - left; apply Reqb_eq; auto.
  - right; intro.
    apply Reqb_eq in H.
    congruence.
Defined.

(* Generation *)
Axiom randomRFloat : R * R -> RandomSeed -> R * RandomSeed.
Extract Constant randomRFloat => "QuickChickLib.randomRFloat".

Axiom randomRFloatCorrect :
  forall a a1 a2 : R,
  is_true (leq a1 a2) ->
  is_true (leq a1 a && leq a a2) <->
  (exists seed : RandomSeed, fst (randomRFloat (a1, a2) seed) = a).

Instance ChooseR : ChoosableFromInterval R :=
  {
    randomR := randomRFloat;
    randomRCorrect := randomRFloatCorrect
  }.

Instance GenR : Gen R :=
  { arbitrary := choose (R0, R1) }.

(* Printing *)
Axiom show_float : R -> string.
Extract Constant show_float =>
  "(fun i ->
  let s = Pervasives.string_of_float i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))".

Instance ShowR : Show R :=
  { show := show_float }.

Extract Constant R0 => "0.0".
Extract Constant R1 => "1.0".

(* Large number for "infinite" distance. *)
Axiom Rlarge : R.
Extract Constant Rlarge => "42424242.0".

Axiom Repsilon : R.
Extract Constant Repsilon => "0.000001".

(* Distances *)
Class Distance (A : Type) :=
  { dist : A -> A -> R }.

Instance distR : Distance R :=
  { dist := fun x y => Rabs (Rminus x y) }.

Definition checker :=
  forAll (choose (R0, R1)) (fun r1 =>
  forAll (choose (R0, R1)) (fun r2 =>
  r1 = r2?)).
(* QuickChick checker. *)

