From Coq Require Import Init.Nat.
Open Scope nat_scope.
From QuickChick Require Import QuickChick.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.


Inductive member : nat -> list nat -> Prop :=
| MemMatch : forall n xs, member n (n::xs)
| MemRecur : forall n n' xs,
    member n xs -> member n (n'::xs).
Derive DecOpt for (member n xs).

Inductive lset : list nat -> Prop :=
| Empty : lset []
| Cons : forall n xs,
           not (member n xs) ->
           lset xs ->
           lset (n::xs).
Derive DecOpt for (lset l).
(* Doesn't work *)
(* Derive ArbitrarySizedSuchThat for (fun l => lset l). *)
(* Also doesn't work *)
(* Derive ArbitrarySizedSuchThat for (fun x => not (eq x x')). *)

Fixpoint insert a xs :=
  match xs with
  | [] => [a]
  | x::xs' => if x =? a then x::xs' else
              x :: (insert a xs')
  end.

Conjecture insertcorrect : forall xs x,
    lset xs ->
    lset (insert x xs).
QuickChick insertcorrect.
