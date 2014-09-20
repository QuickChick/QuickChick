Require Import QuickChick.
Require Import List.
Import ListNotations.
Require Import ssreflect ssrbool ssrnat.

Definition nonempty_list (a : Type) : Type := { l : list a | exists x, In x l}.


Section Generator.
  Context (Gen : Type -> Type)
          (H : GenMonad Gen).
  

Program Fixpoint gen_nonemptylist {a} `{Arbitrary a} : Gen (nonempty_list a) :=
  bindGen arbitrary (fun x =>
  bindGen (listOf arbitrary) (fun xs =>
  returnGen (x :: xs))).
Next Obligation.
  exists x. by left.
Qed.

End Generator.

Instance arbNonempty_list {a} {_ : Arbitrary a} : Arbitrary (nonempty_list a) :=
  {
    arbitrary g G := @gen_nonemptylist g G _ _;
    shrink l := []
  }.

Definition silly_prop (l : nonempty_list nat) : bool := 0 < length (proj1_sig l).

Instance shownonempty_list {a} `{Show a} : (Show (nonempty_list a)) :=
  { show := fun l => show (proj1_sig l) }.


(* Manually creating the checker *)
Section Checker.
  Context (Gen : Type -> Type)
          (H : GenMonad Gen).

Definition silly_checker : Checker Gen := forAll (@gen_nonemptylist Gen H _ _) silly_prop.

End Checker.

Require Import Gen.


Definition test0 :=
  showResult (quickCheck ((@silly_checker Gen _) : Gen QProp)).

QuickCheck test0.

(* Automatically deriving the checker *)

Definition test1 :=
  showResult (quickCheck (silly_prop)).

QuickCheck test1.