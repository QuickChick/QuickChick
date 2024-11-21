From QuickChick Require Import QuickChick.

Inductive Foo (X : Type) :=
| A : X -> Foo X
| B : X -> Foo X.

Arguments A {X}.
Arguments B {X}.
Derive Show for Foo.

Set Printing All.

(*
Definition f :=
  let fix f (x : Foo) :=
    match x with
    | A => 42
    | B => 0
    end in f A.
*)
Inductive Fooish {T} : Foo T -> Foo T -> Prop :=
| AS : forall x, Fooish (A x) (A x)
| BS : forall x y, Fooish (B x) (B y).

(*
Instance GenSizedSuchThat_foo :
  GenSizedSuchThat _ (fun '(x,y) => Fooish x y) :=
  { arbitrarySizeST := fun n => returnGen (Some (A,A)) }.

Sample (@arbitraryST _ (fun '(x,y) => Fooish x y) _).
 *)
Derive Testing for (fun '(x,y,z,w) => Fooish x y z). 
Derive Testing for (Fooish x y). 
Derive Testing for (fun x => Fooish x y). 





