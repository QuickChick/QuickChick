From QuickChick Require Import QuickChick.

Inductive Foo :=
| A
| B.
Derive Show for Foo.

Inductive Fooish : Foo -> Foo -> Prop :=
| AS : Fooish A A
| BS : Fooish B B.

(*
Instance GenSizedSuchThat_foo :
  GenSizedSuchThat _ (fun '(x,y) => Fooish x y) :=
  { arbitrarySizeST := fun n => returnGen (Some (A,A)) }.

Sample (@arbitraryST _ (fun '(x,y) => Fooish x y) _).
 *)
Derive Testing for (fun '(x,y) => Fooish x y). 
Derive Testing for (fun x => Fooish x y). 

