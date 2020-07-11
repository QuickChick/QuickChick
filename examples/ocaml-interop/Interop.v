From QuickChick Require Import QuickChick.
Require Import ZArith.
Require Import String. Local Open Scope string.

Inductive foo :=
| A : Z -> foo
(* | B : string -> foo *)
| C : foo -> foo -> foo.

Derive (Arbitrary, Show) for foo.

Extract Inductive foo => "Foo.foo" [ "Foo.A" "Foo.C" ].

Axiom good_foo : foo -> bool.
Extract Constant good_foo => "Foo.good_foo".

QCInclude "ocaml/*".

QuickChick good_foo.  
