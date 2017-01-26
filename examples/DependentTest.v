From QuickChick Require Import QuickChick Tactics.
Require Import String. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import GenLow GenHigh.
Require Import List.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

Inductive Foo :=
| Foo1 : Foo
| Foo2 : Foo -> Foo
| Foo3 : nat -> Foo -> Foo -> Foo.

Inductive goodFoo (n : nat) : Foo -> Prop :=
| Good1 : goodFoo n Foo1
| Good2 : forall foo, goodFoo 0 foo -> goodFoo n (Foo2 foo)
| Good3 : forall foo2,
            goodFoo n foo2 ->
            goodFoo n (Foo3 n Foo1 foo2).

Inductive Bar A B :=
| Bar1 : A -> Bar A B
| Bar2 : Bar A B -> Bar A B
| Bar3 : A -> B -> Bar A B -> Bar A B -> Bar A B.

Arguments Bar1 {A} {B} _.
Arguments Bar2 {A} {B} _.
Arguments Bar3 {A} {B} _ _ _ _.

Inductive goodBar (A B : Type) (n : nat) : Bar A B -> Prop :=
| Bar1 : forall a, goodBar n (Bar1a)
| Bar2 : forall bar, goodBar 0 bar -> goodBar n (Bar2 bar)
| Bar3 : forall a b bar,
            goodBar n bar ->
            goodFoo n (Bar3 a b (Bar1 a) bar).



DeriveDependent goodFoo.

