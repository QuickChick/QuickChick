From QuickChick Require Import QuickChick Tactics.
Require Import String. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import GenLow GenHigh.
Require Import List.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

Inductive Foo :=
| Foo0 : Foo -> Foo
| Foo1 : Foo 
| Foo2 : Foo -> Foo
| Foo3 : nat -> Foo -> Foo -> Foo.

Inductive goodFoo : nat -> Foo -> Prop :=
| Good0 : forall n foo, goodFoo n (Foo0 foo) (* Need call to arbitrary *)
| Good1 : forall n, goodFoo n Foo1 (* Basic unification *)
| Good2 : forall n foo, goodFoo 0 foo -> goodFoo n (Foo2 foo)
| Good3 : forall n foo2,
            goodFoo n foo2 ->
            goodFoo (S n) (Foo3 n Foo1 foo2).

DeriveDependent goodFoo for 2 as "genGoodFoo". 

Inductive Bar A B :=
| Bar1 : A -> Bar A B
| Bar2 : Bar A B -> Bar A B
| Bar3 : A -> B -> Bar A B -> Bar A B -> Bar A B.

Arguments Bar1 {A} {B} _.
Arguments Bar2 {A} {B} _.
Arguments Bar3 {A} {B} _ _ _ _.

Inductive goodBar {A B : Type} (n : nat) : Bar A B -> Prop :=
| goodBar1 : forall a, goodBar n (Bar1 a)
| goodBar2 : forall bar, goodBar 0 bar -> goodBar n (Bar2 bar)
| goodBar3 : forall a b bar,
            goodBar n bar ->
            goodBar n (Bar3 a b (Bar1 a) bar).

DeriveDependent goodBar for 2 as "genGoodBar".