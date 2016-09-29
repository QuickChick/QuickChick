From QuickChick Require Import QuickChick.
Require Import String. Open Scope string.

Inductive Foo :=
| Foo1 : Foo
| Foo2 : Foo -> Foo
| Foo3 : nat -> Foo -> Foo -> Foo.

DeriveShow Foo as "showFoo".
Print showFoo.

DeriveArbitrary Foo as "arbFoo".
Print arbFoo.

Inductive Bar A :=
| Bar1 : Bar A
| Bar2 : Bar A -> Bar A
| Bar3 : A -> A -> Bar A -> Bar A.

DeriveShow Bar as "showBar".
Print showBar.

DeriveArbitrary Bar as "arbBar".
Print arbBar.

Definition testGen : G (Bar nat) := arbitrary.
Sample testGen.

Arguments Bar3 {A} _ _ _.
DeriveArbitrary Bar as "arbBar2".
Print arbBar2.

Inductive goodFoo : nat -> Foo -> Prop :=
    Good1 : forall n : nat, goodFoo n Foo1
  | Good2 : forall (n : nat) (foo : Foo),
            goodFoo 0 foo -> goodFoo n (Foo2 foo)
  | Good3 : forall (n : nat) (foo2 : Foo),
            goodFoo n foo2 -> goodFoo n (Foo3 n Foo1 foo2).

Require Import List.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.

Fixpoint genGoodFooS (sz : nat) (n : nat) : G {foo | goodFoo n foo} :=
  match sz with
    | O => returnGen (exist (goodFoo n) Foo1 (Good1 n))
    | S sz' =>
      freq [ (1, returnGen (exist (goodFoo n) Foo1 (Good1 n)))
           ; (4, bindGen (genGoodFooS sz' 0) (fun foo => 
                 let (f, bf) := foo in 
                 returnGen (exist (goodFoo n) (Foo2 f) (Good2 n f bf))))
           ; (sz,let f1 := Foo1 in
                 bindGen (genGoodFooS sz' n) (fun foo2 =>
                 let (f2, bf2) := foo2 in
                 returnGen (exist (goodFoo n) (Foo3 n f1 f2) 
                                  (Good3 n f2 bf2))))
           ]
  end.

Inductive goodFoo' (n : nat) : Foo -> Prop :=
| Good1'' : _W 1  -> goodFoo' n Foo1
| Good2'' : _W 4  -> forall foo, goodFoo' 0 foo -> goodFoo' n (Foo2 foo)
| Good3'' : _Size -> forall foo2,
            goodFoo' n foo2 ->
            goodFoo' n (Foo3 n Foo1 foo2).

DeriveGenerators goodFoo' as "goodFooDerived" and "g".
Print goodFooDerived.

From mathcomp.ssreflect Require Import ssreflect ssrnat ssrbool.
Set Bullet Behavior "Strict Subproofs".

Definition dec_good_foo n f : decidable (goodFoo n f).
  move: n.
  induction f => m.
  - left; constructor.
  - move: (IHf 0) => [? | ?].
    + left; constructor; auto.
    + right => H; inversion H; subst; eauto.
  - destruct (Arith.Peano_dec.eq_nat_dec m n).
    + subst.
      destruct f1.
      * { move: (IHf2 n) => [? | ?].
          - left; constructor; auto.
          - right => H; inversion H; auto.
        } 
      * right => H; inversion H.
      * right => H; inversion H.
    + right => H; inversion H; subst; auto.
Qed.

Require Import DecidableClass.

Program Instance Decidable_good_foo (n : nat) (f : Foo) : Decidable (goodFoo n f) :=
  {| Decidable_witness :=
       let fix aux f n :=
           match f with
             | Foo1 => true
             | Foo2 f' => aux f' 0
             | Foo3 m f1 f2 =>
               match f1 with
                 | Foo1 => (eqn m n) && (aux f2 m)
                 | _ => false
               end
           end in
       aux f n
  |}.
Next Obligation.
move : n.
induction f => m; split => H; simpl; auto; try solve [constructor; auto].
- constructor; eapply IHf; eauto.
- inversion H; subst; eauto.
  eapply IHf in H2; eauto.
- destruct f1; try congruence.
  move: H => /Bool.andb_true_iff [/eqtype.eqP ? H]; subst.
  econstructor. eapply IHf2; eauto.
- inversion H; subst; simpl; eauto.
  unfold andb.
  assert (Eq : eqn n n)
    by (rewrite eqnE; apply eqtype.eq_refl).
  rewrite Eq; clear Eq.
  eapply IHf2 in H2; eauto.
Qed.

