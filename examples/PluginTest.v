From QuickChick Require Import QuickChick.
Require Import String. Open Scope string.

Import GenLow GenHigh.
Require Import List.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.

Definition backGen :=
  backtrack [ (1, returnGen None) 
            ; (4, returnGen (Some 42))
            ; (4, bindGen (arbitrary : G bool) (fun b => returnGen (if b then Some 0 else None))) ].

Definition prop :=
  forAll backGen (fun x => collect x true).

(* Should be 3-1 ratio *)
(* QuickChick prop. *)

Inductive Foo :=
| Foo1 : Foo
| Foo2 : Foo -> Foo
| Foo3 : nat -> Foo -> Foo -> Foo.

DeriveShow Foo as "showFoo".
Print showFoo.

DeriveArbitrary Foo as "arbFoo".
Print arbFoo.

Inductive Bar A B :=
| Bar1 : Bar A B
| Bar2 : Bar A B -> Bar A B
| Bar3 : A -> B -> Bar A B -> Bar A B.

DeriveShow Bar as "showBar".
Print showBar.

DeriveArbitrary Bar as "arbBar".
Print arbBar.

Definition testGen : G (Bar nat nat) := arbitrary.
Sample testGen.

Arguments Bar3 {A} {B}  _ _ _.
DeriveArbitrary Bar as "arbBar2".
Print arbBar2.

Inductive goodFoo' (n : nat) : Foo -> Prop :=
| Good1' : _W 1  -> goodFoo' n Foo1
| Good2' : _W 4  -> forall foo, goodFoo' 0 foo -> goodFoo' n (Foo2 foo)
| Good3' : _Size -> forall foo2,
            goodFoo' n foo2 ->
            goodFoo' n (Foo3 n Foo1 foo2).

DeriveGenerators goodFoo' as "goodFoo" and "g".
Print goodFoo.


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

(*
Inductive goodFoo : nat -> Foo -> Prop :=
    Good1 : forall n : nat, goodFoo n Foo1
  | Good2 : forall (n : nat) (foo : Foo),
            goodFoo 0 foo -> goodFoo n (Foo2 foo)
  | Good3 : forall (n : nat) (foo2 : Foo),
            goodFoo n foo2 -> goodFoo n (Foo3 n Foo1 foo2)
Go

Algorithm: to generate forall m, {foo | goodFoo m foo}

  * Keep _compile time_ map var -> unknown/fixed
  * Need to identify basic/non-basic type
    -> Non-basic = type contains non-Type arguments

  (- means compile time, + means runtime)

  + Pick a constructor (e.g. Good3) with frequency
  - Match arguments of result type (m <-> n, foo <-> Foo3 n Foo1 foo2)
    -> we only get equality constraints, maybe fail (need option)
  + For each non-basic precondition:
    * if all arguments fixed -> call decidable instance
    * if not, require 1 non-fixed. call arbitrary for { a | P a}

    For example, at goodFoo n foo2, n is fixed (equal to m) and foo2 
    is not. That means we call arbitrary {foo2 | goodFoo n foo2}
  

*)
Fixpoint genGoodFooTarget (sz : nat) (m : nat) : G (option {foo | goodFoo m foo}) :=
  match sz with
    | O => backtrack [(1, returnGen (Some (exist (goodFoo m) Foo1 (Good1 m))))] (* base case *)
    | S sz' =>
      (* Internally m -> fixed *)
      (* Backtracking choice *)
      backtrack
        [ (* Good1 *)
          (* Match m <-> n, foo <-> Foo1.  *)
          (* Result: n fixed (= m), foo fixed (=Foo1) *)
          (* No non basic types, everything fixed *)
          (1, returnGen (Some (exist (goodFoo m) Foo1 (Good1 m))))
        ; (* Good2 *)
          (* Match m <-> n, foo <-> Foo2 foo' *)
          (* Result n fixed =m, foo tbg based on foo' *)
          (4, 
          (* Generate goodFoo 0 foo *)
           bindGen (genGoodFooTarget sz' 0) (fun res0 =>
           match res0 with 
             | Some (exist foo2 goodFoo2) =>
               (* Done *)
               returnGen (Some (exist (goodFoo m) (Foo2 foo2) (Good2 m foo2 goodFoo2)))
             | None => returnGen None
           end)
          )
        ; (sz, (* Good3 *)
          (* Match m <-> n, foo <-> Foo3 n Foo1 foo2 *)
          (* Generate goodFoo n foo2 *)
          bindGen (genGoodFooTarget sz' m) (fun res0 =>
          match res0 with 
            | Some (exist foo2 goodFoo2) =>
              (* Done *)
              returnGen (Some (exist (goodFoo m) (Foo3 m Foo1 foo2)
                                     (Good3 m foo2 goodFoo2)))
            | None => returnGen None
          end)
          )
        ]
  end.

Sample (genGoodFooTarget 3 3).

From mathcomp.ssreflect Require Import ssreflect ssrnat ssrbool.
Set Bullet Behavior "Strict Subproofs".

Fixpoint goodFooSize foo := 
  match foo with
    | Foo1 => 1
    | Foo2 x => 1 + goodFooSize x
    | Foo3 x x0 x1 => 1 + goodFooSize x0 + goodFooSize x1
  end.

(* Manual completeness proof *)
Theorem genFooComplete (size m : nat) : 
  semGenSize (genGoodFooTarget size m) size <--> 
             fun (x : option {foo | goodFoo m foo}) => 
               match x with 
                 | Some (exist foo _) => goodFooSize foo <= size
                 | _ => false
               end.
Admitted.

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

