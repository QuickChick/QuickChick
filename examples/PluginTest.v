From QuickChick Require Import QuickChick Tactics.
Require Import String. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Import GenLow GenHigh.
Require Import List.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.


Set Bullet Behavior "Strict Subproofs".

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

DeriveArbitrary Foo as "arbFoo" "arbFooSized".
Print arbFoo.
Print arbFooSized.

DeriveSize Foo as "sizeFoo".
Print sizeFoo.
DeriveSizeEqs Foo as "sizedFoo".

Check (fun (x : 2 = 3) => match x with Logic.eq_refl => I end).


Lemma max_lub_l_ssr n m p:
  max n m < p -> n < p.
Proof.
  move /ltP/NPeano.Nat.max_lub_lt_iff => [/ltP H1 _].
  assumption.
Qed.

Lemma max_lub_r_ssr n m p:
  max n m < p -> m < p.
Proof.
  move /ltP/NPeano.Nat.max_lub_lt_iff => [_ /ltP H1].
  assumption.
Qed.

Lemma max_lub_ssr n m p :
  n < p -> m < p -> max n m < p.
Proof.
  move => /ltP H1 /ltP H2.
  apply/ltP/NPeano.Nat.max_lub_lt; eassumption.
Qed.

DeriveSizeEqsProof Foo as "sizedFoo".
(* Check sizedFoo_eq_proof. *)

Inductive test : Type :=
| C : nat -> bool -> test
| D : test -> nat -> test -> bool -> test -> unit -> test.
(* | C : test -> test *)

DeriveSize test as "sizeTest".
Print sizeTest. 
DeriveSizeEqs test as "sizedTest".
Print sizedTest_eqT.
DeriveSizeEqsProof test as "sizedTest".

DeriveSize list as "sizeList".
(* This is broken *)
DeriveSizeEqs list as "sizeList".
DeriveSizeEqsProof list as "sizedList".

Inductive list' (a : Type) : Type :=
| Nil : list' a
| Cons1 : a -> list' nat -> list' a.

(* This breaks CanonicalSize (and also size equation proofs) :
DeriveSize list' as "sizeList". *)


(* Zoe : Probably a good idea to generate size equations automatically. *)
(* Leo : One size equation generated :) *)
Lemma sizedFoo_eq s : sizedFoo_eqT s.
Proof.
  exact (sizedFoo_eq_proof s).
Qed.
                                             
Lemma sizedFoo_zero : sizedFoo_zeroT.
(*   [set Foo1] <--> [set foo : Foo | sizeOf foo <= 0 ].*)
Proof.
  move => [ | f | n f1 f2]; split; simpl; move => H; by firstorder.
Qed.


Lemma sizedFoo_succ s : sizedFoo_succT s.
(*   [set Foo1] :|:
  (\bigcup_(f in fun f => sizeOf f <= s) ([set Foo2 f]) :|:
    \bigcup_n ( 
      \bigcup_(f1 in fun f => sizeOf f <= s) (
         \bigcup_(f2 in fun f => sizeOf f <= s) (
            [set Foo3 n f1 f2]))))  <-->
  [set foo : Foo | sizeOf foo <= s.+1 ].
*)
Proof.
  unfold sizedFoo_succT. Set Printing All. 
  eapply (sizedFoo_eq (s.+1)).
Qed.

Instance arbFooSizeMonotonic s : SizeMonotonic (arbFooSized s).
Proof.
  induction s; try eauto with typeclass_instances.
  apply frequencySizeMonotonic; try eauto with typeclass_instances.
  repeat apply Forall_cons; eauto with typeclass_instances.
Qed.

Theorem arbFooComplete size : 
  semGen (arbFooSized size) <--> [set foo : Foo | sizeOf foo <= size].
Proof.
  induction size; simpl.
  - rewrite -sizedFoo_zero semReturn. reflexivity.
  - (* rewrite with the size lemmas *)
    rewrite -sizedFoo_succ.
    (* then rewrite with the semantics of the outermost combinators *)
    (* Frequency and some normalization of the sets *)
    rewrite semFrequency /=.
    rewrite !cons_set_eq nil_set_eq setU_set0_neut.
    rewrite !bigcup_setU_l !bigcup_set1 /=.
    (* compare the sets pairwise *)
    apply setU_set_eq_compat; [| apply setU_set_eq_compat]; try reflexivity.
    + rewrite semReturn. reflexivity.
    + rewrite -> semBindSizeMonotonic; eauto with typeclass_instances.
      rewrite IHsize.
      apply eq_bigcupr => x.
      rewrite -> semReturn. reflexivity.
    + rewrite -> semBindSizeMonotonic; eauto with typeclass_instances.
      rewrite arbNat_correct.
      apply eq_bigcupr => x.
      rewrite -> semBindSizeMonotonic; eauto with typeclass_instances.
      rewrite IHsize.
      apply eq_bigcupr => y.
      rewrite -> semBindSizeMonotonic; eauto with typeclass_instances.
      rewrite IHsize.
      apply eq_bigcupr => z.
      rewrite -> semReturn. reflexivity.
Qed.

Inductive Bar (A B : Type) :=
| Bar1 : Bar A B
| Bar2 : Bar A B -> Bar A B
| Bar3 : A -> B -> Bar A B -> Bar A B.

DeriveShow Bar as "showBar".
Print showBar.

DeriveArbitrary Bar as "arbBar" "arbBarSized".
Print arbBar.
Print arbBarSized.

Definition testGen : G (Bar nat nat) := arbitrary.
Sample testGen.

Arguments Bar3 {A} {B}  _ _ _.
DeriveArbitrary Bar as "arbBar2" "arbBarSized2".
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

Fixpoint genGoodFooTarget (sz : nat) (m : nat) : G (option Foo) :=
  match sz with
    | O => returnGen (Some Foo1)
      (* Used to be : 
         backtrack [(1, returnGen (Some Foo1))]
      *)
    | S sz' =>
      (* Internally m -> fixed *)
      (* Backtracking choice *)
      backtrack
        [ (* Good1 *)
          (* Match m <-> n, foo <-> Foo1.  *)
          (* Result: n fixed (= m), foo fixed (=Foo1) *)
          (* No non basic types, everything fixed *)
          (1, returnGen (Some Foo1))
        ; (* Good2 *)
          (* Match m <-> n, foo <-> Foo2 foo' *)
          (* Result n fixed =m, foo tbg based on foo' *)
          (4, 
          (* Generate goodFoo 0 foo *)
           bindGen (genGoodFooTarget sz' 0) (fun res0 =>
           returnGen (match res0 with 
                        | Some foo2 =>
                          (* Done *)
                          Some (Foo2 foo2)
                        | None => None
                      end))
          )
        ; (sz, (* Good3 *)
          (* Match m <-> n, foo <-> Foo3 n Foo1 foo2 *)
          (* Generate goodFoo n foo2 *)
          bindGen (genGoodFooTarget sz' m) (fun res0 =>
          returnGen (match res0 with 
                       | Some foo2 =>
                         (* Done *)
                         Some (Foo3 m Foo1 foo2)
                       | None =>None
                     end))
          )
        ]
  end.

(*
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
*)

Sample (genGoodFooTarget 3 3).

Fixpoint goodFooSize foo := 
  match foo with
    | Foo1 => 0
    | Foo2 x => 1 + goodFooSize x
    | Foo3 x x0 x1 => 1 + max (goodFooSize x0) (goodFooSize x1)
  end.

Definition lift {T} (s : set T) : set (option T) :=
  (@Some T) @: s.

Require Import Morphisms.
Instance liftProper {T} : Proper (set_eq ==> set_eq) (@lift T).
Proof.
  move => x y Heq [z |]; firstorder. 
Qed.

Lemma imset_set1 {T U} (f : T -> U) (x : T) :
  f @: [set x] <--> [set f x].
Proof.
  unfold imset. by rewrite bigcup_set1.
Qed.

Lemma lift_set1 {T} (x : T) :
  lift [set x] <--> [set Some x].
Proof.
  unfold lift. by rewrite imset_set1.
Qed.

Lemma lift_setI {T} (s1 s2 : set T) :
  (lift (s1 :&: s2)) <--> (lift s1 :&: lift s2).
Proof.
  move => [ z |] /=; firstorder.
  inv H1; inv H2. by repeat econstructor; eauto.
  by inv H1.
Qed.

Lemma lift_setU {T} (s1 s2 : set T) :
  (lift (s1 :|: s2)) <--> (lift s1 :|: lift s2).
Proof.
    by rewrite /lift /imset bigcup_setU_l.
Qed.

Lemma lift_bigcup {T U} (s1 : set T) (s2 : T -> set U) :
  lift (bigcup s1 s2) <--> (bigcup s1 (fun x => lift (s2 x))).
Proof.
  by rewrite /lift imset_bigcup. 
Qed.

Lemma semBacktrack (A : Type) (l : list (nat * G (option A))) :
  Forall (fun p => SizeMonotonic (snd p)) l -> 
  semGen (backtrack l) <-->
  let l' := [seq x <- l | fst x != 0] in
  \bigcup_(x in l')
   (isSome :&: semGen (snd x)) :|:
  [set None]
  :&: \bigcap_(x in l') (semGen (snd x)).
Admitted.
 
Lemma sizedFoo_goodFoo_eq s m :
  [set Foo1] :|:
   (\bigcup_(f in (fun f => sizedFoo f < s) :&: goodFoo 0) ([set Foo2 f]) :|:
     \bigcup_(f2 in (fun f => sizedFoo f < s) :&: goodFoo m) (
       [set Foo3 m Foo1 f2]))  <-->
  [set foo : Foo | sizedFoo foo <= s ] :&: (goodFoo m).
Proof.
  move => [| f | n f1 f2].
  + simpl; split => _; by repeat constructor.
  + simpl. split.
    * move => [ H
             | [[f' [[H1 H1'] [H2]]]
             | [f2' [Hf2 Hf2']]]];
        subst; try discriminate.
      split; eauto. by constructor.
    * move => [H1 H2]. right; left. eexists; split; last by reflexivity.
      constructor; eauto. inv H2. eassumption.
  + split.
    * move => [H
             | [[f [H1 H2]]
             | [f2' [[Hf2 Hf2'] [Heq1 Heq2 Heq3 ]]]]];
        subst; try discriminate.
      split.
      by apply/leP/NPeano.Nat.le_succ_l/NPeano.Nat.max_lub_lt; ssromega.
      by econstructor.
    * move => [ H1 H2 ]. inv H2.
      right; right. exists f2; split; eauto.
      constructor. 
      move : H1 => /leP/NPeano.Nat.le_succ_l/NPeano.Nat.max_lub_lt_iff [H1 H1'].
      by ssromega. eassumption. reflexivity.
Qed.
  

Lemma sizedFoo_goodFoo_zero :
  [set Foo1] <--> [set foo : Foo | sizedFoo foo <= 0 ].
Proof.
  move => [ | f | n f1 f2]; split; simpl; move => H; by firstorder.
Qed.

Lemma sizedFoo_goodFoo_succ s m :
  [set Foo1] :|:
   (\bigcup_(f in (fun f => sizedFoo f <= s) :&: goodFoo 0) ([set Foo2 f]) :|:
     \bigcup_(f2 in (fun f => sizedFoo f <= s) :&: goodFoo m) (
       [set Foo3 m Foo1 f2])) <-->
  [set foo : Foo | sizedFoo foo <= s.+1 ] :&: (goodFoo m).
Proof.
  setoid_rewrite <- sizedFoo_goodFoo_eq at 3. reflexivity.
Qed.


(* TODO move to gen lib *)
Lemma backtrackSizeMonotonic {A} (lg : list (nat * G (option A))) :
  Forall (fun p => SizeMonotonic (snd p)) lg ->
  SizeMonotonic (backtrack lg).
Admitted.  

Instance genGoodFooTargetSizeMonotonic s m : SizeMonotonic (genGoodFooTarget s m).
Proof.
  elim : s m => [| s IHs ] m; try eauto with typeclass_instances.
  apply backtrackSizeMonotonic.
  repeat apply Forall_cons; try now eauto with typeclass_instances.
Qed.

(* Manual completeness proof *)
Theorem genFooComplete (size m : nat) : 
  semGen (genGoodFooTarget size m) <-->
  lift ([ set foo | sizedFoo foo <= size ] :&: (goodFoo m)).
Proof. 
  elim : size m => [| size IH ] m //=. 
  - rewrite <- sizedFoo_goodFoo_zero.
    rewrite semReturn setI_impl_l. rewrite lift_set1.
    reflexivity.
    move => x H; inv H; constructor.
  - rewrite -sizedFoo_goodFoo_succ semBacktrack /=;
    last by repeat apply Forall_cons; try now eauto with typeclass_instances.
    rewrite !cons_set_eq nil_set_eq. rewrite -> bigcap_setI_l, bigcap_set1.
    rewrite setI_set0.
    + rewrite setU_set0_neut. rewrite !bigcup_setU_l /=.
      rewrite !lift_setU /=.
      apply setU_set_eq_compat; [| apply setU_set_eq_compat ].
      * rewrite bigcup_set1 /= semReturn.
        rewrite setI_impl_r. rewrite lift_set1. reflexivity.
        intros x H; inv H; by constructor.
      * rewrite bigcup_set1 lift_bigcup /=.
        setoid_rewrite semBindSizeMonotonic; try now eauto with typeclass_instances.
        rewrite IH.
        rewrite -> reindex_bigcup
        with (h := @Some Foo) (B := (fun foo : Foo => sizedFoo foo <= size) :&: goodFoo 0);
          last by reflexivity.
        setoid_rewrite semReturn. setoid_rewrite lift_set1.
        rewrite setI_impl_r. reflexivity.
        intros x [k [H1 H2]]. by inv H2.
      * rewrite bigcup_set0 setU_set0_neut.
        rewrite bigcup_set1 lift_bigcup /=.
        setoid_rewrite semBindSizeMonotonic; try now eauto with typeclass_instances.
        rewrite IH.
        rewrite -> reindex_bigcup
        with (h := @Some Foo) (B := (fun foo : Foo => sizedFoo foo <= size) :&: goodFoo m);
          last by reflexivity.
        setoid_rewrite semReturn. setoid_rewrite lift_set1.
        rewrite setI_impl_r. reflexivity.
        intros x [k [H1 H2]]. by inv H2.
    + move => x /= Hc1 Hc2. inv Hc1. inv Hc2.
      apply semReturn in H. inv H.
Qed.

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

