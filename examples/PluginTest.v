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

Lemma setI_impl_l {T} (s1 s2 : set T) : s1 \subset s2 -> s1 :&: s2 <--> s1.
Proof.      
  firstorder.
Qed.      

Lemma bigcup_setU_l:
  forall (U T : Type) (s1 s2 : set U) (f : U -> set T),
  \bigcup_(i in (s1 :|: s2)) f i <-->
  \bigcup_(i in s1) f i :|: \bigcup_(i in s2) f i.
Proof.
  firstorder.
Qed.

(* Derived *)
Fixpoint aux_arb (size : nat) : G Foo :=
  match size with
    | 0 => returnGen Foo1
    | S size' =>
      freq ( (1, returnGen Foo1);;
            [(size,
              bindGen (aux_arb size')
                      (fun p0 : Foo => returnGen (Foo2 p0)));
              (size,
               bindGen arbitrary
                       (fun p0 : nat =>
                          bindGen (aux_arb size')
                                  (fun p1 : Foo =>
                                     bindGen (aux_arb size')
                                             (fun p2 : Foo => returnGen (Foo3 p0 p1 p2)))))])
  end.
           
Fixpoint sizedFoo (foo : Foo) := 
  match foo with 
    | Foo1 => 0
    | Foo2 foo => 1 + sizedFoo foo
    | Foo3 _ foo1 foo2 => 1 + max (sizedFoo foo1) (sizedFoo foo2)
  end.


From mathcomp.ssreflect Require Import ssreflect ssrnat ssrbool.
Import Tactics.
Set Bullet Behavior "Strict Subproofs".

(* Zoe : Probably a good idea to generate size equations automatically. *)

Lemma sizedFoo_eq s :
  [set Foo1] :|:
  (\bigcup_(f in fun f => sizedFoo f < s) ([set Foo2 f]) :|:
    \bigcup_n ( 
      \bigcup_(f1 in fun f => sizedFoo f < s) (
         \bigcup_(f2 in fun f => sizedFoo f < s) (
            [set Foo3 n f1 f2]))))  <-->
  [set foo : Foo | sizedFoo foo <= s ].
Proof.
  move => [| f | n f1 f2].
  + simpl; split => _; eauto. by repeat constructor.
  + simpl. split.
    * move => [H | [[f' [H1 [H2]]] | [n' [Hn [f1' [Hf1 [f2' [Hf2 Heq]]]]]]]];
        subst; try discriminate.
      eassumption.
    * right; left. eexists; split; eauto. reflexivity.
  + split.
    * move => [H | [[f [H1 H2]] | [n' [Hn [f1' [Hf1 [f2' [Hf2 [Heq1 Heq2 Heq3]]]]]]]]];
        subst; try discriminate.
      apply/leP/NPeano.Nat.le_succ_l/NPeano.Nat.max_lub_lt; ssromega.
    * move => H.
      right; right; repeat eexists;
      move : H => /leP/NPeano.Nat.le_succ_l/NPeano.Nat.max_lub_lt_iff H; ssromega.
Qed.
  

Lemma sizedFoo_zero :
  [set Foo1] <--> [set foo : Foo | sizedFoo foo <= 0 ].
Proof.
  move => [ | f | n f1 f2]; split; simpl; move => H; by firstorder.
Qed.

Lemma sizedFoo_succ s :
  [set Foo1] :|:
  (\bigcup_(f in fun f => sizedFoo f <= s) ([set Foo2 f]) :|:
    \bigcup_n ( 
      \bigcup_(f1 in fun f => sizedFoo f <= s) (
         \bigcup_(f2 in fun f => sizedFoo f <= s) (
            [set Foo3 n f1 f2]))))  <-->
  [set foo : Foo | sizedFoo foo <= s.+1 ].
Proof.
  setoid_rewrite <- sizedFoo_eq at 4. reflexivity.
Qed.

(* TODO : move to set lib *)
Lemma setU_set_eq_compat {T} (s1 s2 s1' s2' : set T) :
  s1 <--> s1' ->
  s2 <--> s2' ->
  s1 :|: s2 <--> s1' :|: s2'.
Proof.
  by firstorder.
Qed.

(* TODO move to gen lib *)
Lemma frequencySizeMonotonic {A} (g0 : G A) lg :
  SizeMonotonic g0 ->
  Forall (fun p => SizeMonotonic (snd p)) lg ->
  SizeMonotonic (frequency g0 lg).
Admitted.  

Instance arbFooSizeMonotonic s : SizeMonotonic (aux_arb s).
Proof.
  induction s; try eauto with typeclass_instances.
  apply frequencySizeMonotonic; try eauto with typeclass_instances.
  repeat apply Forall_cons; eauto with typeclass_instances.
Qed.

Theorem arbFooComplete size : 
  semGen (aux_arb size) <--> [set foo : Foo | sizedFoo foo <= size].
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

Fixpoint genGoodFooTarget (sz : nat) (m : nat) : G (option Foo) :=
  match sz with
    | O => backtrack [(1, returnGen (Some Foo1))]
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
           match res0 with 
             | Some foo2 =>
               (* Done *)
               returnGen (Some (Foo2 foo2))
             | None => returnGen None
           end)
          )
        ; (sz, (* Good3 *)
          (* Match m <-> n, foo <-> Foo3 n Foo1 foo2 *)
          (* Generate goodFoo n foo2 *)
          bindGen (genGoodFooTarget sz' m) (fun res0 =>
          match res0 with 
            | Some foo2 =>
              (* Done *)
              returnGen (Some (Foo3 m Foo1 foo2))
            | None => returnGen None
          end)
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


(* Manual completeness proof *)
Theorem genFooComplete (size m : nat) : 
  semGenSize (genGoodFooTarget size m) size <--> 
             fun (x : option Foo) =>
               match x with 
                 | Some foo => goodFooSize foo <= size /\ goodFoo m foo
                 | _ => false
               end.
  move: m; induction size => m //=. 
  - rewrite semBacktrackSize.
    rewrite setI_impl_l.
    + rewrite cons_set_eq nil_set_eq setU_set0_neut bigcup_set1; simpl.
      rewrite semReturnSize.
      rewrite -> eq_bigcapl with (B := [set (1, returnGen (Some Foo1))]).
      * { rewrite bigcap_set1; simpl.
          rewrite semReturnSize (@setI_set0 _ [set None]). 
          - rewrite setU_set0_neut.
            rewrite setI_impl_r.
            + move => [a | ]; split; try by firstorder.
              * move => H; inversion H; subst; simpl; split; eauto.
                by constructor.
              * move => [H1 H2]. inversion H2; subst; simpl in *; try ssromega. 
                by reflexivity.
            + move => x H; inversion H; subst; simpl in *; eauto.
          - move => x H; inversion H; subst; simpl in *; eauto.
            move => Contra; inversion Contra.
        } 
      * reflexivity.
    + move => x H; inversion H; subst; simpl in *; eauto.
  - rewrite semBacktrackSize.
    rewrite cons_set_eq setI_setU_distr bigcap_setI_l.
    rewrite (@setI_set0 _ [set None]).
    + rewrite !bigcup_setU_l !cons_set_eq nil_set_eq setI_setU_distr bigcup_setU_l !setU_set0_neut.
      rewrite !setI_impl_l;
        try solve [move => x H; inversion H; subst; simpl in *; eauto].
      rewrite !bigcup_set1.
      simpl in *.

      rewrite semReturnSize.
      rewrite setI_impl_r; 
        try solve [move => x H; inversion H; subst; simpl in *; eauto].
      rewrite !semBindSize.
      

      { move => x; split.
        - move => [H1 | [[H21 H22] | H3]].
          + inversion H1; subst; simpl in*; eauto.
            split; [ssromega | constructor].
          + destruct x; simpl in *; try discriminate; simpl in *.
            move: H22 => [y [Hy1 Hy2]].
            destruct y; simpl in *;
            apply semReturnSize in Hy2; inversion Hy2; subst; simpl in *.
            
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

