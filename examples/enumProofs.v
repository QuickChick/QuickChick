From QuickChick Require Import QuickChick Tactics TacticsUtil Instances Classes DependentClasses Sets.

Require Import String. Open Scope string.
Require Import List micromega.Lia.


From Ltac2 Require Import Ltac2.

Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Set Bullet Behavior "Strict Subproofs".

Lemma list_subset_cons {A} (h : A) (t : seq A) (s : set A)  :
  s h ->
  t \subset s ->
  (h :: t) \subset s.
Proof.
  intros H1 H2 x Hin. inv Hin; eauto.
Qed.

Lemma list_subset_nil {A} (s : set A)  :
  [::] \subset s.
Proof. intros x Hin. inv Hin. Qed.


Lemma exists_oneOf_hd A (x : A) g' (g : nat -> E A) (l : nat -> seq (E A)) :
  (exists s : nat, semProd (g s) x) ->
  exists s : nat, semProd (oneOf_ g' ((g s) :: (l s))) x.
Proof.
  intros Hin. inv Hin.
  eexists. eapply semOneof. now eauto with typeclass_instances.
  eexists. split; eauto. now left. 
Qed.

Lemma exists_oneOf_tl A (x : A) g' (g : nat -> E A) (l : nat -> seq (E A)) :
  (exists s : nat, match l s with
                   | nil => False
                   | g1 :: gs => semProd (oneOf_ g' (g1 :: gs)) x
                   end) ->
  exists s : nat, semProd (oneOf_ g' ((g s) :: (l s))) x.
Proof.
  intros Hin. inv Hin.
  eexists. eapply semOneof. 
  now eauto with typeclass_instances.
  destruct (l x0)  eqn:Heq.
  - exfalso; eauto.
  - eapply semOneof in H > [ | now eauto with typeclass_instances ].
    rewrite Heq. inv H. destruct H0. eexists. split > [ | eassumption ].
    now right; eauto.
Qed.

Lemma exists_bind A B (x : A) (g : E B) (f : nat -> B -> E A) :
  Correct B g ->
  SizeMonotonic g ->
  (forall a s, SizeMonotonic (f a s)) ->

  (exists z s, semProd (f s z) x) ->  
  exists s : nat, semProd (bindEnum g (f s)) x.
Proof.
  intros Hc Hs1 Hs2 He. inv He. inv H. inv H0.
  inv H.
  assert (Hin : [set : B] x0) by reflexivity.
  eapply Hc in Hin. inv Hin. inv H.
  exists x1, (Nat.max x2 x3). split. reflexivity.
  eapply (@semBindSize E _ _ B A).
  eexists. split.

  eapply Hs1 > [ | eassumption ]. now ssromega.
  eapply Hs2 > [ | eassumption ]. now ssromega.
Qed.

Lemma exists_return A (x : A) :
  exists s : nat, semProd (returnEnum x) x.
Proof.
  exists 0. eapply (@semReturn E _ ProducerSemanticsEnum); reflexivity.
Qed.

Lemma exists_bind_Sized_alt A B
      (g : nat -> E B) (f : B -> nat -> E A)
      (x : A) (z : B) (s' : nat) :
  SizedMonotonic g ->
  (forall s, SizeMonotonic (g s)) ->

  (forall a, SizedMonotonic (f a)) ->
  (forall a s, SizeMonotonic (f a s)) ->

  semProd (g s') z ->
  (exists s, semProd (f z s) x) ->  
  exists s : nat, semProd (bindEnum (g s) (fun x => f x s)) x.
Proof.
  intros Hs Hs' Hsf Hsf' Hprod Hex. inv Hex. inv Hprod.
  inv H. destruct H0.
  exists (Nat.max s' x0). inv H1.
  exists (Nat.max x1 x2).
  
  split. reflexivity.
  
  eapply (@semBindSize E _ _ B A).

  eexists. split.
  eapply Hs > [ | eapply Hs' > [ | eassumption ] ]. ssromega. ssromega.

  eapply Hsf > [ | eapply Hsf' > [ | eassumption ] ]. ssromega. ssromega.
Qed.

Lemma semProd_mon {A} (g : nat -> E A) {_ : SizedMonotonic g} :
  forall s1 s2,
    (s1 <= s2)%coq_nat -> 
    semProd (g s1) \subset semProd (g s2).
Proof.
  intros s1 s2 Hleq.
  intros x Hin. inv Hin. inv H0.
  eexists x0. split; eauto.
  eapply H > [ | eassumption ].
  destruct (leqP s1 s2); eauto.
  ssromega.
Qed.



(** Tactics for proofs *)

(*** Sized Monotonicity *)
Ltac2 rec find_enum (_ : unit) :=
  first
    [ now eapply incl_bigcup_list_nil
    | eapply incl_bigcup_compat_list > [ now eapply subset_refl  | find_enum () ]
    | eapply incl_bigcup_list_hd; now eapply subset_refl
    | eapply incl_bigcup_list_tl; find_enum ()
    ].


Ltac2 base_case_size_mon (_ : unit) :=
  destruct s2 > 
  [ now eapply subset_refl | simpl; first [ now eapply subset_refl
                                          | simpl; rewrite !&Hone; now find_enum () ] ]. 

Ltac2 rec enum_sized_mon (ih : ident) :=
  first
    [ (* ret *)
      now eapply subset_refl
    | (* bind *)
    eapply (@semBindSize_subset_compat _ _ ProducerSemanticsEnum) >
    [ let x := Fresh.in_goal (id_of_string "x") in
      intros $x;
    first
      [ now eapply subset_refl (* for calls to enum *)
      | let ih' := Control.hyp ih in (* for recursive calls *)
        eapply $ih'; now ssromega ]
    | let x := Fresh.in_goal (id_of_string "x") in
      let s := Fresh.in_goal (id_of_string "s") in
      intros $x $s; enum_sized_mon ih
    ]
    ].

Ltac2 rec enums_sized_mon (ih : ident) :=
  first
    [ now eapply incl_bigcup_list_nil
    | eapply incl_bigcup_compat_list > [ now enum_sized_mon @IHs1 | enums_sized_mon ih ] ].

Ltac2 ind_case_sized_mon (_ : unit) :=
  destruct s2 > 
  [ now ssromega | simpl; first [ now enum_sized_mon @IHs1
                                | rewrite !&Hone; now enums_sized_mon @IHs1 ] ]. 


Ltac2 derive_enum_sized_mon (_ : unit) :=
    assert (Hone := @semOneofSize E _ ProducerSemanticsEnum);
    
    match! goal with
    | [ |- @SizedMonotonic ?t _ _ (@enumSized _ ?inst) ] =>
      (intros s s1; revert s; induction s1 as [| s1 IHs1 ];
      intros s s2 Hleq) > [ now base_case_size_mon () | now ind_case_sized_mon () ]
    end. 


(*** Size monotonicity *) 

Ltac2 rec enum_size_mon (ih : ident) :=
  first
    [ (* ret *)
      eapply returnGenSizeMonotonic;
      now eauto with typeclass_instances
    | (* bind *)
      eapply bindMonotonic >
      [ now eauto with typeclass_instances
      | first
          [ now eauto with typeclass_instances (* for calls to enum *)
          | let ih' := Control.hyp ih in (* for recursive calls *)
            eapply $ih'; now ssromega ]
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; enum_size_mon ih
      ]
    ].

Ltac2 rec enums_size_mon (t : constr) (ih : ident) :=
  first
    [ now eapply (@list_subset_nil (E $t))
    | eapply (@list_subset_cons (E $t)) > 
      [ now enum_size_mon ih
      | enums_size_mon t ih ] ]. 

Ltac2 derive_enum_size_mon (_ : unit) :=
  (* intros s;  *)
    match! goal with
    | [ |- @SizeMonotonic ?t _ _ _ ] =>
      induction s as [ | s IHs ];
        simpl;
        first [ eapply oneofMonotonic >  
                [ now eauto with typeclass_instances
                | now enum_size_mon @IHs
                | now enums_size_mon t @IHs ]
              | now enum_size_mon @IHs ]
    end.

(*** Correct monotonic *) 

Ltac2 solve_sized_mon (hs : ident) :=
  let t := Fresh.in_goal (id_of_string "t") in
  let s := Fresh.in_goal (id_of_string "s") in
  let s1 := Fresh.in_goal (id_of_string "s1") in
  let s2 := Fresh.in_goal (id_of_string "s2") in
  let hleq := Fresh.in_goal (id_of_string "Hleq") in
  intros $t $s $s1 $s2 $hleq; now enum_sized_mon hs.      

Ltac2 solve_size_mon (hs : ident) :=
  let t := Fresh.in_goal (id_of_string "t") in
  let s := Fresh.in_goal (id_of_string "s") in
  intros $t $s; now enum_size_mon hs.      

Ltac2 if_exists tac :=
  match! goal with
  | [|- exists s, semProd _ _ ] => tac
  end.

Ltac2 rec enum_size_correct (_ : unit) :=
  first
    [ (* return *)
      now eapply exists_return; eauto
                                  
    | (* bind non rec *)
      match! goal with
      |  [ |- exists _ : nat, semProd (bindEnum enum _) _ ] => 
         eapply exists_bind > [ now eauto with typeclass_instances
                              | now eauto with typeclass_instances
                              | now solve_size_mon @Hsize
                              | now eexists; enum_size_correct () ]
      end
    | (* bind rec *)
      match! goal with
      | [|- exists z, semProd (bindEnum (&_aux_enum z) _) _  ] =>
        eapply exists_bind_Sized_alt >
        [ now eauto with typeclass_instances
        | now eauto with typeclass_instances
        | now solve_sized_mon @Hsized
        | now solve_size_mon @Hsize
        |
        | now enum_size_correct () ]; eassumption
      end
    ]. 

Ltac2 destructIH (_ : unit) :=
  match! goal with
  | [ h : (exists s, semProd _ _) |- _ ] =>
    let h' := Control.hyp h in destruct $h'
  end.

Ltac2 simpl_minus_enumSized (_ : unit) :=
  ltac1:(with_strategy opaque [enumSized] simplstar).

Ltac2 simpl_enumSized (_ : unit) :=
  unfold enumSized; simpl_minus_enumSized (). 

Ltac2 rec try_solve_correct (_ : unit) :=
  first
    [ eapply exists_oneOf_hd; now enum_size_correct ()
    | eapply exists_oneOf_tl; try_solve_correct ()
    ].

Ltac2 derive_enum_correct (_ : unit) := 
  match! goal with
  | [ |- @CorrectSized ?typ _ _ ?en ] =>  
    simpl_enumSized ();
    match! goal with
    | [ |- @CorrectSized _ _ _ [eta ?en_simpl] ] =>
      (* get the enum body *)
      set (_aux_enum := ltac2:(exact $en_simpl));
      let hsize := Fresh.in_goal (id_of_string "Hsize") in
      let hsized := Fresh.in_goal (id_of_string "Hsized") in
      let ind := Fresh.in_goal (id_of_string "t") in
      (* Derive monotonicity instances *)
      assert ($hsized : SizedMonotonic $en) > [ now eauto with typeclass_instances | ];
      assert ($hsize : forall s, SizeMonotonic ($en s)) > [ now eauto with typeclass_instances | ];
      econstructor; intro $ind; split > [ intro; exact I | intros _ ];
      let ind' := Control.hyp ind in
      induction $ind'; eapply exists_Sn; repeat (destructIH ()); simpl_enumSized ();
      first [ try_solve_correct () | enum_size_correct () ]
    end
  end.


(** Examples *)

Inductive tree A : Type :=
| Leaf : A -> tree A
| Leaf' : A -> A -> tree A
| Node : A -> tree A -> tree A -> tree A.


Derive EnumSized for tree.


Instance EnumTree_SizedMonotonic A {_ : Enum A} :
  SizedMonotonic (@enumSized _ (@EnumSizedtree A _)).
Proof. derive_enum_sized_mon (). Qed.
  

Instance EnumTree_SizeMonotonic A `{EnumMonotonic A} s :
  SizeMonotonic (@enumSized _ (@EnumSizedtree A _) s).
Proof. derive_enum_size_mon (). Qed. 



Lemma EnumTree_correct A {H : Enum A} `{EnumMonotonicCorrect A} :
  CorrectSized (@enumSized _(@EnumSizedtree A _)).
Proof. derive_enum_correct (). Qed. 

Inductive Foo : Type :=
| Bar.


Derive EnumSized for Foo.


Instance EnumFoo_SizedMonotonic :
  SizedMonotonic (@enumSized _ EnumSizedFoo).
Proof. derive_enum_sized_mon (). Qed.
  

Instance EnumFoo_SizeMonotonic s :
  SizeMonotonic (@enumSized _ EnumSizedFoo s).
Proof. derive_enum_size_mon (). Qed. 


Lemma EnumFoo_correct :
  CorrectSized (@enumSized _ EnumSizedFoo).
Proof. derive_enum_correct (). Qed. 


Inductive Foo2 A : Type :=
| Bar1
| Bar2 : A -> Foo2 A.


Derive EnumSized for Foo2.


Instance EnumFoo2_SizedMonotonic A {_ : Enum A} :
  SizedMonotonic (@enumSized _ (@EnumSizedFoo2 A _)).
Proof. derive_enum_sized_mon (). Qed.
  

Instance EnumFoo2_SizeMonotonic A `{EnumMonotonic A} s :
  SizeMonotonic (@enumSized _ (@EnumSizedFoo2 A _) s).
Proof. derive_enum_size_mon (). Qed. 


Lemma EnumFoo2_correct A {H : Enum A} `{EnumMonotonicCorrect A} :
  CorrectSized (@enumSized _ (@EnumSizedFoo2 A _)).
Proof. derive_enum_correct (). Qed. 


(* Example with two IH *)
Inductive goodTree : nat -> tree nat  -> Prop :=
| GL : goodTree 0 (Leaf nat 0)
| GN :
    forall k t1 t2 n m,
      goodTree n t1 ->
      goodTree m t2 ->
      goodTree m t1 ->
      goodTree (S n) (Node nat k t1 t2).


