From QuickChick Require Import QuickChick Tactics TacticsUtil Instances Classes DependentClasses.

Require Import String. Open Scope string.
Require Import List micromega.Lia.


From Ltac2 Require Import Ltac2.

Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Set Bullet Behavior "Strict Subproofs".

Class CorrectSized {A : Type} {G} `{Producer G} (g : nat -> G A)  :=
  { prodCorrectSized :
      [ set n | exists s, semProd (g s) n ] <--> [set : A]
  }.

Class Correct {A : Type} {G} `{Producer G} (g : G A)  :=
  { prodCorrect :
      [ set n | semProd g n ] <--> [set : A]
  }.

Ltac2 print_constr (c : constr) := Message.print (Message.of_constr c). 
Ltac2 print_str (c : string) := Message.print (Message.of_string c). 

Local Ltac2 ssromega () := ltac1:(ssromega).


Instance enumNatSized_CorrectSized :
  CorrectSized (@enumSized _ enumNatSized).
Proof.
  constructor. 
  intros t; split; eauto.
  - intros. exact I.
  - intros _. 
    
    induction t.

    + exists 0.

      assert (Hsize := @Enumerators.semChooseSize nat _).
      simpl in *.
      exists 0. split. exact I. eapply Hsize.
      reflexivity.
      reflexivity.
      
    + destruct IHt.
      assert (Hsize := @Enumerators.semChooseSize nat _).
      simpl in *.
      inv H. inv H0. eapply Hsize in H1 > [ | now eauto ].

      exists (x.+1). exists 0. split. exact I. eapply Hsize.
      now eauto.
      simpl in H1.
      simpl. eapply leq_ltS. eassumption.
Qed.       

Instance enumNatSized_SizedMonotonic :
  SizedMonotonic (@enumSized _ enumNatSized).
Proof.
  intros s s1 s2. revert s2.
  induction s1 as [ | s1 IHs1 ].
  - intros s2 Hleq. simpl.
    intros x Hin.
    
    assert (Hsize := @Enumerators.semChooseSize nat _).
    eapply Hsize in Hin; eauto.
    simpl in Hin.
    eapply Hsize. eassumption. simpl.
    ssromega ().
  - intros s2 Hleq.
    destruct s2. now ssromega ().

    simpl.
    rewrite !Enumerators.semChooseSize.
    intros x.
    simpl. intros H. 
    ssromega (). 
    simpl. 
    ssromega ().

    simpl. 
    ssromega ().
Qed.

Instance enumNatSized_SizeMonotonic s:
  SizeMonotonic (@enumSized _ enumNatSized s).
Proof.
  intros s1 s2. revert s2.
  induction s1 as [ | s1 IHs1 ].
  - intros s2 Hleq. simpl.
    intros x Hin.

    assert (Hsize := @Enumerators.semChooseSize nat _).
    eapply Hsize in Hin; eauto.
    simpl in Hin.
    eapply Hsize. eassumption. simpl.
    ssromega ().
  - intros s2 Hleq.
    destruct s2. now ssromega ().

    simpl.
    rewrite !Enumerators.semChooseSize.
    intros x.
    simpl. intros H. 
    ssromega (). 
    simpl. 
    ssromega ().

    simpl. 
    ssromega ().
Qed.


Lemma incl_bigcup_compat_list :
  forall (T U : Type) (h1 h2 : T) (t1 t2 : list T) (F G : T -> set U),
    F h1 \subset G h2 ->
    \bigcup_(x in t1) F x \subset \bigcup_(x in t2) G x ->
    \bigcup_(x in h1 :: t1) F x \subset \bigcup_(x in h2 :: t2) G x.
Proof.
Admitted.


Lemma incl_bigcup_list_tl :
  forall (T U : Type) (h : T) (t : list T) (G : T -> set U) s,
    s \subset \bigcup_(x in t) G x ->
    s \subset \bigcup_(x in h :: t) G x.
Proof.
Admitted.

Lemma incl_bigcup_list_hd :
  forall (T U : Type) (h : T) (t : list T) (G : T -> set U) s,
    s \subset G h ->
    s \subset \bigcup_(x in h :: t) G x.
Proof.
Admitted.

Lemma incl_bigcup_list_nil :
  forall (T U : Type) (G : T -> set U) s,
    \bigcup_(x in [::]) G x \subset s.
Proof. 
Admitted.


(* Ltac2 Notation "ssromega" := ssromega_ltac1 (). *)
(* XXX notation? *)

Inductive tree A : Type :=
| Leaf : A -> tree A
| Leaf' : A -> A -> tree A
| Node : A -> tree A -> tree A -> tree A.

(* Example with two IH *)
Inductive goodTree : nat -> tree nat  -> Prop :=
| GL : goodTree 0 (Leaf nat 0)
| GN :
    forall k t1 t2 n m,
      goodTree n t1 ->
      goodTree m t2 ->
      goodTree m t1 ->
      goodTree (S n) (Node nat k t1 t2).


Derive EnumSized for tree.

Typeclasses eauto := debug.

Instance DecgoodTree (n : nat) (t : tree nat) : DecOpt (goodTree n t) := { decOpt := fun _ => Some true }.


QuickChickDebug Debug On. 


Derive EnumSized for tree.


Ltac2 rec find_enum (_ : unit) :=
  first
    [ now eapply incl_bigcup_list_nil
    | eapply incl_bigcup_compat_list > [ now eapply subset_refl  | find_enum () ]
    | eapply incl_bigcup_list_hd; now eapply subset_refl
    | eapply incl_bigcup_list_tl; find_enum ()
    ].


Ltac2 base_case_size_mon (_ : unit) :=
  destruct s2 > 
  [ now eapply subset_refl | simpl; rewrite !&Hone; now find_enum () ]. 

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
        eapply $ih'; now ssromega () ]
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
  [ now ssromega () | simpl; rewrite !&Hone; now enums_sized_mon @IHs1 ]. 


Ltac2 derive_enum_sized_mon (_ : unit) :=
    assert (Hone := @semOneofSize E _ ProducerSemanticsEnum);
    
    match! goal with
    | [ |- @SizedMonotonic ?t _ _ (@enumSized _ ?inst) ] =>
      (intros s s1; revert s; induction s1 as [| s1 IHs1 ];
      intros s s2 Hleq) > [ now base_case_size_mon () | now ind_case_sized_mon () ]
    end. 


Instance EnumTree_SizedMonotonic A {_ : Enum A} :
  SizedMonotonic (@enumSized _ (@EnumSizedtree A _)).
Proof. derive_enum_sized_mon (). Qed.
  
Lemma list_subset_cons {A} (h : A) (t : seq A) (s : set A)  :
  s h ->
  t \subset s ->
  (h :: t) \subset s.
Proof.
Admitted.

Lemma list_subset_nil {A} (s : set A)  :
  [::] \subset s.
Proof.
Admitted.


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
            eapply $ih'; now ssromega () ]
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

Instance EnumTree_SizeMonotonic A
      {H : Enum A}
      {_ : SizeMonotonic (@enum A H)} s :
  (* TODO debug: *) 
  (* `{_ : @EnumMonotonic A _ ProducerEnum _} s :  *)
  SizeMonotonic (@enumSized _ (@EnumSizedtree A _) s).
Proof. derive_enum_size_mon (). Qed. 


Lemma exists_oneOf_hd A (x : A) g' (g : nat -> E A) (l : nat -> seq (E A)) :
  (exists s : nat, semProd (g s) x) ->
  exists s : nat, semProd (oneOf_ g' ((g s) :: (l s))) x.
Admitted.

Lemma exists_oneOf_tl A (x : A) g' (g : nat -> E A) (l : nat -> seq (E A)) :
  (exists s : nat, semProd (oneOf_ g' (l s)) x) ->
  exists s : nat, semProd (oneOf_ g' ((g s) :: (l s))) x.
Admitted.

Lemma exists_bind_Sized A B (x : A) (g : nat -> E B) (f : nat -> B -> E A) :
  CorrectSized g ->
  (exists z s, semProd (f s z) x) ->  
  exists s : nat, semProd (bindEnum (g s) (f s)) x.
Proof.
Admitted.

Lemma exists_bind A B (x : A) (g : E B) (f : nat -> B -> E A) :
  Correct g ->
  (exists z s, semProd (f s z) x) ->  
  exists s : nat, semProd (bindEnum g (f s)) x.
Proof.
Admitted.

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
  eapply Hs > [ | eapply Hs' > [ | eassumption ] ]. ssromega (). ssromega ().

  eapply Hsf > [ | eapply Hsf' > [ | eassumption ] ]. ssromega (). ssromega ().
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
  ssromega ().
Qed.

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
         eapply exists_bind > [ now eauto with typeclass_instances | now eexists; enum_size_correct () ]
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
      induction $ind'; eapply exists_Sn; repeat (destructIH ()); simpl_enumSized (); try_solve_correct ()
    end
  end.

Lemma EnumTree_correct A {H : Enum A} {_ : SizeMonotonic (@enum A H)} {_ : Correct (@enum A _)} :
  CorrectSized (@enumSized _(@EnumSizedtree A _)).
Proof. derive_enum_correct (). Qed. 


Derive ArbitrarySizedSuchThat for (fun foo => goodTree n foo).

QuickChickDebug Debug On.

Derive SizedProofEqs for (fun foo => goodTree n foo).

Derive SizeMonotonicSuchThatOpt for (fun foo => goodTree n foo).

Derive GenSizedSuchThatCorrect for (fun foo => goodTree n foo).

Derive GenSizedSuchThatSizeMonotonicOpt for (fun foo => goodTree n foo).

Definition genSTgooTree (n : nat) := @arbitraryST _ (fun foo => goodTree n foo) _.

(* Definition genSTgooTreeSound (n : nat) := @STCorrect _ _ (@arbitraryST _  (fun foo => goodTree n foo) _) _. *)

Existing Instance GenSizedSuchThatgoodFooUnif. (* ???? *)

Derive SizeMonotonicSuchThatOpt for (fun (x : Foo) => goodFooUnif input x).

Derive SizedProofEqs for (fun foo => goodFooUnif n foo).

Derive GenSizedSuchThatCorrect for (fun foo => goodFooUnif n foo).

Derive GenSizedSuchThatSizeMonotonicOpt for (fun foo => goodFooUnif n foo).

Definition genSTgoodFooUnif (n : nat) := @arbitraryST _  (fun foo => goodFooUnif n foo) _.

Definition genSTgoodFooUnifSound (n : nat) := @STCorrect _ _ (@arbitraryST _  (fun foo => goodFooUnif n foo) _) _.

(* Interesting. Do we need  Global instance?? *) 
Existing Instance GenSizedSuchThatgoodFooNarrow.  (* Why???? *)

Derive SizeMonotonicSuchThatOpt for (fun foo => goodFooNarrow n foo).

Derive SizedProofEqs for (fun foo => goodFooNarrow n foo).

Derive GenSizedSuchThatCorrect for (fun foo => goodFooNarrow n foo).

Derive GenSizedSuchThatSizeMonotonicOpt for (fun foo => goodFooNarrow n foo).

Definition genSTgoodFooNarrow (n : nat) := @arbitraryST _  (fun foo => goodFooNarrow n foo) _.

Definition genSTgoodFooNarrowSound (n : nat) := @STCorrect _ _ (@arbitraryST _  (fun foo => goodFooNarrow n foo) _) _.

Existing Instance GenSizedSuchThatgoodFooCombo.

Derive SizeMonotonicSuchThatOpt for (fun foo => goodFooCombo n foo).

Derive SizedProofEqs for (fun foo => goodFooCombo n foo).

Derive GenSizedSuchThatCorrect for (fun foo => goodFooCombo n foo).

Derive GenSizedSuchThatSizeMonotonicOpt for (fun foo => goodFooCombo n foo).

Definition genSTgoodFooCombo (n : nat) := @arbitraryST _  (fun foo => goodFooCombo n foo) _.

Definition genSTgoodFooComboSound (n : nat) := @STCorrect _ _ (@arbitraryST _  (fun foo => goodFooCombo n foo) _) _.

Existing Instance GenSizedSuchThatgoodFoo.

Derive SizeMonotonicSuchThatOpt for (fun (x : Foo) => goodFoo input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFoo input x).

Derive GenSizedSuchThatCorrect for (fun foo => goodFoo n foo).

Derive GenSizedSuchThatSizeMonotonicOpt for (fun foo => goodFoo n foo).

Definition genSTgoodFoo (n : nat) := @arbitraryST _  (fun foo => goodFoo n foo) _.

Definition genSTgoodFooSound (n : nat) := @STCorrect _ _ (@arbitraryST _  (fun foo => goodFoo n foo) _) _.

Existing Instance GenSizedSuchThatgoodFooPrec.  (* ???? *)

Derive SizeMonotonicSuchThatOpt for (fun (x : Foo) => goodFooPrec input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooPrec input x).

Derive GenSizedSuchThatCorrect for (fun foo => goodFooPrec n foo).

Derive GenSizedSuchThatSizeMonotonicOpt for (fun foo => goodFooPrec n foo).

Definition genSTgoodFooPrec (n : nat) := @arbitraryST _  (fun foo => goodFooPrec n foo) _.

Definition genSTgoodFooPrecSound (n : nat) := @STCorrect _ _ (@arbitraryST _  (fun foo => goodFooPrec n foo) _) _.

Existing Instance GenSizedSuchThatgoodFooMatch.  (* ???? *)

Derive SizeMonotonicSuchThatOpt for (fun foo => goodFooMatch n foo).

Derive SizedProofEqs for (fun foo => goodFooMatch n foo).

Derive GenSizedSuchThatCorrect for (fun foo => goodFooMatch n foo).

Derive GenSizedSuchThatSizeMonotonicOpt for (fun foo => goodFooMatch n foo).

Definition genSTgoodFooMatch (n : nat) := @arbitraryST _  (fun foo => goodFooMatch n foo) _.

Definition genSTgoodFooMatchSound (n : nat) := @STCorrect _ _ (@arbitraryST _  (fun foo => goodFooMatch n foo) _) _.

Existing Instance GenSizedSuchThatgoodFooRec.  (* ???? *)

Derive SizeMonotonicSuchThatOpt for (fun (x : Foo) => goodFooRec input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooRec input x).

Derive GenSizedSuchThatCorrect for (fun foo => goodFooRec n foo).

Derive GenSizedSuchThatSizeMonotonicOpt for (fun foo => goodFooRec n foo).

Definition genSTgoodFooRec (n : nat) := @arbitraryST _  (fun foo => goodFooRec n foo) _.

Definition genSTgoodFooRecSound (n : nat) := @STCorrect _ _ (@arbitraryST _  (fun foo => goodFooRec n foo) _) _.

Inductive goodFooB : nat -> Foo -> Prop :=
| GF1 : goodFooB 2 (Foo2 Foo1)
| GF2 : goodFooB 3 (Foo2 (Foo2 Foo1)).

Derive ArbitrarySizedSuchThat for (fun (x : Foo) => goodFooB input x).

Derive SizedProofEqs for (fun (x : Foo) => goodFooB input x).

Derive SizeMonotonicSuchThatOpt for (fun foo => goodFooB n foo).

Derive GenSizedSuchThatCorrect for (fun foo => goodFooB n foo).

Derive GenSizedSuchThatSizeMonotonicOpt for  (fun foo => goodFooB n foo).

Definition genSTgoodFooB (n : nat) := @arbitraryST _  (fun foo => goodFooB n foo) _.

Definition genSTgoodFooBSound (n : nat) := @STCorrect _ _ (@arbitraryST _  (fun foo => goodFooB n foo) _) _.

(* Derive SizeMonotonicSuchThat for (fun foo => goodTree n foo). *)
(* XXX
   bug for 
| GL : goodTree 0 Leaf
| GN : forall k t1 t2 n, goodTree n t1 ->
                      ~ t1 =  t2 ->υ
                      (* goodTree m t1 -> *)
                      goodTree (S n) (Node k t1 t2).
 *)

Inductive LRTree : tree -> Prop :=
| PLeaf : LRTree Leaf
| PNode :
    forall m t1 t2,
      ~ t1 = Node 2 Leaf Leaf ->
      ~ Node 4 Leaf Leaf = t1 ->
      LRTree t1 ->
      LRTree t2 ->
      LRTree (Node m t1 t2).



Derive ArbitrarySizedSuchThat for (fun (x : tree) => LRTree x).

(* XXX sucThatMaybe case *)

Instance DecidableLRTree t : Dec (LRTree t).
Proof.
Admitted.

Derive SizedProofEqs for (fun (x : tree) => LRTree x).

Derive SizeMonotonicSuchThatOpt for (fun foo => LRTree foo).

Derive GenSizedSuchThatCorrect for (fun foo => LRTree foo).

Derive GenSizedSuchThatSizeMonotonicOpt for (fun foo => LRTree foo).

Definition genSTLRTree (n : nat) := @arbitraryST _  (fun foo => LRTree foo) _.

Definition genSTLRTreeSound (n : nat) := @STCorrect _ _ (@arbitraryST _  (fun foo => LRTree foo) _) _.


Inductive HeightTree : nat -> tree -> Prop :=
| HLeaf : forall n, HeightTree n Leaf
| HNode :
    forall t1 t2 n m,
      HeightTree n t1 ->
      HeightTree n t2 ->
      HeightTree (S n) (Node m t1 t2).


Instance ArbitrarySuchThatEql {A} (x : A) : GenSuchThat A (fun y => eq x y) :=
  {| arbitraryST := returnGen (Some x) |}.



(* XXX breaks gen *)

(* Inductive ex_test : tree -> Prop := *)
(* | B : ex_test Leaf  *)
(* | Ind : *)
(*     forall (list  y12  : nat) t, *)
(*       list = y12 -> *)
(*       ex_test (Node 4 t t). *)

(* Derive ArbitrarySizedSuchThat for (fun (x : tree) => ex_test x). *)

(* Set Printing All.  *)

(* Inductive LRTree : tree -> Prop := *)
(* | PLeaf : LRTree Leaf *)
(* | PNode : *)
(*     forall m t1 t2, *)
(*       Node 2 Leaf Leaf = t1 -> *)
(*       t1 = Node 2 Leaf Leaf -> *)
(*       LRTree t1 -> *)
(*       LRTree t2 -> *)
(*       LRTree (Node m t1 t2). *)

(* Inductive test : nat -> Foo -> Prop := *)
(* | T : forall (x : False), test 1 Foo1. *)

(* Derive ArbitrarySizedSuchThat for (fun foo => test n foo). *)

(* Inductive test1 : bool -> Foo -> Prop := *)
(* | T1 : forall (x1 x2 x3 : bool), x1 = x3 -> test1 x2 Foo1. *)

(* Derive ArbitrarySizedSuchThat for (fun foo => test1 n foo). *)

(* Inductive test2 : nat -> Foo -> Prop := *)
(* | T2 : forall (x1 x2 : bool), x1 = x2 ->  test2 1 Foo1. *)
 
(* Derive ArbitrarySizedSuchThat for (fun foo => test2 n foo). *)

(* XXX weird bug when naming binders with name of already existing ids,
   e.g. nat, list*)

(* Inductive HeightTree : nat -> tree -> Prop := *)
(* | HLeaf : forall n, HeightTree n Leaf *)
(* | HNode : *)
(*     forall t1 t2 n k m, *)
(*       k = 3 -> *)
(*       HeightTree k t2 -> *)
(*       HeightTree k t1 -> *)
(*       HeightTree n (Node m t1 t2). *)

(* Inductive goodTree : nat -> tree -> Prop := *)
(* | GL : goodTree 0 Leaf *)
(* | GN : forall k t1 t2 n m, goodTree n t1 -> *)
(*                       goodTree m t2 -> *)
(*                       goodTree (n + m + 1) (Node k t1 t2). *)

(* Lemma test2 {A} (gs1 gs2 : nat -> list (nat * G (option A))) s s1 s2 :  *)
(*       \bigcup_(g in gs1 s1) (semGenSize (snd g) s) \subset  \bigcup_(g in gs2 s2) (semGenSize (snd g) s) -> *)
(*       semGenSize (backtrack (gs1 s1)) s \subset semGenSize (backtrack (gs2 s2)) s. *)
(* Admitted. *)

(* Goal (forall inp : nat, SizedMonotonic (@arbitrarySizeST Foo (fun (x : Foo) => goodFooRec inp x) _)). *)
(* Proof. *)
(*   intros inp. *)
(*   constructor. *)
(*   intros s s1 s2. *)
(*   revert inp. *)
(*   induction s1; induction s2; intros. *)
(*   - simpl. eapply subset_refl. *)
(*   - simpl. *)
(*     refine (test *)
(*               (fun s => [(1, returnGen (Some Foo1))]) *)
(*               (fun s => [(1, returnGen (Some Foo1)); *)
(*                        (1, *)
(*                         doM! foo <- *)
(*                            (fix aux_arb (size0 input0_ : nat) {struct size0} :  *)
(*                               G (option Foo) := *)
(*                               match size0 with *)
(*                                 | 0 => backtrack [(1, returnGen (Some Foo1))] *)
(*                                 | size'.+1 => *)
(*                                   backtrack *)
(*                                     [(1, returnGen (Some Foo1)); *)
(*                                       (1, doM! foo <- aux_arb size' 0; returnGen (Some (Foo2 foo)))] *)
(*                               end) s 0; returnGen (Some (Foo2 foo)))]) *)
(*               s 0 s2 _). *)
(*     admit. *)
(*   - ssromega. *)
(*   - simpl. *)
(*     refine (test *)
(*               (fun s => [(1, returnGen (Some Foo1)); *)
(*                        (1, *)
(*                         doM! foo <- *)
(*                            (fix aux_arb (size0 input0_ : nat) {struct size0} :  *)
(*                               G (option Foo) := *)
(*                               match size0 with *)
(*                                 | 0 => backtrack [(1, returnGen (Some Foo1))] *)
(*                                 | size'.+1 => *)
(*                                   backtrack *)
(*                                     [(1, returnGen (Some Foo1)); *)
(*                                       (1, doM! foo <- aux_arb size' 0; returnGen (Some (Foo2 foo)))] *)
(*                               end) s 0; returnGen (Some (Foo2 foo)))]) *)
(*               (fun s => [(1, returnGen (Some Foo1)); *)
(*                        (1, *)
(*                         doM! foo <- *)
(*                            (fix aux_arb (size0 input0_ : nat) {struct size0} :  *)
(*                               G (option Foo) := *)
(*                               match size0 with *)
(*                                 | 0 => backtrack [(1, returnGen (Some Foo1))] *)
(*                                 | size'.+1 => *)
(*                                   backtrack *)
(*                                     [(1, returnGen (Some Foo1)); *)
(*                                       (1, doM! foo <- aux_arb size' 0; returnGen (Some (Foo2 foo)))] *)
(*                               end) s 0; returnGen (Some (Foo2 foo)))]) *)
(*               s s1 s2 _). *)
(*     admit. *)

Definition success := "Proofs work!".
Print success.
