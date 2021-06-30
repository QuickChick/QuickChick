From QuickChick Require Import QuickChick Tactics TacticsUtil Instances Classes
     DependentClasses Sets EnumProofs.

Require Import String. Open Scope string.
Require Import List micromega.Lia.

Import ListNotations.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

From Ltac2 Require Import Ltac2.

Require Import enumProofs. (* TODO change *)

Set Bullet Behavior "Strict Subproofs".

Inductive In' {A} : A -> list A -> Prop :=
| In_hd :
    forall x l, In' x (cons x l)
| In_tl :
    forall x y l, In' x l -> In' x (cons y l).


Derive DecOpt for (In' a l).

Instance DecOptIn'_listSizeMonotonic A {_ : Enum A} {_ : Dec_Eq A}
         (x : A) (l : list A) : DecOptSizeMonotonic (In' x l).
Proof. derive_mon (). Qed.

Instance DecOptIn'_list_sound A {_ : Enum A} {_ : Dec_Eq A} (x : A) (l : list A) :
  DecOptSoundPos (In' x l).
Proof. derive_sound (). Qed.

Instance DecOptIn'_list_complete A {_ : Enum A} {_ : Dec_Eq A} (x : A) (l : list A) :
  DecOptCompletePos (In' x l).
Proof. derive_complete (). Qed.

Derive ArbitrarySizedSuchThat for (fun x => In' x l).
Derive EnumSizedSuchThat for (fun x => In' x l).



Ltac2 rec enumST_sized_mon (ih : ident) :=
  first
    [ (* ret *)
      match! goal with
      | [ |- ?s \subset ?s ] => now eapply subset_refl
      end
    | (* dec matching *)
      match! goal with
      | [ |- semProdSizeOpt (match @decOpt ?p ?i ?s1 with _ => _ end) _ \subset
             semProdSizeOpt (match decOpt ?s2 with _ => _ end) _ ] =>
        let hdec := Fresh.in_goal (id_of_string "Hdec") in 
        destruct (@decOpt $p $i $s1) eqn:$hdec >
        [ ((erewrite (@CheckerProofs.mon $p $i _ $s1 $s2) > [ | | eassumption ]) > [ enumST_sized_mon ih | ssromega ])
        | rewrite (@semReturnSizeOpt_None E _ ProducerSemanticsEnum); now eapply sub0set ]
      end
     | (* input matching *) 
      match! goal with
      | [ |- semProdSizeOpt (match ?p with _ => _ end) _ \subset _ ] =>
        destruct $p; enumST_sized_mon ih
      end
    | (* bindOpt *)
      eapply (@semBindOptSizeOpt_subset_compat E _ ProducerSemanticsEnum) >
      [ first
          [ now eapply subset_refl (* for calls to enum *)
          | let ih' := Control.hyp ih in (* for recursive calls *)
            eapply $ih'; now ssromega ]
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; enumST_sized_mon ih
      ]
    | (* bind *)
      eapply (@semBindSizeOpt_subset_compat E _ ProducerSemanticsEnum) >
      [ now eapply subset_refl 
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; enumST_sized_mon ih
      ]
    | ()
    ].

Ltac2 rec find_enumST (ih : ident) :=
  first
    [ now eapply incl_bigcup_list_nil
    | eapply incl_bigcup_compat_list > [ (now enumST_sized_mon ih)  | find_enumST ih ]
    | eapply incl_bigcup_list_tl; find_enumST ih
    ].

Ltac2 base_case_st_size_mon (s2 : constr) :=
  destruct $s2 > 
  [ first [ now eapply subset_refl | rewrite !enumerate_correct_size_opt; find_enumST @dummy ]
  | rewrite !enumerate_correct_size_opt; find_enumST @dummy ]. 

Ltac2 ind_case_st_sized_mon (s2 : constr) (ih : ident) :=
  destruct $s2 > 
  [ now ssromega |  rewrite !enumerate_correct_size_opt; (* find_enumST ih *) () ]. 

Ltac2 derive_enumST_SizedMonotonic (_ : unit) :=
  match! goal with
  | [ |- SizedMonotonicOpt (@enumSizeST ?typ ?pred ?inst) ] =>
    assert (Henum := @enumerate_correct_size $typ);
      
    let s := Fresh.in_goal (id_of_string "s") in
    let s1 := Fresh.in_goal (id_of_string "s1") in
    let s2 := Fresh.in_goal (id_of_string "s2") in
    let s1i := Fresh.in_goal (id_of_string "s1i") in
    let s2i := Fresh.in_goal (id_of_string "s2i") in
    let hleq := Fresh.in_goal (id_of_string "Hleq") in
    let hleqi := Fresh.in_goal (id_of_string "Hleqi") in
    let ihs1 := Fresh.in_goal (id_of_string "ihs1") in
    intros $s $s1 $s2 $hleq; simpl_enumSizeST ();
      let hleq' := Control.hyp hleq in
      let s1' := Control.hyp s1 in
      let s2' := Control.hyp s2 in
      assert ($hleqi := $hleq');
      revert $hleqi $hleq;
      generalize $s2' at 1 3; generalize $s1' at 1 3; revert $s $s2; revert_params inst;
        (induction $s1' as [| $s1 $ihs1 ]; intro_params inst; intros $s $s2 $s1i $s2i $hleqi $hleq) >
        [ base_case_st_size_mon s2' | ind_case_st_sized_mon s2' ihs1  ]
  end.






Instance EnumSizedSuchThatIn'_SizedMonotonic A {_ : Enum A} l :
  SizedMonotonicOpt (@enumSizeST _ _ (EnumSizedSuchThatIn' l)).
Proof. derive_enumST_SizedMonotonic ().

       eapply incl_bigcup_compat_list.
       now enumST_sized_mon @ihs1.

       eapply incl_bigcup_compat_list.


Ltac2 rec enumST_sized_mon (ih : ident) :=
  first
    [ (* ret *)
      match! goal with
      | [ |- ?s \subset ?s ] => now eapply subset_refl
      end
    | (* dec matching *)
      match! goal with
      | [ |- semProdSizeOpt (match @decOpt ?p ?i ?s1 with _ => _ end) _ \subset
             semProdSizeOpt (match decOpt ?s2 with _ => _ end) _ ] =>
        let hdec := Fresh.in_goal (id_of_string "Hdec") in 
        destruct (@decOpt $p $i $s1) eqn:$hdec >
        [ ((erewrite (@CheckerProofs.mon $p $i _ $s1 $s2) > [ | | eassumption ]) > [ (* enumST_sized_mon ih *) | ssromega ])
        | rewrite (@semReturnSizeOpt_None E _ ProducerSemanticsEnum); now eapply sub0set ]
      end
     | (* input matching *) 
      match! goal with
      | [ |- semProdSizeOpt (match ?p with _ => _ end) _ \subset _ ] =>
        destruct $p; (* enumST_sized_mon ih *) ()
      end
    | (* bindOpt *)
      eapply (@semBindOptSizeOpt_subset_compat E _ ProducerSemanticsEnum) >
      [ first
          [ now eapply subset_refl (* for calls to enum *)
          | let ih' := Control.hyp ih in (* for recursive calls *)
            eapply $ih'; now ssromega ]
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; (* enumST_sized_mon ih *) ()
      ]
    | (* bind *)
      eapply (@semBindSizeOpt_subset_compat E _ ProducerSemanticsEnum) >
      [ now eapply subset_refl 
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; enumST_sized_mon ih
      ]
    | ()
    ].



       now enumST_sized_mon @ihs1.

Qed.




Inductive ltest : list nat -> nat -> Prop :=
  | ltestnil :
      ltest [] 0
  | ltestcons :
      forall x m' m l,
        (* eq (m' + 1) m -> *)
        In' m' l ->
        ltest l m' ->
        ltest (x :: l) m.

Derive EnumSizedSuchThat for (fun n => eq x n).
Derive EnumSizedSuchThat for (fun n => eq n x).

(* Derive DecOpt for (ltest l n). *)

(* Derive EnumSizedSuchThat for (fun n => ltest l n). *)


Set Typeclasses Debug.
QuickChickDebug Debug On.

Derive DecOpt for (ltest l n).


  
Derive EnumSizedSuchThat for (fun n => le m n).

Inductive goodTree : nat -> tree nat  -> Prop :=
| GL : forall a, goodTree 0 (Leaf nat a)
| GN :
    forall k t1 t2 n (* m : nat)*),
      (* le m n -> *)
      goodTree n t1 ->
      goodTree n t1 ->
      goodTree (S n) (Node nat k t1 t2).

Derive DecOpt for (goodTree n t).

(* XXX this fails if tree has type param A ... *) 

Instance DecOptgoodTree_listSizeMonotonic n t : DecOptSizeMonotonic (goodTree n t).
Proof. derive_mon (). Qed.

Instance DecOptgoodTree_list_sound n t : DecOptSoundPos (goodTree n t).
Proof. derive_sound (). Qed.

Instance DecOptgoodTree_list_complete n t : DecOptCompletePos (goodTree n t).
Proof. derive_complete (). Qed.

Derive EnumSizedSuchThat for (fun t => goodTree k t).


Inductive tree1 :=
| Leaf1 : tree1
| Node1 : nat -> tree1 -> tree1 -> tree1.


Inductive bst : nat -> nat -> tree1 -> Prop :=
| BstLeaf : forall n1 n2, bst n1 n2 Leaf1
| BstNode : forall min max n t1 t2,
    le min max -> le min n -> le n max ->
    bst min n t1 -> bst n max t2 ->
    bst min max (Node1 n t1 t2).


Derive DecOpt for (bst min max t).


Derive EnumSizedSuchThat for (fun t => bst min max t).



Instance EnumSizedSuchThatgoodTree_SizedMonotonic n :
  SizedMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n)).
Proof. derive_enumST_SizedMonotonic (). Qed.

Instance EnumSizedSuchThatle_SizedMonotonic n :
  SizedMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatle n)).
Proof. derive_enumST_SizedMonotonic (). Qed.

Instance EnumSizedSuchThatbst_SizedMonotonic min max :
  SizedMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatbst min max)).
Proof. derive_enumST_SizedMonotonic (). Qed.  


Instance EnumSizedSuchThatgoodTree_SizeMonotonic n :
  forall s, SizeMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n) s).
Proof. derive_enumST_SizeMonotonic (). Qed.

Instance EnumSizedSuchThatle_SizeMonotonic n :
  forall s, SizeMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatle n) s).
Proof. derive_enumST_SizeMonotonic (). Qed.

Instance EnumSizedSuchThatbst_SizeMonotonic min max :
  forall s, SizeMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatbst min max) s).
Proof. derive_enumST_SizeMonotonic (). Qed.


(* XXX predicate must be eta expanded, otherwise typeclass resolution fails *)
Instance EnumSizedSuchThatle_Correct n :
  CorrectSizedST [eta le n] (@enumSizeST _ _ (@EnumSizedSuchThatle n)).
Proof. derive_enumST_Correct (). Qed.


Instance EnumSizedSuchThatgoodTree_Correct n :
  CorrectSizedST (goodTree n) (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n)).
Proof. derive_enumST_Correct (). Qed.  



Instance EnumSizedSuchThatbst_Correct n m :
  CorrectSizedST (bst n m) (@enumSizeST _ _ (@EnumSizedSuchThatbst n m)).
Proof. derive_enumST_Correct (). Qed.
