From QuickChick Require Import QuickChick Tactics TacticsUtil Instances Classes DependentClasses Sets.

Require Import String. Open Scope string.
Require Import List micromega.Lia.


From Ltac2 Require Import Ltac2.

Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import enumProofs. (* TODO change *)

Set Bullet Behavior "Strict Subproofs".


Derive EnumSizedSuchThat for (fun n => le m n).


(* Example with two IH *)

Set Typeclasses Debug.
QuickChickDebug Debug On.

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
Proof. Admitted. (* TODO debug *) 

Instance DecOptgoodTree_list_sound n t : DecOptSoundPos (goodTree n t).
Proof. derive_sound (). Qed.

Instance DecOptgoodTree_list_complete n t : DecOptCompletePos (goodTree n t).
Proof. derive_complete (). Qed.


Derive EnumSizedSuchThat for (fun t => goodTree k t).
(* Why is it taking so much time? *) 

Lemma enumerate_SizeMonotonic (A : Type) (l : seq (E (option A))) :
  l \subset SizeMonotonic ->
  SizeMonotonic (enumerate l).
Proof.
  unfold enumerate. 
  assert (Datatypes.length l = Datatypes.length l)%coq_nat by reflexivity.  
  revert H.
  generalize (Datatypes.length l) at 2 3 4.
  intros n. revert l. induction n; intros l Heq Hsub.
  - simpl. now eauto with typeclass_instances.
  - simpl.
    eapply bindMonotonicStrong; eauto with typeclass_instances.
    
    intros x1 Hin. eapply Enumerators.semChoose in Hin; eauto. simpl in *. 
    
    destruct (Enumerators.pickDrop_exists l x1). simpl in *. now ssromega.
    destruct H. destruct H. destruct H0. destruct H1.

    rewrite H.

    eapply bindMonotonicStrong; eauto with typeclass_instances.
    
    intros a Hin'.

    destruct a; eauto with typeclass_instances. 

    eapply returnGenSizeMonotonic; eauto with typeclass_instances.

    assert (Heq' : (n.+1 - 1) = n). { ssromega. }

    rewrite Heq'. eapply IHn. 

    now ssromega.

    eapply subset_trans. eassumption. eassumption.
Qed.


Ltac2 simpl_minus_enumSizeST (_ : unit) :=
  ltac1:(with_strategy opaque [enumSizeST enum decOpt enumSizeST] simplstar).

Ltac2 simpl_enumSizeST (_ : unit) :=
  unfold enumSizeST; simpl_minus_enumSizeST (). 

Ltac2 rec enumST_size_mon (ih : ident) :=
  first
    [ (* ret *)
      eapply returnGenSizeMonotonic;
      now eauto with typeclass_instances
    | (* bindOpt *)
      eapply bindMonotonicOpt >
      [ now eauto with typeclass_instances
      | first
          [ (* for calls to enum in params *)
            now eauto with typeclass_instances 
          | (* for call to existing enum instances. XXX not sure why typeclass resulotion doesn't work *)
            eapply sizedSizeMonotonic; now eauto with typeclass_instances 
          | (* for recursive calls *)
             let ih' := Control.hyp ih in 
            eapply $ih' ]
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; enumST_size_mon ih
      ]
    | (* bind *)
      eapply bindMonotonic >
      [ now eauto with typeclass_instances
      | first
          [ (* for calls to enum in params *)
            now eauto with typeclass_instances 
          | (* for call to existing enum instances. XXX not sure why typeclass resulotion doesn't work *)
            eapply sizedSizeMonotonic; now eauto with typeclass_instances 
          | (* for recursive calls *)
             let ih' := Control.hyp ih in 
            eapply $ih' ]
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; enumST_size_mon ih
      ]
    | (* input matching *)
      match! goal with
      | [ |- SizeMonotonic (match ?p with _ => _ end) ] =>
        destruct $p; enumST_size_mon ih
      end
    | ()
    ].

Ltac2 rec enumsST_size_mon (t : constr) (ih : ident) :=
  first
    [ now eapply (@list_subset_nil (E (option $t)))
    | eapply (@list_subset_cons (E (option $t))) > 
      [ now enumST_size_mon @ih
      | enumsST_size_mon t ih ] ]. 


Ltac2 revert_params (inst : constr) :=
  match Constr.Unsafe.kind inst with
  | Constr.Unsafe.App ty args  =>
    let l := constrs_to_idents (Array.to_list args) in
    List.iter (fun x => revert $x) l; ()
  | _ => () 
  end.

Ltac2 intro_params (inst : constr) :=
  match Constr.Unsafe.kind inst with
  | Constr.Unsafe.App ty args  =>
    let l := constrs_to_idents (Array.to_list args) in
    List.iter (fun x => intro $x) (List.rev l); ()
  | _ => () 
  end.

Ltac2 derive_enumST_SizeMonotonic (_ : unit) :=
  let s := Fresh.in_goal (id_of_string "s") in
  let ihs := Fresh.in_goal (id_of_string "Ihs") in
  let si := Fresh.in_goal (id_of_string "si") in
  intro $s;
  let s' := Control.hyp s in 

  match! goal with
  | [ |- SizeMonotonic (@enumSizeST ?typ ?pred ?inst _) ] =>   
    simpl_enumSizeST (); generalize $s' at 1; revert_params inst;
    induction $s' as [ | $s $ihs ]; intro_params inst; intros $si;
       eapply enumerate_SizeMonotonic; 
       now enumsST_size_mon typ @IHs
  end.

Instance EnumSizedSuchThatgoodTree_SizeMonotonic n :
  forall s, SizeMonotonic (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n) s).
Proof. derive_enumST_SizeMonotonic (). Qed.

Lemma enumerate_correct_size_opt {A} (lst : list (E (option A))) s :
  semProdSizeOpt (enumerate lst) s <--> \bigcup_(x in lst) (semProdSizeOpt x s).
Proof.
  assert (Hc := enumerate_correct_size lst s).
  intros x. destruct (Hc (Some x)) as [H1 H2].
  split.
  - intros Hin. simpl in *.

    assert (Hin' : ((fun u : option A => u) :&: semEnumSize (enumerate lst) s) (Some x)).
    { split; eauto. }
    
    eapply Hc in Hin'. destruct Hin'. inv H. inv H3.
    eexists. split; eauto.

  - intros Hin. simpl in *.
    
    assert (Hin' : (\bigcup_(x in lst) ((fun u : option A => u) :&: semEnumSize x s)) (Some x)).
    { inv Hin. inv H. eexists; split; eauto. split; eauto. }
    
    eapply Hc in Hin'. destruct Hin'. eassumption.
Qed.       

Lemma enumerate_correct_opt {A} (lst : list (E (option A))) :
  semProdOpt (enumerate lst) <--> \bigcup_(x in lst) (semProdOpt x).
Proof.
  split; intros H.
  - inv H. inv H0.
    assert (Hin : semProdSizeOpt (enumerate lst) x a).
    { eassumption. }
    eapply (@enumerate_correct_size_opt A) in Hin.
    inv Hin. inv H0.
    eexists. split; eauto. eexists. split; eauto.
  - destruct H. destruct H. destruct H0. destruct H0.
    assert (Hin :  (\bigcup_(x in lst) (semProdSizeOpt x x0)) a).
    { eexists. split; eauto. }
    eapply (@enumerate_correct_size_opt A) in Hin.
    eexists. split; eauto. 
Qed.       


Lemma semReturnSizeOpt {G : Type -> Type} {H : Producer G} {_ : ProducerSemantics}
      (A : Type) (x : A) (size : nat) :
  semProdSizeOpt (ret (Some x)) size <--> [set x].
Proof.
  intros x1; simpl; split; intros Hin.
  - unfold semProdSizeOpt, somes in *.
    eapply semReturnSize in Hin. inv Hin. reflexivity.

  - unfold semProdSizeOpt, somes in *.
    eapply semReturnSize. inv Hin. reflexivity.
Qed. 

Lemma semReturnSizeOpt_None {G : Type -> Type}
      {H : Producer G} {_ : ProducerSemantics}
      (A : Type) (size : nat) :
  semProdSizeOpt (ret None) size <--> @set0 A.
Proof.
  intros x1; simpl; split; intros Hin.
  - unfold semProdOpt, somes in *.
    eapply semReturnSize in Hin. inv Hin.
  - inv Hin.
Qed. 

Lemma semReturnOpt {G : Type -> Type} {H : Producer G} {_ : ProducerSemantics}
      (A : Type) (x : A) :
  semProdOpt (ret (Some x)) <--> [set x].
Proof.
  intros x1; simpl; split; intros Hin.
  - unfold semProdOpt, somes in *.
    eapply semReturn in Hin. inv Hin. reflexivity.
    
  - unfold semProdOpt, somes in *.
    eapply semReturn. inv Hin. reflexivity.
Qed. 


Lemma semReturnOpt_None {G : Type -> Type}
      {H : Producer G} {_ : ProducerSemantics}
      (A : Type):
  semProdOpt (ret None) <--> @set0 A.
Proof.
  intros x1; simpl; split; intros Hin.
  - unfold semProdOpt, somes in *.
    eapply semReturn in Hin. inv Hin.
  - inv Hin.
Qed. 

Lemma semOptBind {G : Type -> Type} {H : Producer G} {_ : ProducerSemantics}
      A B (g : G A) (f : A -> G (option B)) :
  SizeMonotonic g ->
  (forall a : A, SizeMonotonic (f a)) ->
  semProdOpt (bind g f) <-->
  \bigcup_(a in semProd g) semProdOpt (f a).
Proof.
  intros Hs Hsf.
  unfold semProdOpt.
  rewrite semBindSizeMonotonic; eauto.

  split.
  - intros Hin. inv Hin. inv H1.
    eexists. split; eauto.

  - intros Hin. inv Hin. inv H1.
    eexists. split; eauto.
Qed. 

Lemma semOptBindSize {G : Type -> Type} {H : Producer G} {_ : ProducerSemantics}
      A B (g : G A) (f : A -> G (option B)) size :
  semProdSizeOpt (bind g f) size <-->
  \bigcup_(a in semProdSize g size) semProdSizeOpt (f a) size.
Proof.
  unfold semProdSizeOpt.
  rewrite semBindSize; eauto.

  split.
  - intros Hin. inv Hin. inv H1.
    eexists. split; eauto.

  - intros Hin. inv Hin. inv H1.
    eexists. split; eauto.
Qed. 

Lemma semOptBindOpt {G : Type -> Type} {H : Producer G} {_ : ProducerSemantics}
      A B (g : G (option A)) (f : A -> G (option B)) :
  SizeMonotonic g ->
  (forall a : A, SizeMonotonic (f a)) ->
  semProdOpt (bindOpt g f) <-->
  \bigcup_(a in semProdOpt g) semProdOpt (f a).
Proof.
  intros Hs Hsf.
  unfold bindOpt. rewrite semOptBind; eauto.
  
  - split. 
    + intros Hin. inv Hin. inv H1.
      destruct x. eexists. split; eauto.
      eapply semReturnOpt_None in H3. inv H3.

    + intros Hin. inv Hin. inv H1.
      eexists. split; eauto.

  - intros a; destruct a; eauto with typeclass_instances.
Qed.

Lemma semOptBindOptSize {G : Type -> Type} {H : Producer G} {_ : ProducerSemantics}
      A B (g : G (option A)) (f : A -> G (option B)) size :
  semProdSizeOpt (bindOpt g f) size <-->
  \bigcup_(a in semProdSizeOpt g size) semProdSizeOpt (f a) size.
Proof.
  unfold bindOpt. rewrite semOptBindSize; eauto.
  
  - split. 
    + intros Hin. inv Hin. inv H1.
      destruct x. eexists. split; eauto.
      eapply semReturnSizeOpt_None in H3. inv H3.

    + intros Hin. inv Hin. inv H1.
      eexists. split; eauto.
Qed. 



Ltac2 rec enums_sized_mon (ih : ident) :=
  first
    [ now eapply incl_bigcup_list_nil
    | eapply incl_bigcup_compat_list > [ | enums_sized_mon ih ] ].

Lemma semBindOptSizeOpt_subset_compat
      (G : Type -> Type) (PG : Producer G)
      { _ : ProducerSemantics }
      (A B : Type) (g g' : G (option A)) (f f' : A -> G (option B)) s : 
  semProdSizeOpt g s \subset semProdSizeOpt g' s ->
  (forall (x : A),
      semProdSizeOpt (f x) s \subset semProdSizeOpt (f' x) s) ->
  semProdSizeOpt (bindOpt g f) s \subset semProdSizeOpt (bindOpt g' f') s.
Proof.
  intros Hyp1 Hyp2.
  rewrite !semOptBindOptSize.
  eapply incl_bigcup_compat; eauto.
Qed. 

Lemma semBindSizeOpt_subset_compat
      (G : Type -> Type) (PG : Producer G)
      { _ : ProducerSemantics }
      (A B : Type) (g g' : G A) (f f' : A -> G (option B)) s : 
  semProdSize g s \subset semProdSize g' s ->
  (forall (x : A),
      semProdSizeOpt (f x) s \subset semProdSizeOpt (f' x) s) ->
  semProdSizeOpt (bind g f) s \subset semProdSizeOpt (bind g' f') s.
Proof.
  intros Hyp1 Hyp2.
  rewrite !semOptBindSize.
  eapply incl_bigcup_compat; eauto.
Qed.


Ltac2 rec enumST_sized_mon (ih : ident) :=
  first
    [ (* ret *)
      now eapply subset_refl
    | (* dec matching *)
      match! goal with
      | [ |- semProdSizeOpt (match decOpt ?s1 with _ => _ end) _ \subset
             semProdSizeOpt (match decOpt ?s2 with _ => _ end) _ ] =>
        let hdec := Fresh.in_goal (id_of_string "Hdec") in 
        destruct (decOpt $s1) eqn:$hdec >
        [ ((erewrite CheckerProofs.mon > [ | | eassumption ]) > [ enumST_sized_mon ih | ssromega ])
        | rewrite semReturnSizeOpt_None; now eapply sub0set ]
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
    ].

Ltac2 rec find_enum (ih : ident) :=
  first
    [ now eapply incl_bigcup_list_nil
    | eapply incl_bigcup_compat_list > [ now (enumST_sized_mon ih)  | find_enum ih ]
    | eapply incl_bigcup_list_tl; find_enum ih
    ].

Ltac2 base_case_size_mon (s2 : constr) :=
  destruct $s2 > 
  [ now eapply subset_refl | rewrite !enumerate_correct_size_opt; now find_enum @dummy ]. 

Ltac2 ind_case_sized_mon (s2 : constr) (ih : ident) :=
  destruct $s2 > 
  [ now ssromega |  rewrite !enumerate_correct_size_opt; now find_enum ih ]. 

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
      assert ($hleqi := $hleq'); revert $hleqi $hleq;
      generalize $s2' at 1 3; generalize $s1' at 1 3; revert $s $s2; revert_params inst;
        (induction $s1' as [| $s1 $ihs1 ]; intro_params inst; intros $s $s2 $s1i $s2i $hleqi $hleq) >
        [ base_case_size_mon s2' | ind_case_sized_mon s2' ihs1 ]
  end.


Instance EnumSizedSuchThatgoodTree_SizedMonotonic n :
  SizedMonotonicOpt (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n)).
Proof. now derive_enumST_SizedMonotonic (). Qed. 


Class CorrectSizedST {A : Type} (P : A -> Prop) {G} `{Producer G} (g : nat -> G (option A)) :=
  { corrST : [ set x | exists s, semProdOpt (g s) x ]  <-->  [set x : A | P x ] }.


Instance EnumSizedSuchThatgoodTree_SizedMonotonic n :
  CorrectSizedST (goodTree n) (@enumSizeST _ _ (@EnumSizedSuchThatgoodTree n)).
Proof.
  match! goal with
  | [ |- CorrectSizedST _ (@enumSizeST ?typ ?pred ?inst) ] =>
    assert (Henum := @enumerate_correct_opt $typ);

    let x := Fresh.in_goal (id_of_string "x") in
        
    
    simpl_enumSizeST (); (); split; intros $x; split >
      [ (* sound *) | (* complete *) admit ]
  end.


  Ltac2 sound_enumST (_ : unit) :=
    let s := Fresh.in_goal (id_of_string "s") in
    let si := Fresh.in_goal (id_of_string "si") in
    let ihs := Fresh.in_goal (id_of_string "ihs") in
    let hgen := Fresh.in_goal (id_of_string "Hgen") in
    intros [$s $hgen]; revert $hgen;

    let s' := Control.hyp s in

    generalize $s' at 1; induction $s' as [ | $s $ihs]; intros $si $hgen;
    eapply &Henum in $hgen.
  
  sound_enumST ().
  
  rewrite Henum in Hgen. 
  erewrite enumerate_correct_opt in Hgen.

  Focus 2. 
  revert $hgen. 
  
  now derive_enumST_SizedMonotonic (). Qed. 

           
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


Definition test min_ max_:=
  (let
   fix aux_arb init_size size0 (min_ : nat) (max_ : nat) : E (Coq.Init.Datatypes.option (tree1)) :=
     match size0 with
     | O => enumerate (Coq.Lists.List.cons
                         (@returnEnum (option (tree1)) (@Some (tree1) (@Leaf1))) Coq.Lists.List.nil)
     | S size' =>
         enumerate
           (Coq.Lists.List.cons (@returnEnum (option (tree1)) (@Some (tree1) (@Leaf1)))
              (Coq.Lists.List.cons
                 match @decOpt (@le min_ max_) _ init_size as s with
                 | Some res_b =>
                     match res_b with
                     | true =>
                         @bindEnumOpt nat tree1 (@enumSuchThat _ (fun n => @le min_ n) _)
                           (fun n =>
                            match @decOpt (@le n max_) _ init_size as s return E (Coq.Init.Datatypes.option (tree1)) with
                            | Some res_b =>
                                match res_b with
                                | true =>
                                    @bindEnumOpt tree1 tree1 (aux_arb init_size size' min_ n)
                                      (fun t1 =>
                                      @bindEnumOpt tree1 tree1 (aux_arb init_size size' n max_)
                                         (fun t2 => @returnEnum (option (tree1)) (@Some (tree1) (@Node1 n t1 t2))))
                                | false => @returnEnum (option (tree1)) (@None (tree1))
                                end
                            | None => @returnEnum (option (tree1)) (@None (tree1))
                            end)
                     | false => @returnEnum (option (tree1)) (@None (tree1))
                     end
                 | None => @returnEnum (option (tree1)) (@None (tree1))
                 end Coq.Lists.List.nil))
     end in
 fun size0 => aux_arb size0 size0 min_ max_).

  let
    fix aux_arb (init_size size0 min_0 max_0 : nat) {struct size0} : E (option tree1) :=
    match size0 with
    | 0 => enumerate [:: returnEnum (Some Leaf1)]
    | size'.+1 =>
      enumerate
        [:: returnEnum (Some Leaf1);
        match decOpt init_size with
        | Some true =>
          bindEnumOpt (enumST [eta le min_0])
                      (fun n : nat =>
                         match decOpt init_size with
                         | Some true =>
                           bindEnumOpt (aux_arb init_size size' min_0 n)
                                       (fun t1 : tree1 =>
                                          bindEnumOpt (aux_arb init_size size' n max_0)
                                                      (fun t2 : tree1 => returnEnum (Some (Node1 n t1 t2))))
                         | _ => returnEnum None
                         end)
        | _ => returnEnum None
        end]
    end in
  fun size0 : nat => aux_arb size0 size0 min_ max_.
