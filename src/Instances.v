Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From Coq Require Import
     Arith
     Basics
     List
     Recdef
     ZArith
     Lia.
From mathcomp Require Import
     ssrbool
     ssreflect
     ssrnat.
From QuickChick Require Import
     Classes
     Sets
     Producer
     Enumerators
     Generators
     Tactics.

Import ListNotations QcDefaultNotation.
Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".

(** Basic generator instances *)
#[global] Instance genBoolSized : GenSized bool :=
  {| arbitrarySized x := elems_ true [true; false] |}.

#[global] Instance genNatSized : GenSized nat :=
  {| arbitrarySized x := choose (0,x) |}.

#[global] Instance genZSized : GenSized Z :=
  {| arbitrarySized x := let z := Z.of_nat x in
                         choose (-z, z)%Z |}.

#[global] Instance genNSized : GenSized N :=
  {| arbitrarySized x := let n := N.of_nat x in
                         choose (N0, n) |}.

#[global] Instance genListSized {A : Type} `{GenSized A} : GenSized (list A) :=
  {| arbitrarySized x := listOf (arbitrarySized x) |}.

(* [3] is a lower priority than [Classes.GenOfGenSized],
   avoiding an infinite loop in typeclass resolution. *)

#[global] Instance genList {A : Type} `{Gen A} : Gen (list A) | 3 :=
  {| arbitrary := listOf arbitrary |}.

#[global] Instance genOption {A : Type} `{Gen A} : Gen (option A) | 3 :=
  {| arbitrary := freq [ (1, ret None)
                       ; (7, liftM Some arbitrary)] |}.

#[global] Instance genPairSized {A B : Type} `{GenSized A} `{GenSized B}
: GenSized (A*B) :=
  {| arbitrarySized x :=
       liftM2 pair (arbitrarySized x)
                   (arbitrarySized x)
  |}.

#[global] Instance genPair {A B : Type} `{Gen A} `{Gen B} : Gen (A * B) :=
  {| arbitrary := liftM2 pair arbitrary arbitrary |}.

(* Enumerator #[global] Instances *)

#[global] Instance enumBoolSized : EnumSized bool :=
  {| enumSized x := elems_ true [true; false] |}.

#[global] Instance enumNatSized : EnumSized nat :=
  {| enumSized x := chooseEnum (0,x) |}.

#[global] Instance enumZSized : EnumSized Z :=
  {| enumSized x := let z := Z.of_nat x in
                         chooseEnum (-z, z)%Z |}.

#[global] Instance enumNSized : EnumSized N :=
  {| enumSized x := let n := N.of_nat x in
                         chooseEnum (N0, n) |}.

#[global] Instance enumListSized {A : Type} `{Enum A} : EnumSized (list A) :=
  {| enumSized x := bindEnum (choose (0,x)) (fun x => vectorOf x enum) |}.

(* [3] is a lower priority than [Classes.EnumOfEnumSized],
   avoiding an infinite loop in typeclass resolution. *)

#[global] Instance enumList {A : Type} `{Enum A} : Enum (list A) | 3 :=
  {| enum := listOf enum |}.

#[global] Instance enumOption {A : Type} `{Enum A} : Enum (option A) | 3 :=
  {| enum := oneOf [ (ret None)
                   ; (liftM Some enum)] |}.

#[global] Instance enumPairSized {A B : Type} `{EnumSized A} `{EnumSized B}
: EnumSized (A*B) :=
  {| enumSized x :=
       liftM2 pair (enumSized x)
                   (enumSized x)
  |}.

#[global] Instance enumPair {A B : Type} `{Enum A} `{Enum B} : Enum (A * B) :=
  {| enum := liftM2 pair enum enum |}.


#[global] Instance enumOpt {A} (H : Enum A) : Enum (option A) :=
  {| enum :=
       match enum with
       | MkEnum f => MkEnum (fun n => LazyList.lcons None (fun _ => LazyList.mapLazyList Some (f n)))
       end
  |}.


(** Shrink#[global] Instances *)
#[global] Instance shrinkBool : Shrink bool :=
  {| shrink x :=
       match x with
         | false => nil
         | true  => cons false nil
       end
  |}.


#[global] Instance enumOptCorrect A `{EnumCorrect A} :
  Correct _ (@enum _ (enumOpt _)).
Proof.
  constructor.  
  intros t; split; eauto.
  - intros. exact I.
  - intros _. 
    simpl.
    inv H. inv H0. unfold semProd. simpl.
    destruct t.
    + destruct (prodCorrect a).
      destruct H3. now reflexivity.
      inv H3. simpl in *.
      eexists x. split. eassumption.
      destruct H. simpl in *. destruct enum0.
      unfold semEnumSize in *. simpl. right.
      eapply LazyList.lazy_in_map_iff.
      eexists. split. reflexivity.
      eassumption.
    + exists 0. split. reflexivity.
      destruct H. simpl. destruct enum0.
      unfold semEnumSize in *. simpl. left. reflexivity.
Qed.       

#[global] Instance enumOpt_SizeMonotonic A `{EnumMonotonic A} :
  SizeMonotonic (@enum _ (enumOpt _)).
Proof.
  destruct H. destruct enum. simpl in *. 
  intros s1 s2 Hleq [ x |]; simpl.
  - eapply H0 in Hleq. simpl in *.
    intros Hin.
    unfold semEnumSize in *. simpl in *. right.
    inv Hin; try congruence.
    eapply LazyList.lazy_in_map_iff.
    eexists. split. reflexivity.
    eapply Hleq.
    eapply LazyList.lazy_in_map_iff in H. destruct H.
    inv H. inv H2. eassumption.
  - unfold semEnumSize in *. simpl in *. firstorder.
Qed.

#[global] Instance enumOpt_SizeFP A `{Enum A} :
  SizeFP (@enum _ (enumOpt _)).
Proof.
  destruct H. destruct enum. simpl in *.
  
  intros s1 s2 Hleq Hnin. simpl.
  unfold semEnumSize in *. simpl in *. firstorder.
Qed.


#[global] Instance enumNatSized_CorrectSized :
  CorrectSized (@enumSized _ enumNatSized).
Proof.
  constructor. 
  intros t; split; eauto.
  - intros. exact I.
  - intros _. 
    
      assert (Hsize := @Enumerators.semChooseSize nat _).
      simpl in *.
      
      exists t. exists t. split. exact I. eapply Hsize.
      reflexivity. ssromega.
Qed.       

#[global] Instance enumNatSized_SizedMonotonic :
  SizedMonotonic (@enumSized _ enumNatSized).
Proof.
  intros s s1 s2 Hleq. simpl.
  intros x Hin.
    
  assert (Hsize := @Enumerators.semChooseSize nat _).
  eapply Hsize in Hin; eauto.
  simpl in Hin.
  eapply Hsize.
  reflexivity.
  simpl.
  ssromega.
Qed.

#[global] Instance enumNatSized_SizeMonotonic s:
  SizeMonotonic (@enumSized _ enumNatSized s).
Proof.
  intros s1 s2 Hleq. simpl.
  intros x Hin.

  assert (Hsize := @Enumerators.semChooseSize nat _).
  eapply Hsize in Hin; eauto.
  simpl in Hin.
  eapply Hsize. reflexivity. simpl.
  ssromega.
Qed.

(* TODO. These case be derived automatically. Change the default definitions *)

#[global] Instance enumListSized_SizedMonotonic A `{EnumMonotonic A} :
  SizedMonotonic (@enumSized (list A) enumListSized).
Proof.
  intros s s1 s2 Hleq x Hin.
  eapply semBindSizeEnum in Hin. destruct Hin as [a [Hin He]].
  assert (Hvec := @semVectorOfSize E _ _). eapply Hvec in He. destruct He as [Heq Hin'].
  eapply semBindSizeEnum. exists a. split.
  eapply Enumerators.semChooseSize in Hin. simpl in *.
  eapply Enumerators.semChooseSize. now eauto.
  simpl. now ssromega. now eauto.
  eapply Hvec. split; eauto.
Qed. 
 

#[global] Instance enumListSized_SizeMonotonic A `{EnumMonotonic A} s :
  SizeMonotonic (@enumSized (list A) enumListSized s).
Proof.
  eapply bindMonotonic; eauto with typeclass_instances.
Qed.


#[global] Instance enumListSized_CorrectSized A `{EnumMonotonicCorrect A} :
  CorrectSized (@enumSized (list A) enumListSized).
Proof.
  assert (Hvec := @semVectorOfSize E _ _).
  constructor. intros l; induction l; simpl.
  - split; intros Hin; simpl in *. now constructor.
    eexists 0. eexists 0. split; eauto.
    eapply semBindSizeEnum. eexists. split.
    eapply Enumerators.semChooseSize. now eauto.
    2:{ eapply Hvec. split. reflexivity. eapply sub0set. }
    now eauto.
  - split; intros Hin. now constructor.
    destruct IHl as [_ IHl].
    edestruct IHl as [x [s1 [Hin1 He]]]. now constructor.
    eapply semBindSizeEnum in He.
    destruct He as [y [Hen Hv]].
    eapply Hvec in Hv; eauto with typeclass_instances. destruct Hv as [Heq Hinl].
    subst.
    eapply Enumerators.semChooseSize in Hen; eauto. simpl in *.

    destruct H2. destruct H1. edestruct prodCorrect with (a := a).
    edestruct H2 as [s2 [ _ Hin'] ]. reflexivity.
      
    eexists (x + 1). eexists (s1 + s2). split. reflexivity.
    eapply semBindSizeEnum. exists (length l+1). split.
    eapply Enumerators.semChooseSize; eauto. simpl in *. ssromega.
    eapply Hvec. split. simpl. now ssromega.
    eapply cons_subset.

    eapply H0; [| eassumption ].  now ssromega.

    eapply subset_trans. eassumption.
    eapply H0. now ssromega. 
Qed.

#[global] Instance enumPairSized_SizedMonotonic A {_ : EnumSized A} { _ : SizedMonotonic (@enumSized A _)}
  B {_ : EnumSized B} { _ : SizedMonotonic (@enumSized B _)}:
  SizedMonotonic (@enumSized (A * B) enumPairSized).
Proof.
  intros s s1 s2 Hleq.
  simpl. rewrite !semBindSizeEnum.
  eapply incl_bigcup_compat; eauto.
  intros x.
  simpl. rewrite !semBindSizeEnum.
  eapply incl_bigcup_compat; eauto.
  intros y. eapply subset_refl.
Qed.

#[global] Instance enumPairSized_SizeMonotonic A {_ : EnumSized A} { _ : forall s, SizeMonotonic (@enumSized A _ s)}
         B {_ : EnumSized B} { _ : forall s, SizeMonotonic (@enumSized B _ s)} s :
  SizeMonotonic (@enumSized (A * B) enumPairSized s).
Proof.
  eapply bindMonotonic; eauto with typeclass_instances.
  intros x.
  eapply bindMonotonic; eauto with typeclass_instances.
  intros y. eapply returnGenSizeMonotonic; eauto with typeclass_instances.  
Qed.

#[global] Instance enumPairSized_CorrectSized
         A {_ : EnumSized A} { _ : forall s, SizeMonotonic (@enumSized A _ s)}
         { _ : SizedMonotonic (@enumSized A _)} { _ : CorrectSized (@enumSized A _)}
         B {_ : EnumSized B} { _ : forall s, SizeMonotonic (@enumSized B _ s)}
         { _ : SizedMonotonic (@enumSized B _)} { _ : CorrectSized (@enumSized B _)}:
  CorrectSized (@enumSized (A * B) enumPairSized).
Proof.
  constructor. split.
  { intros. reflexivity. }
  destruct a.
  intros _.
  destruct H1 as [[_ Hca]]. 
  destruct H4 as [[_ Hcb]].
  destruct Hca as [x1 [s1 [_ Hin1]]]. reflexivity.
  destruct Hcb as [x2 [s2 [_ Hin2]]]. reflexivity.
  eexists (x1 + x2). simpl. eexists (s1 + s2). split. reflexivity.
  simpl. eapply semBindSizeEnum.
  eexists. split.
  eapply H0. 2:{ eapply H; [| eassumption ]. ssromega. }
  ssromega.
  eapply semBindSizeEnum.
  eexists. split.
  eapply H2. 2:{ eapply H3; [| eassumption ]. ssromega. }
  ssromega.
  eapply semReturnSizeEnum. reflexivity. 
Qed.       


#[global] Instance enumOption_SizeMonotonic A {_ : Enum A} { _ : SizeMonotonic (@enum A _)} :
  SizeMonotonic (@enum (option A) enumOption).
Proof.
  simpl. eapply oneofMonotonic; eauto with typeclass_instances.
  eapply returnGenSizeMonotonic; eauto with typeclass_instances.
  eapply cons_subset.
  eapply returnGenSizeMonotonic; eauto with typeclass_instances.
  eapply cons_subset.
  eapply bindMonotonic; eauto with typeclass_instances.
  intros y. eapply returnGenSizeMonotonic; eauto with typeclass_instances.  
  eapply sub0set.
Qed.

 
#[global] Instance enumOption_Correct A {_ : Enum A} { _ : Correct A (@enum A _)}:
  Correct _ (@enum (option A) enumOption).
Proof.
  constructor. split. intros. reflexivity.
  intros _.
  simpl. destruct a.
  - destruct H as [ [ _ Hc ] ]. destruct Hc as [x [H1 H2]]. reflexivity.
    eexists x. split. reflexivity.
    eapply semOneofSize. eauto with typeclass_instances.
    eexists. split. right. left.
    eexists. eapply semBindSizeEnum. eexists. split. eassumption.
    eapply semReturnSizeEnum. reflexivity.
  - exists 0. split. reflexivity.
    eapply semOneofSize. eauto with typeclass_instances.
    eexists. split. left. reflexivity.
    eapply semReturnSizeEnum. reflexivity.
Qed.       

Lemma andb_len x1 x2 x3 x4 : 
  (x1 <=? x2)%num && (x3 <=? x4)%num <-> (x1 <= x2)%num /\ (x3 <= x4)%num.
Proof.
  destruct (x1 <=? x2)%num eqn:Heq1; simpl; split; try easy;
    destruct (x3 <=? x4)%num eqn:Heq2; simpl; try easy.
  - eapply N.leb_le in Heq1. eapply N.leb_le in Heq2.
    easy.
  - intros [H1 H2]. eapply N.leb_nle in Heq2.
    eauto.
  - intros [H1 H2]. eapply N.leb_nle in Heq1. eauto.
  - intros [H1 H2]. eapply N.leb_nle in Heq1. eauto.
Qed.   

#[global] Instance enumNSized_SizedMonotonic :
  SizedMonotonic (@enumSized _ enumNSized).
Proof. 
  intros s s1 s2 Hleq. simpl.
  intros x Hin.
  assert (Hsize := @Enumerators.semChooseSize N _).
  eapply Hsize in Hin; eauto.
  simpl in Hin. 
  eapply Hsize. simpl in *.
  eapply N.leb_le. now lia. 
  eapply andb_len in Hin. eapply andb_len. ssromega.
  simpl. eapply N.leb_le. ssromega. 
Qed. 

#[global] Instance enumNSized_SizeMonotonic s:
  SizeMonotonic (@enumSized _ enumNSized s).
Proof.
  intros s1 s2 Hleq. simpl.
  intros x Hin.

  assert (Hsize := @Enumerators.semChooseSize N _).
  
  eapply Hsize in Hin; eauto.
  simpl in Hin.
  eapply Hsize. simpl. eapply N.leb_le. ssromega.
  eapply andb_len in Hin. eapply andb_len. split; ssromega.
  eapply N.leb_le. ssromega.
Qed.

(* Lemma of_nat_bin t : *)
(*   (N.of_nat (nat_of_bin t)) = t. *)
(* Proof. *)
(*   destruct t. reflexivity. *)
(*   simpl. *)
(*   induction p; simpl. *)
(*   - admit. *)
(*   -  *)
  
#[global] Instance enumNSized_CorrectSized :
  CorrectSized (@enumSized _ enumNSized).
Proof.
  constructor. 
  intros t; split; eauto.
  - intros. exact I.
  - intros _. 
    
      assert (Hsize := @Enumerators.semChooseSize N _).
      simpl in *.
      
      exists (N.to_nat t). exists 0 . split. exact I. eapply Hsize.
      eapply N.leb_le. ssromega.
      eapply andb_len. split; ssromega.
Qed.       
  
#[global] Instance enumBoolSized_SizeMonotonic s:
  SizeMonotonic (@enumSized _ enumBoolSized s).
Proof.
  intros s1 s2 Hleq.
  assert ( Heq := @semElementsSize E _ _).
  simpl in *. rewrite Heq.
  eapply subset_refl.
Qed.

#[global] Instance enumBoolSized_CorrectSized :
  CorrectSized (@enumSized _ enumBoolSized).
Proof.
  constructor. 
  intros t; split; eauto.
  - intros. exact I.
  - intros _. 
    destruct t; exists 0; simpl;
    eapply semElements; eauto with typeclass_instances.
    now left.
    right. now left.
Qed.       


#[global] Instance enumBoolSized_SizedMonotonic :
  SizedMonotonic (@enumSized _ enumBoolSized).
Proof.
  intros s s1 s2 Hleq. simpl.
  assert ( Heq := @semElementsSize E _ _).
  simpl in *. rewrite Heq.
  eapply subset_refl.
Qed.


(** Shrinking of nat starts to become annoying *)
Function shrinkNatAux (x : nat) {measure (fun x => x) x} : list nat :=
  match x with
    | O => nil
    | S n =>
      let x' := Nat.div x 2 in
      x' :: shrinkNatAux x'
  end.
Proof.
  move => x n Eq;
  pose proof (Nat.divmod_spec n 1 0 0) as H.
  assert (H' : (0 <= 1)%coq_nat) by lia; apply H in H';
  subst; simpl in *; clear H.
  destruct (Nat.divmod n 1 0 0) as [q u];  destruct u; simpl in *; lia.
Defined.

#[global] Instance shrinkNat : Shrink nat :=
  {| shrink := shrinkNatAux |}.

(** Shrinking of Z is even more so *)
Lemma abs_div2_pos : forall p, Z.abs_nat (Z.div2 (Z.pos p)) = Nat.div2 (Pos.to_nat p).
Proof.
  intros. destruct p.
    rewrite /Z.div2 /Pos.div2.
      rewrite /Z.abs_nat. rewrite Pos2Nat.inj_xI.
      rewrite <- Nat.add_1_r. rewrite mult_comm.
      rewrite Nat.div2_div. rewrite Nat.div_add_l; simpl; lia.
    rewrite /Z.div2 /Pos.div2.
      rewrite /Z.abs_nat. rewrite Pos2Nat.inj_xO.
      rewrite mult_comm. rewrite Nat.div2_div. rewrite Nat.div_mul. reflexivity. lia.
  reflexivity.
Qed.

Lemma neg_succ : forall p,
  Z.neg (Pos.succ p) = Z.pred (Z.neg p).
Proof.
  move => p. rewrite <- Pos.add_1_r.
  rewrite <- Pos2Z.add_neg_neg.
  rewrite <- Z.sub_1_r.
  reflexivity.
Qed.

Lemma neg_pred : forall p, (p > 1)%positive ->
  Z.neg (Pos.pred p) = Z.succ (Z.neg p).
Proof.
  move => p Hp. destruct p using Pos.peano_ind. by inversion Hp.
  rewrite Pos.pred_succ. rewrite neg_succ. rewrite Z.succ_pred.
  reflexivity.
Qed.

Lemma abs_succ_neg : forall p,
  Z.abs_nat (Z.succ (Z.neg p)) = Nat.pred (Pos.to_nat p).
Proof.
  move => p. destruct p using Pos.peano_ind. reflexivity.
  rewrite -neg_pred /Z.abs_nat. rewrite Pos2Nat.inj_pred. reflexivity.
  apply Pos.lt_1_succ. apply Pos.lt_gt; apply Pos.lt_1_succ.
Qed.

Lemma abs_succ_div2_neg : forall p,
  Z.abs_nat (Z.succ (Z.div2 (Z.neg p))) = Nat.div2 (Pos.to_nat p) \/
  Z.abs_nat (Z.succ (Z.div2 (Z.neg p))) = Nat.pred (Nat.div2 (Pos.to_nat p)).
Proof.
  intros. destruct p.
    left. rewrite /Z.div2 /Pos.div2.
      rewrite neg_succ. rewrite <- Zsucc_pred. rewrite /Z.abs_nat. rewrite Pos2Nat.inj_xI.
      rewrite <- Nat.add_1_r. rewrite mult_comm.
      rewrite Nat.div2_div. rewrite Nat.div_add_l; simpl; lia.
    right. rewrite /Z.div2 /Pos.div2.
      rewrite Pos2Nat.inj_xO. rewrite mult_comm.
      rewrite Nat.div2_div. rewrite Nat.div_mul. simpl.
      apply abs_succ_neg. lia.
  left. simpl. reflexivity.
Qed.

Function shrinkZAux (x : Z) {measure (fun x => Z.abs_nat x) x}: list Z :=
  match x with
    | Z0 => nil
    | Zpos _ => rev (cons (Z.pred x) (cons (Z.div2 x) (shrinkZAux (Z.div2 x))))
    | Zneg _ => rev (cons (Z.succ x) (cons (Z.succ (Z.div2 x)) (shrinkZAux (Z.succ (Z.div2 x)))))
  end.
Proof.
  move => ? p ?. subst. rewrite abs_div2_pos. rewrite Zabs2Nat.inj_pos.
    rewrite Nat.div2_div. apply Nat.div_lt. apply Pos2Nat.is_pos. lia.
  move => ? p ?. subst. destruct (abs_succ_div2_neg p) as [H | H].
    rewrite {}H /Z.abs_nat. rewrite Nat.div2_div.
      apply Nat.div_lt. apply Pos2Nat.is_pos. lia.
    rewrite {}H /Z.abs_nat. eapply le_lt_trans. apply le_pred_n. rewrite Nat.div2_div.
      apply Nat.div_lt. apply Pos2Nat.is_pos. lia.
Qed.

#[global] Instance shrinkZ : Shrink Z :=
  {| shrink := shrinkZAux |}.

Open Scope program_scope.

#[global] Instance shrinkN : Shrink N :=
  {| shrink := map Z.to_N ∘ shrink ∘ Z.of_N |}.

Definition shrinkListAux {A : Type} (shr : A -> list A) : list A -> list (list A) :=
  fix shrinkListAux_ (l : list A) : list (list A) :=
    match l with
    | nil => nil
    | cons x xs =>
      xs :: map (fun xs' => cons x xs') (shrinkListAux_ xs)
         ++ map (fun x'  => cons x' xs) (shr x )
    end.

#[global] Instance shrinkList {A : Type} `{Shrink A} : Shrink (list A) :=
  {| shrink := shrinkListAux shrink |}.

#[global] Instance shrinkPair {A B} `{Shrink A} `{Shrink B} : Shrink (A * B) :=
  {|
    shrink := fun (p : A * B) =>
      let (a,b) := p in
      map (fun a' => (a',b)) (shrink a) ++ map (fun b' => (a,b')) (shrink b)
  |}.

#[global] Instance shrinkOption {A : Type} `{Shrink A} : Shrink (option A) :=
  {| shrink m :=
       match m with
         | None => []
         | Some x => None :: (map Some (shrink x))
       end
  |}.

(** Arbitraries are derived automatically! *)


(**#[global] Instance correctness *)

(* Needed to add this! *)
Opaque semProdSize.

#[global] Program Instance arbNatMon :
  @SizeMonotonic nat G ProducerGen (@arbitrary nat _).
Next Obligation.
  rewrite !semSizedSize !semChooseSize // => n /andP [/leP H1 /leP H2].
  move : H => /leP => Hle. apply/andP.
  split; apply/leP; ssromega.
Qed.

(** Correctness proof about built-in generators *)

#[global] Instance boolSizeMonotonic : SizeMonotonic (@arbitrary bool _).
Proof.
  unfold arbitrary, GenOfGenSized.
  eapply sizedSizeMonotonic; unfold arbitrarySized, genBoolSized.
  - eauto with typeclass_instances.
  - intros; eauto with typeclass_instances.
  - intros n s1 s2 Hs. eapply subset_refl.
Qed.

#[global] Instance boolSizedMonotonic : SizedMonotonic (@arbitrarySized bool _).
Proof.
  intros n s1 s2 Hs. eapply subset_refl.
Qed.

#[global] Instance boolCorrect : Correct bool arbitrary.
Proof.
  constructor. unfold arbitrary, GenOfGenSized.
  rewrite semSized.
  unfold arbitrarySized, genBoolSized.
  intros x. split; intros H; try now constructor.
  exists 0. split. constructor.
  eapply semElementsSize; eauto with typeclass_instances.
  destruct x; try solve [left; auto]; right; left; auto.
Qed.

Local Open Scope set_scope.

Lemma arbBool_correct:
  semProd arbitrary <--> [set: bool].
Proof.
rewrite /arbitrary /arbitrarySized /genBoolSized /=.
rewrite semSized => n; split=> // _.
exists n; split=> //.
apply semElementsSize => //=;
                           eauto with typeclass_instances.
destruct n; repeat (try solve [left; auto]; right).
Qed.

Lemma arbNat_correct:
  semProd arbitrary <--> [set: nat].
Proof.
rewrite /arbitrary /=.
rewrite semSized => n; split=> // _; exists n; split=> //.
by rewrite (semChooseSize _ _ _) /RandomQC.leq /=.
Qed.

#[global] Instance ArbNatGenCorrect : Correct nat arbitrary.
Proof.
  constructor. now apply arbNat_correct.
Qed.

Lemma arbInt_correct s :
  semProdSize arbitrary s <-->
  [set z | (- Z.of_nat s <= z <= Z.of_nat s)%Z].
Proof.
rewrite semSizedSize semChooseSize.
  by move=> n; split=> [/andP|] [? ?]; [|apply/andP]; split; apply/Zle_is_le_bool.
apply/(Zle_bool_trans _ 0%Z); apply/Zle_is_le_bool.
  exact/Z.opp_nonpos_nonneg/Zle_0_nat.
exact/Zle_0_nat.
Qed.

Lemma arbBool_correctSize s :
  semProdSize arbitrary s <--> [set: bool].
Proof.
rewrite /arbitrary //=.
rewrite semSizedSize semElementsSize //; split=> /RandomQC.leq _ //=; case a=> //=.
repeat (try solve [left; auto]; right).
repeat (try solve [left; auto]; right).
Qed.

Lemma arbNat_correctSize s :
  semProdSize arbitrary s <--> [set n : nat | (n <= s)%coq_nat].
Proof.
by rewrite semSizedSize semChooseSize // => n /=; case: leP.
Qed.

Lemma arbInt_correctSize : semProd arbitrary <--> [set: Z].
Proof.
rewrite /arbitrarySized semSized => n; split=> // _; exists (Z.abs_nat n); split=> //.
simpl.
rewrite Nat2Z.inj_abs_nat (semChooseSize _ _ _).
  by case: n => //= p; rewrite !Z.leb_refl.
apply/(Zle_bool_trans _ 0%Z); apply/Zle_is_le_bool.
  exact/Z.opp_nonpos_nonneg/Z.abs_nonneg.
exact/Z.abs_nonneg.
Qed.

Lemma arbList_correct:
  forall {A} `{H : Arbitrary A} (P : nat -> A -> Prop) s,
    (semProdSize arbitrary s <--> P s) ->
    (semProdSize arbitrary s <-->
     (fun (l : list A) => length l <= s /\ (forall x, List.In x l -> P s x))).
Proof.
  move => A G S H P s Hgen l.
  rewrite !/arbitrary /genList.
  split.
  - move => /semListOfSize [Hl Hsize]. split => // x HIn //=. apply Hgen. auto.
  - move => [Hl HP].
    apply semListOfSize; eauto with typeclass_instances.
    split => // x HIn.
    apply Hgen. auto.
Qed.

Opaque ret.
Opaque liftM.
Lemma arbOpt_correct:
  forall {A} `{H : Arbitrary A} (P : nat -> A -> Prop) s,
    (semProdSize arbitrary s <--> P s) ->
    (semProdSize arbitrary s <-->
     (fun (m : option A) =>
        match m with
          | None => true
          | Some x => P s x
        end)).
Proof.
  move => A G S Arb P s Hgen m. rewrite !/arbitrary /genOption; split.
  - move => /semFrequencySize [[w g] H2].
    move: H2 => [[H2 | [H2 | H2]] H3];
    destruct m => //=; apply Hgen => //=;
    inversion H2; subst; auto; simpl in *.
    + apply (@semReturnSize Generators.G ProducerGen ProducerSemanticsGen (option A) _) in H3; inversion H3.
    + apply semLiftProdSize in H3; eauto with typeclass_instances. inversion H3 as [x [H0 H1]].
      inversion H1; subst; auto.
  - destruct m eqn:Hm; simpl in *; move => HP; subst.
    + apply semFrequencySize; simpl.
      exists (7, liftM Some arbitrary); split; auto.
      * right; left; auto.
      * simpl. apply semLiftProdSize; simpl;
                 eauto with typeclass_instances.
        apply imset_in; apply Hgen; auto.
    + apply semFrequencySize; simpl.
      exists (1, ret None); split; auto.
      * left; auto.
      * simpl.
        apply (@semReturnSize Generators.G ProducerGen ProducerSemanticsGen). constructor.
Qed.

Lemma arbPair_correctSize
      {A B} `{Arbitrary A} `{Arbitrary B} (Sa : nat -> set A)
      (Sb : nat -> set B) s:
    (semProdSize arbitrary s <--> Sa s) ->
    (semProdSize arbitrary s <--> Sb s) ->
    (semProdSize arbitrary s <--> setX (Sa s) (Sb s)).
Proof.
  move => Hyp1 Hyp2 .
  Opaque liftM2.
  simpl.
  rewrite semLiftProd2Size; move => [a b].
  split.
  by move => [[a' b'] [[/= /Hyp1 Ha /Hyp2 Hb] [Heq1 Heq2]]]; subst; split.
  move => [/Hyp1 Ha /Hyp2 Hb]. eexists; split; first by split; eauto.
  reflexivity.
Qed.
