Require Import Arbitrary Random GenLow.
Import GenLow.

Require Import PArith.
Require Import List.
Import ListNotations.

(* LL: TODO: Add proof obligation that the result paths be prefix free? *)
Class CoArbitrary (A : Type) : Type :=
  {
    coarbitrary : A -> positive;
    coarbReverse : positive -> option A;
    coarbCorrect : forall a, coarbReverse (coarbitrary a) = Some a
  }.

Instance coArbPos : CoArbitrary positive := 
  {|
    coarbitrary x := x;
    coarbReverse x := Some x
  |}.
Proof. auto. Qed.

Local Open Scope positive.
Fixpoint posToPathAux (p : positive) : SplitPath := 
  match p with 
    | xH => []
    | xI p' => posToPathAux p' ++ [Left; Right]
    | xO p' => posToPathAux p' ++ [Left; Left ]
  end.

Definition posToPath (p : positive) : SplitPath := posToPathAux p ++ [Right].

Fixpoint pathToPosAux (p : SplitPath) (f : positive -> positive) 
: option positive :=
match p with 
  | [Right] => Some (f xH)
  | Left :: Right :: p' => pathToPosAux p' (fun p => xI (f p))
  | Left :: Left  :: p' => pathToPosAux p' (fun p => xO (f p))     
  | _ => None
end.

Definition pathToPos p := pathToPosAux p (fun x => x).

(*
Eval compute in (pathToPos (posToPath 1)).
Eval compute in (pathToPos (posToPath 2)).
Eval compute in (pathToPos (posToPath 3)).
Eval compute in (pathToPos (posToPath 4)).
Eval compute in (pathToPos (posToPath 5)).
Eval compute in (pathToPos (posToPath 6)).
Eval compute in (pathToPos (posToPath 7)).
Eval compute in (pathToPos (posToPath 8)).
Eval compute in (pathToPos (posToPath 9)).
*)

Definition list_ind' (A : Type) (P : list A -> Prop) : 
                    P [] -> (forall (a : A), P [a]) -> 
                    (forall (a b : A) (l : list A), P l -> P (a :: b :: l)) ->
                    forall (l : list A), P l :=
  fun H0 H1 H2 => 
    fix aux (l : list A) : P l := 
      match l with 
        | []  => H0
        | [x] => H1 x
        | a :: b :: l' => H2 a b l' (aux l')
      end.

Lemma aux1 : forall l p f, pathToPosAux (l ++ [Right]) f = Some p ->
               exists f', forall l', pathToPosAux (l ++ l') f =
                                    pathToPosAux l' f' /\ f' xH = p.
induction l using list_ind'; intros.
+ simpl in *; inversion H; subst.
  exists f; intros.
  split; auto.
+ simpl in H; destruct a; inversion H.
+ pose proof IHl p; clear IHl.
  destruct a; destruct b; simpl in *.
  -  pose proof (H0 (fun p0 => xO (f p0))); clear H0.
     apply H1 in H; clear H1.
     assumption.
  -  pose proof (H0 (fun p0 => xI (f p0))); clear H0.
     apply H1 in H; clear H1.
     assumption.
  - inversion H.
  - inversion H.
Qed.

Lemma posPathInj : forall p, pathToPos (posToPath p) = Some p.
induction p; unfold posToPath, pathToPos in *; simpl in *.
- apply aux1 in IHp. 
  inversion IHp as [f' Hyp]; clear IHp.
  rewrite <- app_assoc; simpl.
  pose proof Hyp [Left; Right; Right] as H; clear Hyp.
  inversion H as [H0 H1]; clear H.
  rewrite H0; clear H0.
  simpl; subst; auto.
- apply aux1 in IHp. 
  inversion IHp as [f' Hyp]; clear IHp.
  rewrite <- app_assoc; simpl.
  pose proof Hyp [Left; Left; Right] as H; clear Hyp.
  inversion H as [H0 H1]; clear H.
  rewrite H0; clear H0.
  simpl; subst; auto.
- auto.
Qed.

Fixpoint lengthSplit {A : Type} (l l' : list A) : option (list A * list A) :=
  match l, l' with
    | [], x => Some ([], x)
    | _::xs, y::ys => 
      option_map (fun (p : list A * list A) => 
                    let (l1,l2) := p in (y::l1, l2)) (lengthSplit xs ys)
    | _, _ => None
  end.

Lemma lengthSplit1 : forall {A : Type} (l l' : list A), 
                       le (length l) (length l') -> 
                       exists p, lengthSplit l l' = Some p.
induction l as [ | x xs IHxs].
+ intros; exists ([], l'); auto.
+ intros l' LE; destruct l' as [ | b bs] eqn:LEq.
  - inversion LE.
  - pose proof IHxs bs as IH; clear IHxs.
    assert (LE' : le (length xs) (length bs))
           by (simpl in *; omega). (* Overkill? :) *)
    clear LE.
    apply IH in LE'; clear IH.
    inversion LE' as [pair Split]; clear LE'.
    destruct pair as [l1 l2] eqn:Pair.
    simpl.
    rewrite Split.
    exists (b :: l1, l2).
    simpl.
    auto.
Qed.

Lemma lengthSplit2 : forall {A : Type} (l l' l1 l2 : list A), 
                       lengthSplit l l' = Some (l1, l2) -> l1 ++ l2 = l'.
induction l.
+ intros l' l1 l2 Hyp; simpl in Hyp; inversion_clear Hyp; auto.
+ intros l' l1 l2 Hyp. 
  simpl in Hyp.
  destruct l' as [ | y ys] eqn:L'.
  - inversion Hyp.
  - destruct l1 eqn:L1.
    * destruct (lengthSplit l ys); simpl in *.
      + destruct p; congruence.
      + congruence.
    * pose proof IHl ys l0 l2; clear IHl.
      destruct (lengthSplit l ys) eqn:LenSplit; simpl in *.
      + inversion Hyp. destruct p. inversion H1. subst.
        rewrite H; auto.
      + inversion Hyp.
Qed.      

Lemma lengthSplit3 : forall {A : Type} (l l' l1 l2 : list A), 
                       lengthSplit l l' = Some (l1, l2) -> length l1 = length l.
induction l as [ | x xs IHxs].
+ intros; simpl in H; inversion H; auto.
+ intros l' l1 l2 Split.
  simpl in Split.
  destruct l'.
  - inversion Split.
  - destruct l1.
    * destruct (lengthSplit xs l').
      + simpl in *. destruct p. inversion Split.
      + simpl in *. inversion Split.
    * simpl in *. 
      destruct (lengthSplit xs l') eqn:LenSplit.
      + simpl in *. destruct p. inversion Split; subst; clear Split.
        pose proof (IHxs l' l1 l2 LenSplit) as Hyp; clear IHxs.
        auto.
      + simpl in *. inversion Split.
Qed.        

Lemma lengthPathEven : forall p, exists n, length (posToPathAux p) = (2 * n)%nat.
induction p.
+ inversion IHp as [n Hyp]; clear IHp.
  simpl.
  exists (S n).
  rewrite app_length. 
  rewrite Hyp.
  simpl.
  omega.
+ inversion IHp as [n Hyp]; clear IHp.
  simpl.
  exists (S n).
  rewrite app_length. 
  rewrite Hyp.
  simpl.
  omega.
+ exists (O).
  simpl.
  auto.
Qed.

Lemma evenPathAux : forall l l' l'' f n p, length l = (2 * n)%nat -> 
                      pathToPosAux (l ++ l'') f = Some p ->
                      exists f', pathToPosAux (l ++ l') f = pathToPosAux l' f'.
induction l using list_ind'.
+ intros. exists f. auto.
+ intros. simpl in *. omega.
+ intros l' l'' f n p Len Valid.
  destruct n.
  - simpl in Len. congruence.
  - simpl in Len; assert (length l = (2 * n)%nat) by omega.
    destruct a eqn:A; destruct b eqn:B; simpl in *.
    * unfold pathToPos in Valid. simpl in Valid.
      pose proof (IHl l' l'' (fun p => xO (f p)) n p H Valid) as Hyp; clear IHl H.
      inversion Hyp as [f' HF]; clear Hyp.
      exists f'.
      auto.
    * unfold pathToPos in Valid. simpl in Valid.
      pose proof (IHl l' l'' (fun p => xI (f p)) n p H Valid) as Hyp; clear IHl H.
      inversion Hyp as [f' HF]; clear Hyp.
      exists f'.
      auto.
    * inversion Valid.
    * inversion Valid.
Qed.

Lemma posToPathBeginsLeft : forall p, p <> xH ->
                              head (posToPathAux p) = Some Left.
intros.
induction p.
+ destruct (Pos.eq_dec p 1).
  - subst.
    unfold posToPath.
    auto.
  - unfold posToPath in *.
  - apply IHp in n.                                  
    simpl.
    destruct (posToPathAux p).
    * simpl in n. inversion n.
    * simpl in n. inversion n. subst. auto.
+ destruct (Pos.eq_dec p 1).
  - subst.
    unfold posToPath.
    auto.
  - unfold posToPath in *.
  - apply IHp in n.                                  
    simpl.
    destruct (posToPathAux p).
    * simpl in n. inversion n.
    * simpl in n. inversion n. subst. auto.
+ unfold not in H. 
  exfalso. apply H. auto.
Qed.

Lemma listAppNeq : forall (A : Type) (l1 l2 l3 l4 : list A), 
                     (forall (x y : A), {x = y} + {x <> y}) ->
                     length l1 = length l2 -> 
                     l1 <> l2 ->
                     l1 ++ l3 <> l2 ++ l4.
induction l1.
+ intros.
  destruct l2.
  - unfold not in H0. exfalso; apply H0; auto.
  - simpl in H; inversion H.
+ intros l2 l3 l4 EqDec Len Neq.
  destruct l2 as [ | b l2 ].
  - simpl in Len. congruence.
  - destruct (EqDec a b).
    * subst. simpl in Len. 
      inversion Len as [ Len']; clear Len.
      simpl.
      pose proof (IHl1 l2 l3 l4 EqDec Len') as Contra; clear IHl1.
      assert (l1 <> l2) by (unfold not; intros; congruence).
      apply Contra in H.
      unfold not in *.
      intros.
      apply H.
      inversion H0.
      auto.
    * unfold not; intros.
      inversion H.
      congruence.
Qed.

Lemma PosToPathPrefixFree : forall (x y : positive), ~ (x = y) -> 
                              PrefixFree [posToPath x;
                                          posToPath y].
intros.
apply FreeCons; [ apply FreeCons ; [ constructor | intros p Contra; inversion Contra] | ].
intros.
inversion H0; subst; clear H0; [ | inversion H2].
unfold posToPath in *; simpl in *; repeat rewrite <- app_assoc in *.


destruct (Compare_dec.le_ge_dec (length (posToPathAux y)) 
                                (length (posToPathAux x))).
+ pose proof (lengthSplit1 (posToPathAux y) (posToPathAux x) l) as Hyp.
  inversion Hyp as [pair Split]; clear Hyp.
  destruct pair.
  pose proof (lengthSplit2 (posToPathAux y) (posToPathAux x) l0 l1 Split) as AppHyp.
  pose proof (lengthSplit3 (posToPathAux y) (posToPathAux x) l0 l1 Split) as LenHyp.
  pose proof (lengthPathEven y) as Hyp; inversion Hyp as [n LenN]; subst; clear Hyp.
  assert (Even : exists f', pathToPosAux (l0 ++ l1) (fun x => x) = pathToPosAux l1 f') 
    by (eapply evenPathAux; [ rewrite LenHyp; eassumption 
                            | instantiate (2 := (l1 ++ [Right])); 
                              instantiate (1 := x);
                              rewrite app_assoc;
                              rewrite AppHyp;
                              apply posPathInj ] ).
  inversion Even as [f' HF]; clear Even.
  rewrite <- AppHyp in H1.
  rewrite <- app_assoc in H1.
  destruct (list_eq_dec Direction_eq_dec (posToPathAux y) l0).
  - subst. apply app_inv_head in H1.
    admit.
  - eapply listAppNeq.
    * apply Direction_eq_dec.
    * instantiate (1 := l0). instantiate (1 := posToPathAux y). eauto.
    * eassumption.
    * eapply H1.
+ admit.
Qed.

Function rangeNat (p : nat) : list nat :=
  match p with 
    | O => []
    | S n' => p :: (rangeNat n')
  end.

Definition rangePos (p : positive) : list positive := 
  map Pos.of_nat (rangeNat (Pos.to_nat p)).

Lemma ltInRange : forall m n, le n m -> n <> O -> In n (rangeNat m).
  induction m; intros.
  + inversion H. simpl. auto.
  + simpl. inversion H.
    - left; auto.
    - right; subst. apply IHm; auto.
Qed.

Lemma posLtInRange : forall max pos, Pos.le pos max -> In pos (rangePos max).
  intros.
  apply in_map_iff.
  exists (Pos.to_nat pos).
  split.
  - apply Pos2Nat.id.
  - apply ltInRange.
    + apply Pos2Nat.inj_le; auto.
    + pose proof (Pos2Nat.is_succ pos) as Contra; inversion_clear Contra; congruence.
Qed.

Lemma rangeNatLt : forall n m, In m (rangeNat n) -> lt m (S n).
  induction n; intros.
  + simpl in H. inversion H. 
  + inversion H.
    - subst. unfold lt. apply le_n.
    - apply IHn in H0.
      unfold lt in *.
      apply le_S.
      auto.
Qed.    

Lemma rangePosPrefixFree : forall p, PrefixFree (map posToPath (rangePos p)).
  intros.
  unfold rangePos.
  induction (Pos.to_nat p).
  + constructor.
  + simpl. apply FreeCons; auto.
    intros.
    apply in_map_iff in H.
    clear IHn.
    inversion H; clear H.
    inversion H1; clear H1.
    subst.
    apply in_map_iff in H2.
    inversion H2; clear H2.
    inversion H; clear H.
    apply rangeNatLt in H2.
    remember (match n with | O => 1 | S _ => Pos.succ (Pos.of_nat n) end) as m.
    assert (x <> m). admit.
    pose proof PosToPathPrefixFree x m.
    apply H3 in H.
    inversion H.
    eapply H7.
    + left; auto.
    + eauto.
Qed.    

Definition posFunToPathFun (f : positive -> RandomSeed) (p : SplitPath) 
: RandomSeed :=
  match pathToPos p with 
    | Some a => f a
    | None   => newRandomSeed
  end.

Theorem coarbComplete' : forall (max : positive) (f : positive -> RandomSeed) ,
                          exists seed, forall p, p <= max -> 
                            varySeed (posToPath p) seed = f p.
intros.
pose proof (topLevelSeedTheorem (map posToPath (rangePos max)) 
                                (posFunToPathFun f) (rangePosPrefixFree max)).
inversion H; clear H.
exists x.
intros.
pose proof H0 (posToPath p).
rewrite H1.
+ unfold posFunToPathFun.
  rewrite posPathInj.
  reflexivity.
+ apply in_map_iff.
  exists p.
  split; auto.
  apply posLtInRange.
  auto.
Qed.

Definition funToPosFun {A : Type} `{_ : CoArbitrary A} (f : A -> RandomSeed) (p : positive)
: RandomSeed :=
  match coarbReverse p with 
    | Some a => f a
    | None   => newRandomSeed
  end.

Definition coarbLe {A : Type} `{_ : CoArbitrary A} (x y : A) : Prop :=
  Pos.le (coarbitrary x) (coarbitrary y).

Lemma coarbLePreservesLe : forall {A : Type} `{_ : CoArbitrary A} (x y : A),
  coarbLe x y -> Pos.le (coarbitrary x) (coarbitrary y).
by [].
Qed.

Theorem coarbComplete : forall {A : Type} `{_ : CoArbitrary A} (max : A)
                               (f : A -> RandomSeed),
                          exists seed, forall a, coarbLe a max ->
                                          varySeed (posToPath (coarbitrary a)) seed = f a.
intros.
pose proof (coarbComplete' (coarbitrary max) (funToPosFun f)) as Hyp.
inversion Hyp as [seed HSeed]; clear Hyp.
exists seed.
intros a HLe.
pose proof (HSeed (coarbitrary a)) as HCo; clear HSeed.
apply coarbLePreservesLe in HLe.
apply HCo in HLe; clear HCo.
rewrite HLe; clear HLe.
unfold funToPosFun.
rewrite coarbCorrect.
reflexivity.
Qed.

Instance arbFun {A B : Type} `{_ : CoArbitrary A} `{_ : Arbitrary B} : Arbitrary (A -> B) :=
  {|
    arbitrary := 
      reallyUnsafePromote (fun a => variant (posToPath (coarbitrary a)) arbitrary);
    shrink x := []
  |}.
                            
  

