Require Import Arbitrary Random GenLow.
Import GenLow.

Require Import PArith.
Require Import List.
Import ListNotations.

(* LL: TODO: Add proof obligation that the result paths be prefix free? *)
Class CoArbitrary (A : Type) : Type :=
  {
    coarbitrary : A -> SplitPath;
    coarbitraryCorrect : forall (x y : A), ~ (x = y) -> PrefixFree [coarbitrary x;
                                                                    coarbitrary y]
  }.

Local Open Scope positive.
Fixpoint posToPathAux (p : positive) : SplitPath := 
  match p with 
    | xH => []
    | xI p' => posToPathAux p' ++ [Left; Right]
    | xO p' => posToPathAux p' ++ [Left; Left ]
  end.

Definition posToPath (p : positive) : SplitPath := posToPathAux p ++ [Right].

Instance coArbPos : CoArbitrary positive := 
  {|
    coarbitrary := posToPath
  |}.
Proof.
Admitted.

Function rangeNat (p : nat) : list nat :=
  match p with 
    | O => [] 
    | S n' => p :: (rangeNat n')
  end.

Definition rangePos (p : positive) : list positive := 
  map Pos.of_nat (rangeNat (Pos.to_nat p)).

Lemma rangeNatLt : forall n m, In m (rangeNat n) -> lt m (S n).
  induction n; intros.
  + inversion H.
  + inversion H.
    - subst. unfold lt. apply le_n.
    - apply IHn in H0.
      unfold lt in *.
      apply le_S.
      auto.
Qed.    

Lemma rangePosPrefixFree : forall p, PrefixFree (map coarbitrary (rangePos p)).
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
    pose proof coarbitraryCorrect x m.
    apply H3 in H.
    inversion H.
    eapply H7.
    + left; auto.
    + eauto.
Qed.    

Theorem coArbComplete : forall (max : positive) (f : positive -> RandomSeed) ,
                          exists seed, forall p, p <= max -> 
                            varySeed (coarbitrary p) seed = f p.
intros.
pose proof (topLevelSeedTheorem (map coarbitrary (rangePos max)) (fun p => f (rangePosPrefixFree _)).

topLevelSeedTheorem
     : forall (l : list SplitPath) (f : SplitPath -> RandomSeed),
       PrefixFree l ->
       exists s : RandomSeed,
         forall p : SplitPath, In p l -> varySeed p s = f p

                          
                          p <= max -> exists seed, fora

Instance arbFun {A B : Type} `{_ : CoArbitrary A} `{_ : Arbitrary B} : Arbitrary (A -> B) :=
  {|
    arbitrary := 
      reallyUnsafePromote (fun a => variant (coarbitrary a) arbitrary);
    shrink x := []
  |}.

(*
Definition varyComplete : forall (max : nat) (f : nat -> RandomSeed),
                          exists (seed : RandomSeed), 
                            forall (n : nat),
                              n <= max -> varySeed n seed = f n.


induction max; intros.
+ pose proof (randomSplitAssumption (f O) (f O)) as Seed; inversion Seed as [seed Hyp].
  exists seed; intros p H.
  inversion_clear H.
  unfold varySeed, varySeed_terminate, boolVary; simpl.
  rewrite Hyp.
  reflexivity.
+ pose proof (IHmax f) as Seed.
  inversion Seed as [seed Hyp]; clear Seed.
*)
(*  
exists randomSeedInhabitant; intros.
  inversion H. 
  - admit.
  - 

pose proof IHmax f as IH.
    inversion IH as [seed' Hyp'].
    
unfold varySeed, varySeed_terminate, boolVary. simpl.
  

  inversion 
admit.
+ admit.
+ pose proof (randomSplitAssumption (f xH) (f xH)) as Seed; inversion Seed as [seed Hyp].
  exists seed; intros p H.
  apply Pos.le_lteq in H.
  inversion H as [Contra | ].
  - apply Pos.nlt_1_r in Contra; inversion Contra.
  - subst. unfold varySeed. unfold boolVary. rewrite Hyp. reflexivity.
Qed.

Axiom randomSplitAssumption :
  forall s1 s2 : RandomSeed, exists s, randomSplit s = (s1,s2).
*)


