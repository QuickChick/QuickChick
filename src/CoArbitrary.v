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

Fixpoint posToPath (p : positive) : SplitPath := 
  match p with 
    | xH => [Right]
    | xI p' => posToPath p' ++ [Left; Right]
    | xO p' => posToPath p' ++ [Left; Left ]
  end.

Instance coArbPos : CoArbitrary positive := 
  {|
    coarbitrary := posToPath
  |}.
Proof.
intros.  
eapply FreeCons.
+ constructor. 
+ unfold In. left. eauto.
+ instantiate (1 := []). simpl.
  generalize dependent y.
  induction x.
  - intros.
    destruct y.
    rewrite app_nil_r in H0.
    simpl in H0.
    apply app_inv_tail in H0.
    

    * compute in H0; simpl in *.

Require Import Recdef.
Require Import Numbers.Natural.Peano.NPeano.
Require Import ZArith.
Function natToPath (n : nat) {measure (fun n => n) n} : SplitPath := 
  match n with 
    | O => [Right]
    | _ => (natToPath (n / 2))
           ++ (Left :: (if beq_nat (modulo n 2) 0 then Right else Left) :: [])
  end.
Proof.
intros; subst; apply Nat.div_lt; [apply lt_0_Sn | ]; auto.
Defined. 

Instance coArbNat : CoArbitrary nat :=
  {|
    coarbitrary := natToPath
  |}.
Proof.
intros.  
eapply FreeCons.
+ constructor. 
+ unfold In. left. eauto.
+ instantiate (1 := []). admit.
Qed.

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


