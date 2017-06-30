From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From QuickChick Require Import QuickChick Tactics.


Import QcNotation. 

Instance frequencySizeMonotonic_alt 
: forall {A : Type} (g0 : G A) (lg : seq (nat * G A)),
    SizeMonotonic g0 ->
    lg \subset [set x | SizeMonotonic x.2 ] ->
    SizeMonotonic (frequency g0 lg).
Admitted.

Lemma semFreq :
  forall (A : Type) (ng : nat * G A) (l : seq (nat * G A)),
    semGen (freq ((fst ng, snd ng) ;; l)) <-->
    \bigcup_(x in (ng :: l)) semGen x.2.
Admitted.

Lemma semFreqSize :
  forall {A : Type} (ng : nat * G A) (l : seq (nat * G A)) (size : nat),
    semGenSize (freq ((fst ng, snd ng) ;; l)) size <-->
    \bigcup_(x in (ng :: l)) semGenSize x.2 size.
Admitted.

Lemma oneOf_freq {A} (g : G A) (gs : list (G A)) size :
  semGenSize (oneOf (g ;; gs)) size <-->
  semGenSize (freq ((1, g) ;; map (fun x => (1, x)) gs)) size.  
Admitted.

Definition all (A : Type) (f : A -> Prop) : Prop := forall (x : A), f x.

Lemma nat_set_ind (A : Type) `{Hyp : CanonicalSized A} :
  forall (P : nat -> set A -> Prop),
    (P 0 zeroSized) ->
    (forall (n : nat) s, P n s -> P (n.+1) (succSized s)) ->
    (forall (n : nat), P n [ set x | size x <= n ]).
Proof.
Admitted.

Instance bindOptMonotonic
        {A B} (g : G (option A)) (f : A -> G (option B))
        `{SizeMonotonic _ g} `{forall x, SizeMonotonic (f x)} : 
  SizeMonotonic (bindGenOpt g f).
Admitted.

Instance suchThatMaybeMonotonic
         {A : Type} (g : G A) (f : A -> bool) `{SizeMonotonic _ g} : 
  SizeMonotonic (suchThatMaybe g f).
Admitted.

Instance suchThatMaybeOptMonotonic
         {A : Type} (g : G (option A)) (f : A -> bool) `{SizeMonotonic _ g} : 
  SizeMonotonic (suchThatMaybeOpt g f).
Admitted.

Lemma bigcap_setU_l:
  forall (U T : Type) (s1 s2 : set U) (f : U -> set T),
    \bigcap_(i in s1) f i :&: \bigcap_(i in s2) f i <--> \bigcap_(i in s1 :|: s2) f i.
Proof.
  intros. split.
  - intros [ H1 H2 ] x [ H3 | H3 ]; eauto.
  - intros H. split; intros x H3; eapply H.
    now left. now right.
Qed.

Lemma setI_set_incl :
  forall (A : Type) (s1 s2 s3 : set A),
    s1 \subset s2 ->
    s1 \subset s3 ->
    s1 \subset s2 :&: s3.
Proof.
  firstorder.
Qed.

Lemma imset_isSome {A} (s : set A) :
  Some @: s \subset isSome.
Proof.
  intros y [x [Sx H]]. inv H. eauto.
Qed.

Lemma bigcup_cons_subset_r :
  forall (A B : Type) (l : A) (ls : seq A) (f : A -> set B) (s1 s2 : set B),
    s1 \subset f l ->
    s2 \subset \bigcup_(x in ls) f x ->
    s1 :|: s2 \subset \bigcup_(x in (l :: ls)) f x.
Proof.
  intros A B l ls f s1 s2 H1 H2.
  apply setU_l_subset.
  - rewrite bigcup_setU_l bigcup_set1.
    eapply setU_subset_l. eassumption.
  - rewrite bigcup_setU_l bigcup_set1.
    eapply setU_subset_r. eassumption.
Qed.

Lemma bigcup_setI_cons_subset_r :
  forall (A B : Type) (l : A) (ls : seq A) (f : A -> set B) (s1 s2 : set B) (s3 : set A),
    s3 l ->
    s1 \subset f l ->
    s2 \subset \bigcup_(x in ls :&: s3) f x ->
    s1 :|: s2 \subset \bigcup_(x in (l :: ls) :&: s3) f x.
Proof.
  intros A B l ls f s1 s2 s3 H1 H2 H3.
  apply setU_l_subset.
  - intros x Hs1. eexists l; split; eauto.
    split; eauto. left; eauto.
  - intros x Hs1. eapply H3 in Hs1.
    edestruct Hs1 as [x' [[Hs3 Hls] Hin]].
    eexists x'; split; eauto. split; eauto.
    right; eauto.
Qed.

Lemma imset_union_set_eq:
  forall (U T : Type) (s1 s2 : set U) (f : U -> T),
    f @: (s1 :|: s2) <--> f @: s1 :|: f @: s2.
Proof.
  intros U T s1 s2 f.
  firstorder.
Qed.

Lemma imset_bigcup_setI_cons_subset_r :
  forall (A B : Type) (l : A) (ls : seq A) (f : A -> set (option B))
    (s1 s2 : set B) (s3 : set A),
    s3 l ->
    Some @: s1 \subset f l ->
    Some @: s2 \subset \bigcup_(x in ls :&: s3) f x ->
    Some @: (s1 :|: s2) \subset \bigcup_(x in (l :: ls) :&: s3) f x.
Proof.
  intros A B l ls f s1 s2 s3 H1 H2 H3.
  rewrite imset_union_set_eq. apply setU_l_subset.
  - intros x Hs1. eexists l; split; eauto.
    split; eauto. left; eauto.
  - intros x Hs1. eapply H3 in Hs1.
    edestruct Hs1 as [x' [[Hs3 Hls] Hin]].
    eexists x'; split; eauto. split; eauto.
    right; eauto.
Qed.

Lemma imset_set0_subset {A B} (f : A -> B) (s : set B) :
  (f @: set0) \subset s.
Proof.
  firstorder.
Qed.

(* Typeclasses eauto := debug.*)

Lemma eq_symm {A : Type} (x y : A) :
  x = y -> y = x.
Proof.
  firstorder.
Qed.

Lemma plus_leq_compat_l n m k :
  n <= m ->
  n <= m + k.
Proof. 
  intros. ssromega.
Qed.

Lemma plus_leq_compat_r n m k :
  n <= k ->
  n <= m + k.
Proof. 
  intros. ssromega.
Qed.

Lemma leq_refl: forall n, n <= n.
Proof.
  intros. ssromega.
Qed.

(* Yikes this is stupid, find a workaround *)
Definition prop := Prop.
