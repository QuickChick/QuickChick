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

Lemma succ_neq_zero :
  forall x, S x <> 0.
Proof.
  firstorder.
Qed.

Lemma isSomeSome {A : Type} (y : A) :
  Some y.
Proof.
  exact isT.
Qed.

Lemma semBacktrack:
  forall (A : Type) (l : seq (nat * G (option A))),
    semGen (backtrack l) <-->
    (\bigcup_(x in (l :&: (fun x => x.1 <> 0))) (isSome :&: (semGen x.2))) :|:
    ([set None] :&: (\bigcap_(x in l :&: (fun x => x.1 <> 0)) (semGen x.2))).
Admitted.


Lemma semSuchThatMaybe_complete:
  forall (A : Type) (g : G A) (f : A -> bool) (s : set A),
    s \subset semGen g ->
    (Some @: (s :&: (fun x : A => f x))) \subset
    semGen (suchThatMaybe g f).
Proof.
Admitted.

Lemma semSuchThatMaybeOpt_complete:
  forall (A : Type) (g : G (option A)) (f : A -> bool) (s : set A),
    (Some @: s) \subset semGen g ->
    (Some @: (s :&: (fun x : A => f x))) \subset
    semGen (suchThatMaybeOpt g f).
Proof.
Admitted.

Lemma semSuchThatMaybe_sound:
  forall (A : Type) (g : G A) (f : A -> bool) (s : set A),
    semGen g \subset s ->
    semGen (suchThatMaybe g f) \subset ((Some @: (s :&: (fun x : A => f x))) :|: [set None]).
Proof.
Admitted.

Lemma semSuchThatMaybeOpt_sound:
  forall (A : Type) (g : G (option A)) (f : A -> bool) (s : set A),
    semGen g \subset ((Some @: s) :|: [set None]) ->
    semGen (suchThatMaybeOpt g f) \subset (Some @: (s :&: (fun x : A => f x)) :|: [set None]).
Proof.
Admitted.

Lemma isSome_subset {A : Type} (s1 s2 s1' s2' : set (option A)) :
  isSome :&: s1 \subset isSome :&: s2 ->
  isSome :&: (s1 :|: ([set None] :&: s1')) \subset isSome :&: (s2 :|: ([set None] :&: s2')).
Proof.
  intros Hyp x [H1 H2]. destruct x as [ x | ]; try discriminate.
  split; eauto.
  inv H2. left; eauto.
  eapply Hyp. now split; eauto.
  inv H. now inv H0.
Qed.

Lemma setI_set_eq_r {A : Type} (s1 s2 s2' : set A) :
  s2 <--> s2' ->
  (s1 :&: s2) <--> (s1 :&: s2').
Proof.
  intros. rewrite H; reflexivity.
Qed.

Lemma semBindSize_subset_compat {A B : Type} (g g' : G A) (f f' : A -> G B) s :
  semGenSize g s \subset semGenSize g' s ->
  (forall x, semGenSize (f x) s \subset semGenSize (f' x) s) ->
  semGenSize (bindGen g f) s \subset semGenSize (bindGen g' f') s.
Proof.
  intros H1 H2. rewrite !semBindSize.
  eapply subset_trans.
  eapply incl_bigcupl. eassumption.
  eapply incl_bigcupr. eassumption.
Qed.

Lemma semBindSizeOpt_subset_compat {A B : Type} (g g' : G A) (f f' : A -> G (option B)) s :
  semGenSize g s \subset semGenSize g' s ->
  (forall x, isSome :&: semGenSize (f x) s \subset isSome :&: semGenSize (f' x) s) ->
  isSome :&: semGenSize (bindGen g f) s \subset isSome :&: semGenSize (bindGen g' f') s.
Proof.
  intros H1 H2. rewrite !semBindSize.
  eapply subset_trans.
  eapply setI_subset_compat. eapply subset_refl.
  eapply incl_bigcupl. eassumption.
  rewrite !setI_bigcup_assoc. 
  eapply incl_bigcupr. eassumption.
Qed.

Lemma semBindOptSizeOpt_subset_compat {A B : Type} (g g' : G (option A)) (f f' : A -> G (option B)) s :
  isSome :&: semGenSize g s \subset isSome :&: semGenSize g' s ->
  (forall x, isSome :&: semGenSize (f x) s \subset isSome :&: semGenSize (f' x) s) ->
  isSome :&: semGenSize (bindGenOpt g f) s \subset isSome :&: semGenSize (bindGenOpt g' f') s.
Proof.
Admitted.

Lemma suchThatMaybeOpt_subset_compat {A : Type} (p : A -> bool) (g1 g2 : G (option A)) s :
  isSome :&: (semGenSize g1 s) \subset isSome :&: (semGenSize g2 s) ->
  isSome :&: (semGenSize (suchThatMaybeOpt g1 p) s) \subset
  isSome :&: (semGenSize (suchThatMaybeOpt g2 p) s).
Proof.
Admitted.

Lemma suchThatMaybe_subset_compat {A : Type} (p : A -> bool) (g1 g2 : G A) s :
  (semGenSize g1 s) \subset (semGenSize g2 s) ->
  isSome :&: (semGenSize (suchThatMaybe g1 p) s) \subset
  isSome :&: (semGenSize (suchThatMaybe g2 p) s).
Proof.
Admitted.

Lemma bigcup_cons_setI_subset_compat {A B} (f : A -> set B)
      (x x' : A) (l l' : seq A) s :
  f x \subset f x' ->
  \bigcup_(x in (l :&: s)) (f x) \subset
   \bigcup_(x in (l' :&: s)) (f x) ->
  \bigcup_(x in ((x :: l) :&: s)) (f x) \subset
   \bigcup_(x in ((x' :: l') :&: s)) (f x).
Proof.
Admitted.

(* more specific lemmas to help type checking of the proof term *)
Lemma bigcup_cons_setI_subset_compat_backtrack {A}
      (n n' : nat) (g g' : G (option A)) (l l' : seq (nat * G (option A))) s :
  isSome :&: semGenSize g s  \subset isSome :&: semGenSize g' s ->
  \bigcup_(x in (l :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s) \subset
  \bigcup_(x in (l' :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s) ->
  \bigcup_(x in (((n, g) :: l) :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s) \subset
  \bigcup_(x in (((n', g') :: l') :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s).
Proof.
Admitted.

Lemma bigcup_cons_setI_subset_pres_backtrack {A}
      (n : nat) (g : G (option A)) (l l' : seq (nat * G (option A))) s :
  \bigcup_(x in (l :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s) \subset
  \bigcup_(x in (l' :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s) ->
  \bigcup_(x in (l :&: (fun x => x.1 <> 0))) (isSome :&: semGenSize x.2 s) \subset
  \bigcup_(x in ((n, g) :: l') :&: (fun x => x.1 <> 0)) (isSome :&: semGenSize x.2 s).
Proof.
Admitted.

Lemma bigcup_nil_setI {A B} (f : A -> set B)
      (l : seq A) s :
  \bigcup_(x in nil :&: s) (f x) \subset
  \bigcup_(x in (l :&: s)) (f x).
Proof.
Admitted.
