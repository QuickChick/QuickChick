Require Import String micromega.Lia List.

Require Import Tactics TacticsUtil Instances Classes DependentClasses Sets
        Producer Generators EnumProofs Checker Decidability CheckerProofs.

Import ListNotations.

Set Warnings "-notation-overwritten, -parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Local Open Scope set_scope.

From Ltac2 Require Import Ltac2.


Set Bullet Behavior "Strict Subproofs".


Section Lemmas. 

  
  Lemma exists_oneOf_hd A (x : A) g' (g : nat -> G A) (l : nat -> seq (G A)) :
    (exists s : nat, semProd (g s) x) ->
    exists s : nat, semProd (oneOf_ g' ((g s) :: (l s))) x.
  Proof.
    intros Hin. inv Hin.
    eexists. eapply semOneof. now eauto with typeclass_instances.
    eexists. split; eauto. now left. 
  Qed.

  Lemma exists_oneOf_tl A (x : A) g' (g : nat -> G A) (l : nat -> seq (G A)) :
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

  Lemma exists_freq_hd A (x : A) g' (g : nat -> G A) (l : nat -> seq (nat * G A)) n :
    (exists s : nat, semProd (g s) x) ->
    exists s : nat, semProd (freq_ g' ((S n, g s) :: (l s))) x.
  Proof.
    intros Hin. inv Hin.
    eexists. eapply (@semFrequency A). simpl.
    eexists. split; eauto. now left. eassumption.
  Qed.

  Lemma exists_freq_tl A (x : A) g' (g : nat -> G A) (l : nat -> seq (nat * G A)) n :
    (exists s : nat, match l s with
                     | (S n, g1) :: gs => semProd (freq_ g' ((S n, g1) :: gs)) x
                     | _ => False                                                  
                     end) ->
    exists s : nat, semProd (freq_ g' ((S n, g s) :: (l s))) x.
  Proof.
    intros Hin. inv Hin.
    eexists. eapply (@semFrequency A). simpl.
    destruct (l x0)  eqn:Heq.
    - exfalso; eauto.
    - destruct p. destruct n0; try (now (exfalso; eauto)).
      eapply (@semFrequency A) in H.
      rewrite Heq. simpl in H. inv H. destruct H0. eexists. split > [ | eassumption ].
      now right; eauto.
  Qed.

  Lemma exists_bind A B (x : A) (g : G B) (f : nat -> B -> G A) :
    Correct B g ->
    SizeMonotonic g ->
    (forall a s, SizeMonotonic (f a s)) ->

    (exists z s, semProd (f s z) x) ->  
    exists s : nat, semProd (bindGen g (f s)) x.
  Proof.
    intros Hc Hs1 Hs2 He. inv He. inv H. inv H0.
    inv H.
    assert (Hin : [set : B] x0) by reflexivity.
    eapply Hc in Hin. inv Hin. inv H.
    exists x1, (Nat.max x2 x3). split. reflexivity.
    eapply (@semBindSize G ProducerGen _ B A).
    eexists. split.

    eapply Hs1 > [ | eassumption ]. now ssromega.
    eapply Hs2 > [ | eassumption ]. now ssromega.
  Qed.

  Lemma exists_return A (x : A) :
    exists s : nat, semProd (returnGen x) x.
  Proof.
    exists 0. eapply (@semReturn G _ ProducerSemanticsGen); reflexivity.
  Qed.

  Lemma exists_bind_Sized_alt A B
        (g : nat -> G B) (f : B -> nat -> G A)
        (x : A) (z : B) (s' : nat) :
    SizedMonotonic g ->
    (forall s, SizeMonotonic (g s)) ->

    (forall a, SizedMonotonic (f a)) ->
    (forall a s, SizeMonotonic (f a s)) ->

    semProd (g s') z ->
    (exists s, semProd (f z s) x) ->  
    exists s : nat, semProd (bindGen (g s) (fun x => f x s)) x.
  Proof.
    intros Hs Hs' Hsf Hsf' Hprod Hex. inv Hex. inv Hprod.
    inv H. destruct H0.
    exists (Nat.max s' x0). inv H1.
    exists (Nat.max x1 x2).
    
    split. reflexivity.
    
    eapply (@semBindSize G ProducerGen _ B A).

    eexists. split.
    eapply Hs > [ | eapply Hs' > [ | eassumption ] ]. ssromega. ssromega.

    eapply Hsf > [ | eapply Hsf' > [ | eassumption ] ]. ssromega. ssromega.
  Qed.

  Lemma semProd_mon {A} (g : nat -> G A) {_ : SizedMonotonic g} :
    forall s1 s2,
      (s1 <= s2)%coq_nat -> 
      semProd (g s1) \subset semProd (g s2).
  Proof.
    intros s1 s2 Hleq.
    intros x Hin. inv Hin. inv H0.
    eexists x0. split; eauto.
    eapply H > [ | eassumption ].
    destruct (leqP s1 s2); eauto.
  Qed.

  
  Lemma exists_gen_hd A (g : nat -> G (option A)) (gs : nat -> list (nat * G (option A))) x n : 
    (exists s, semProdOpt (g s) x) ->
    exists s, semProdOpt (backtrack ((S n, g s) :: gs s)) x.
  Proof.
    intros [s He].
    exists s.
    eapply (@backtrack_correct_opt A).
    eexists. split. split. now left. simpl. lia. eassumption.
  Qed.

  Lemma exists_gen_tl A (g : nat -> G (option A)) (gs : nat -> list (nat * G (option A))) x n : 
    (exists s, semProdOpt (backtrack (gs s)) x) ->
    exists s, semProdOpt (backtrack ((n, g s) :: gs s)) x.
  Proof.
    intros [s He].
    exists s.
    eapply (@backtrack_correct_opt A).
    eapply (@backtrack_correct_opt A) in He. destruct He as [z [Hin Hsem]].
    inv Hin. eexists. split. split. now right; eauto. eassumption. eassumption.
  Qed.


  Lemma exists_bind_Opt A B (x : A) (g : G B) (f : B -> nat -> G (option A)) z :
    Correct B g ->
    SizeMonotonic g ->
    (forall a s, SizeMonotonicOpt (f a s)) ->

    (exists s, semProdOpt (f z s) x) ->  
    exists s : nat, semProdOpt (bindGen g (fun x => f x s)) x.
  Proof.
    intros Hc Hs1 Hs2 He. inv He. inv H. inv H0.
    inv H.
    assert (Hin : [set : B] z) by reflexivity.
    eapply Hc in Hin. inv Hin. inv H.
    exists x0, (Nat.max x1 x2). split. reflexivity.
    eapply (@semBindSize G ProducerGen _ B).
    eexists. split.

    eapply Hs1 > [ | eassumption ]. now ssromega.
    eapply Hs2 > [ | eassumption ]. now ssromega.
  Qed.

  Lemma exists_return_Opt A (x : A) :
    exists s : nat, semProdOpt (returnGen (Some x)) x.
  Proof.
    exists 0. eapply (@semReturn G _ ProducerSemanticsGen); reflexivity.
  Qed.

  Lemma exists_bindOpt_Opt A B (x : A) (g : G (option B)) (f : B -> nat -> G (option A)) z :
    SizeMonotonicOpt g ->
    (forall a s, SizeMonotonicOpt (f a s)) ->

    semProdOpt g z ->
    (exists s, semProdOpt (f z s) x) ->  
    exists s : nat, semProdOpt (bindOpt g (fun x => f x s)) x.
  Proof.
    intros Hc Hs1 Hs2 He. destruct He as [s1 He].
    exists s1.
    eapply (@semOptBindOpt G _ _ B); eauto with typeclass_instances.

    eexists. split; eassumption.
  Qed.

  Lemma exists_bindOpt_Opt_Sized A B (x : A) (g : nat -> G (option B)) (f : B -> nat -> G (option A)) z :
    SizedMonotonicOpt g ->
    (forall s, SizeMonotonicOpt (g s)) ->

    (forall a, SizedMonotonicOpt (f a)) ->
    (forall a s, SizeMonotonicOpt (f a s)) ->

    (exists s, semProdOpt (g s) z) ->
    (exists s, semProdOpt (f z s) x) ->  
    exists s : nat, semProdOpt (bindOpt (g s) (fun z => f z s)) x.
  Proof.
    intros Hs1 Hs1' Hs2 Hs2' Hg Hf. destruct Hg as [s1 He].
    destruct Hf.
    exists (max x0 s1).
    eapply (@semOptBindOpt G _ _ B); eauto with typeclass_instances.
    inv He. inv H. inv H0. inv H1. 
    eexists. split. 
    eexists. split. reflexivity.
    eapply Hs1 > [ | eassumption ]. ssromega.
    eexists. split. reflexivity.
    eapply Hs2 > [ | eassumption ]. ssromega.  
  Qed.

  

  Lemma exists_match_DecOpt {B} P {_ : DecOpt P} (k : nat -> G (option B)) z :
    DecOptSizeMonotonic P ->
    DecOptCompletePos P -> 
    SizedMonotonicOpt k ->
    P ->
    (exists s, semProdOpt (k s) z) ->
    exists (s : nat),
      semProdOpt (match decOpt s.+1 with
                  | Some true => k s
                  | _ => returnGen None
                  end) z.
  Proof.
    intros Hmon Hcom Hmonk Hp [s1 [s [_ He]]].
    eapply Hcom in Hp. destruct Hp as [s2 Hdec].
    eexists (max s1 s2).
    eapply Hmon in Hdec. rewrite Hdec.

    eexists. split. reflexivity. eapply Hmonk > [ | eassumption ].
    ssromega. ssromega.
  Qed.

  Lemma semProdSizeOpt_semProdOpt {A} {G : Type -> Type} {_ : Producer G} (e1 e2 : G (option A)) :
    (forall s, semProdSizeOpt e1 s \subset semProdSizeOpt e2 s) ->
    semProdOpt e1 \subset semProdOpt e2.
  Proof.
    intros H x Hin. inv Hin. inv H0. eexists. split; eauto. eapply H. eassumption.
  Qed. 

  Lemma incl_bigcup_compat_list_pair (T K U : Type) (h1 h2 : T) (t1 : list T)
        (t2 : list (K * T)) (F : T -> set U) (G : K * T -> set U) k :
    F h1 \subset G (k, h2) ->
    \bigcup_(x in t1) F x \subset \bigcup_(x in t2) G x ->
    \bigcup_(x in h1 :: t1) F x \subset \bigcup_(x in (k, h2) :: t2) G x.
  Proof.
    intros Hs1 Hs2.
    intros x Hin. inv Hin. inv H. inv H0.
    - eexists. split. now left. eauto.
    - edestruct Hs2.
      eexists. split; eauto.
      destruct H0. eexists. split. now right; eauto.
      eassumption.
  Qed.

End Lemmas.

(** Examples *)

(** ** Enum **)

Ltac2 simpl_minus_arbitrarySized (_ : unit) :=
  ltac1:(with_strategy opaque [arbitrarySized] simplstar).

Ltac2 simpl_arbitrarySized (_ : unit) :=
  unfold arbitrarySized; simpl_minus_arbitrarySized (). 

(*** Sized Monotonicity *)

Ltac2 rec gen_sized_mon (ih : ident) :=
  first
    [ (* ret *)
      guarded_subset_refl ()
    | (* bind *)
    eapply (@semBindSize_subset_compat _ _ ProducerSemanticsGen) >
    [ let x := Fresh.in_goal (id_of_string "x") in
      intros $x;
    first
      [ now eapply subset_refl (* for calls to enum *)
      | let ih' := Control.hyp ih in (* for recursive calls *)
        eapply $ih'; now ssromega ]
    | let x := Fresh.in_goal (id_of_string "x") in
      let s := Fresh.in_goal (id_of_string "s") in
      intros $x $s; gen_sized_mon ih
    ]
    ].

Ltac2 rec find_gen (_ : unit) :=
  first
    [ now eapply incl_bigcup_list_nil
    | eapply incl_bigcup_compat_list_pair > [ now eapply subset_refl  | find_gen () ]
    | eapply incl_bigcup_list_hd; now eapply subset_refl
    | eapply incl_bigcup_list_tl; find_gen ()
    ].


Ltac2 base_case_size_mon (_ : unit) :=
  destruct s2 > 
  [ guarded_subset_refl () | simpl_arbitrarySized (); first [ guarded_subset_refl ()
                                                            | rewrite !&Hone, !&Hfreq; now find_gen () ] ]. 

Ltac2 rec gens_sized_mon (ih : ident) :=
  first
    [ now eapply incl_bigcup_list_nil
    | eapply incl_bigcup_compat_list > [ now gen_sized_mon @IHs1 | gens_sized_mon ih ] ].

Ltac2 ind_case_sized_mon (_ : unit) :=
  destruct s2 > 
  [ now ssromega | simpl_arbitrarySized (); first [ now gen_sized_mon @IHs1
                                                  | rewrite !&Hfreq; now gens_sized_mon @IHs1 ] ]. 


Ltac2 derive_gen_SizedMonotonic (_ : unit) :=
    assert (Hone := @semOneofSize G _ ProducerSemanticsGen);
    
    match! goal with
    | [ |- @SizedMonotonic ?t _ _ (@arbitrarySized _ ?inst) ] =>
      assert (Hfreq := (@semFrequencySize $t));
      (intros s s1; revert s; induction s1 as [| s1 IHs1 ];
      intros s s2 Hleq) > [ now base_case_size_mon () | now ind_case_sized_mon () ]
    end. 


(* Size Mon *)

Ltac2 rec gen_size_mon (ih : ident) :=
  first
    [ (* ret *)
      eapply returnGenSizeMonotonic; tci
    | (* bind *)
      eapply bindMonotonic >
      [ tci
      | first
          [ now find_size_mon_inst ()  (* for calls to enum *)
          | let ih' := Control.hyp ih in (* for recursive calls *)
            eapply $ih'; now ssromega ]
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; gen_size_mon ih
      ]
    ].

Ltac2 rec gens_size_mon (t : constr) (ih : ident) :=
  first
    [ now eapply (@list_subset_nil (G $t))
    | eapply (@list_subset_cons (G $t)) > 
      [ now gen_size_mon ih
      | gens_size_mon t ih ] ]. 

Ltac2 rec gens_size_mon_pair (t : constr) (ih : ident) :=
  first
    [ now eapply (@list_subset_nil (nat * G $t))
    | eapply (@list_subset_cons (nat * G $t)) >
      [ now gen_size_mon ih
      | gens_size_mon_pair t ih ] ].

Ltac2 derive_gen_SizeMonotonic (_ : unit) :=
  intros s;
    match! goal with
    | [ |- @SizeMonotonic ?t _ _ _ ] =>
      induction s as [ | s IHs ];
        simpl_arbitrarySized ();
        first [ eapply oneofMonotonic >  
                [ tci
                | now gen_size_mon @IHs
                | now gens_size_mon t @IHs ]
              | now gen_size_mon @IHs
              | eapply (@frequencySizeMonotonic_alt $t) >  
                [ now gen_size_mon @IHs
                | now gens_size_mon_pair t @IHs ] ]
    end.


(* Correct *)

Ltac2 find_corr_inst (_ : unit) :=
  first [ tci
        | match! goal with
          | [ |- Correct ?ty (sizedGen arbitrarySized) ] =>
            eapply (@GenCorrectOfSized $ty _) >
            [ tci
            | now find_size_mon_inst ()
            | tci ]
          end ].

Ltac2 solve_sized_mon (hs : ident) :=
  intros ? ? ? ? ?; now gen_sized_mon hs.      

Ltac2 solve_size_mon (hs : ident) :=
  intros ? ?; now gen_size_mon hs.      


Ltac2 rec gen_size_correct (_ : unit) :=
  first
    [ (* return *)
      now eapply exists_return; eauto
                                  
    | (* bind non rec *)
      match! goal with
      |  [ |- exists _ : nat, semProd (bindGen (* enum *) _ _) _ ] => 
         eapply exists_bind > [ now find_corr_inst ()
                              | now find_size_mon_inst ()
                              | now solve_size_mon @Hsize
                              | now eexists; gen_size_correct () ]
      end
    | (* bind rec *)
      match! goal with
      | [|- exists z, semProd (bindGen (&_aux_gen z) _) _  ] =>
        eapply exists_bind_Sized_alt >
        [ tci
        | now find_size_mon_inst ()
        | now solve_sized_mon @Hsized
        | now solve_size_mon @Hsize
        |
        | now gen_size_correct () ]; eassumption
      end
    ]. 


Ltac2 rec try_solve_correct (_ : unit) :=
  first
    [ eapply exists_freq_hd; now gen_size_correct ()
    | eapply exists_freq_tl; try_solve_correct ()
    ].

Ltac2 derive_gen_Correct (_ : unit) := 
  match! goal with
  | [ |- @CorrectSized ?typ _ _ ?en ] =>  
    simpl_enumSized ();
    match! goal with
    | [ |- @CorrectSized _ _ _ [eta ?gen_simpl] ] =>
      (* get the enum body *)
      set (_aux_gen := ltac2:(exact $gen_simpl));
      let hsize := Fresh.in_goal (id_of_string "Hsize") in
      let hsized := Fresh.in_goal (id_of_string "Hsized") in
      let ind := Fresh.in_goal (id_of_string "t") in
      (* Derive monotonicity instances *)
      assert ($hsized : SizedMonotonic $en) > [ tci | ];
      assert ($hsize : forall s, SizeMonotonic ($en s)) > [ tci | ];
      econstructor; intro $ind; split > [ intro; exact I | intros _ ];
      let ind' := Control.hyp ind in
      induction $ind'; eapply exists_Sn; repeat (destructIH ()); simpl_arbitrarySized ();
      first [ gen_size_correct () | try_solve_correct () ]
    end
  end.


(* GenST *)


Ltac2 simpl_minus_arbitrarySizeST (_ : unit) :=
  ltac1:(with_strategy opaque [arbitrarySizeST arbitrary decOpt] simplstar).

Ltac2 simpl_arbitrarySizeST (_ : unit) :=
  unfold arbitrarySizeST; simpl_minus_arbitrarySizeST (). 

(*** Sized monotonic *) 

Lemma incl_bigcup_compat_list_P (T U : Type) (h1 h2 : T) (t1 t2 : list T) (F G : T -> set U) (P : T -> Prop) :
    F h1 \subset G h2 ->
    P h1 -> P h2 ->
    \bigcup_(x in t1 :&: P) F x \subset \bigcup_(x in t2 :&: P) G x ->
    \bigcup_(x in (h1 :: t1) :&: P) F x \subset \bigcup_(x in (h2 :: t2) :&: P) G x.
Proof.
  intros Hs1 Hp1 Hp2 Hs2.
  intros x Hin. inv Hin. inv H. inv H0. inv H.
  - eexists. split. constructor. now left. eauto. eauto.
  - edestruct Hs2.
    eexists. split; eauto.
    split. eassumption. eassumption. inv H. inv H3. 
    eexists. split. constructor. now right; eauto.
    eassumption. eassumption.
Qed.

Lemma incl_bigcup_list_nil_P (T U : Type) (G : T -> set U) s (P : T -> Prop) :
    \bigcup_(x in [::] :&: P) G x \subset s.
Proof. 
  intros x Hin. inv Hin. inv H. inv H0. inv H.
Qed.

Lemma incl_bigcup_list_tl_P (T U : Type) (h : T) (t : list T) (G : T -> set U) s (P : T -> Prop) :
    s \subset \bigcup_(x in t :&: P) G x ->
    s \subset \bigcup_(x in (h :: t) :&: P) G x.
Proof.
  intros Hyp x Hin. eapply Hyp in Hin.
  inv Hin. inv H. inv H0.
  eexists. split. split. now right; eauto. eauto. eauto.
Qed.

Lemma in_bigcup_list_tl_P (T U : Type) (h : T) (t : seq T) (G : T -> set U) (z : U) (P : T -> Prop) :
  (\bigcup_(x in t :&: P) G x) z -> (\bigcup_(x in (h :: t) :&: P) G x) z.
Proof.
  intros Hin. destruct Hin. inv H. inv H0.
  eexists. split. split. right. eassumption. eassumption. eassumption. 
Qed.

Lemma in_bigcup_list_cons_P (T U : Type) (h : T) (t : seq T) (G : T -> set U) (z : U)  (P : T -> Prop) :
  (\bigcup_(x in ((h :: t) :&: P)) G x) z ->
  G h z /\ P h \/ (\bigcup_(x in t :&: P) G x) z.
Proof.
  intros Hin. inv Hin. inv H. inv H0; eauto. inv H; eauto.
  right. eexists; split; eauto. split; eauto.
Qed.

Lemma bigcup_nil_set0_P (T U : Type) (F : T -> set U) (P : T -> Prop) : 
  \bigcup_(x in [::] :&: P) F x <--> set0.
Proof.
  split; intros Hin; inv Hin; eauto.
  inv H. inv H0. inv H.
Qed.


Ltac2 rec genST_sized_mon (ih : ident) :=
  first
    [ (* ret *)
      guarded_subset_refl ()
    | (* dec matching *)
      match! goal with
      | [ |- semProdSizeOpt (match @decOpt ?p ?i ?s1 with _ => _ end) _ \subset
             semProdSizeOpt (match decOpt ?s2 with _ => _ end) _ ] =>
        let hdec := Fresh.in_goal (id_of_string "Hdec") in 
        destruct (@decOpt $p $i $s1) eqn:$hdec >
        [ ((erewrite (@CheckerProofs.mon $p $i _ $s1 $s2) > [ | | first [ eassumption | ssromega ] ]) > [ genST_sized_mon ih | ssromega ])
        | rewrite (@semReturnSizeOpt_None G _ ProducerSemanticsGen); now eapply sub0set ]
      end
     | (* input matching *) 
      match! goal with
      | [ |- semProdSizeOpt (match ?p with _ => _ end) _ \subset _ ] =>
        destruct $p; genST_sized_mon ih
      end
    | (* bindOpt *)
      eapply (@semBindOptSizeOpt_subset_compat G _ ProducerSemanticsGen) >
      [ first
          [ now eapply subset_refl (* for calls to gen *)
          | let ih' := Control.hyp ih in (* for recursive calls *)
            eapply $ih'; now ssromega ]
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; genST_sized_mon ih
      ]
    | (* bind *)
      eapply (@semBindSizeOpt_subset_compat G _ ProducerSemanticsGen) >
      [ now eapply subset_refl 
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; genST_sized_mon ih
      ]
    | ()
    ].

Ltac2 rec find_genST (ih : ident) :=
  first
    [ now eapply incl_bigcup_list_nil_P
    | eapply incl_bigcup_compat_list_P >
      [ simpl_minus_arbitrarySizeST (); now genST_sized_mon ih | simpl; ssromega | simpl; ssromega  | find_genST ih ]
    | eapply incl_bigcup_list_tl_P; find_genST ih
    ].

Ltac2 base_case_st_size_mon (s2 : constr) :=
  destruct $s2 > 
  [ first [ guarded_subset_refl () | rewrite !backtrack_correct_size_opt; simpl_minus_arbitrarySizeST (); find_genST @dummy ]
  | rewrite !backtrack_correct_size_opt; find_genST @dummy ]. 

Ltac2 ind_case_st_sized_mon (s2 : constr) (ih : ident) :=
  destruct $s2 > 
  [ now ssromega |  rewrite !backtrack_correct_size_opt; simpl_minus_arbitrarySizeST (); find_genST ih ]. 

Ltac2 derive_genST_SizedMonotonic (_ : unit) :=
  match! goal with
  | [ |- SizedMonotonicOpt (@arbitrarySizeST ?typ ?pred ?inst) ] =>
      
    let s := Fresh.in_goal (id_of_string "s") in
    let s1 := Fresh.in_goal (id_of_string "s1") in
    let s2 := Fresh.in_goal (id_of_string "s2") in
    let s1i := Fresh.in_goal (id_of_string "s1i") in
    let s2i := Fresh.in_goal (id_of_string "s2i") in
    let hleq := Fresh.in_goal (id_of_string "Hleq") in
    let hleqi := Fresh.in_goal (id_of_string "Hleqi") in
    let ihs1 := Fresh.in_goal (id_of_string "ihs1") in
    intros $s $s1 $s2 $hleq; simpl_arbitrarySizeST ();
      let hleq' := Control.hyp hleq in
      let s1' := Control.hyp s1 in
      let s2' := Control.hyp s2 in
      assert ($hleqi := $hleq');
      revert $hleqi $hleq;
      generalize $s2' at 1 3; generalize $s1' at 1 3; revert $s $s2; EnumProofs.revert_params pred;
        (induction $s1' as [| $s1 $ihs1 ]; EnumProofs.intro_params pred; intros $s $s2 $s1i $s2i $hleqi $hleq) >
        [ base_case_st_size_mon s2' | ind_case_st_sized_mon s2' ihs1 ]
  end.



(* Size Monotonicity *)


Ltac2 rec genST_size_mon (ih : ident) :=
  first
    [ (* ret *)
      eapply returnGenSizeMonotonicOpt; tci
    | (* bindOpt *)
      eapply bindOptMonotonicOpt >
      [ tci
      | first
          [ (* for calls to gen in params *)
            tci
          | (* for call to existing gen instances. XXX not sure why typeclass resulotion doesn't work *)
            eapply sizedSizeMonotonicOpt; tci 
          | (* for recursive calls *)
             let ih' := Control.hyp ih in 
            eapply $ih' ]
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; genST_size_mon ih
      ]
    | (* bind *)
      eapply bindMonotonicOpt >
      [ tci
      | first
          [ (* for calls to gen in params *)
            tci 
          | (* for call to existing gen instances. XXX not sure why typeclass resulotion doesn't work *)
            eapply sizedSizeMonotonic; tci 
          | (* for recursive calls *)
             let ih' := Control.hyp ih in 
            eapply $ih' ]
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; genST_size_mon ih
      ]
    | (* input/dec matching *)
      match! goal with
      | [ |- SizeMonotonicOpt (match ?p with _ => _ end) ] =>
        destruct $p; genST_size_mon ih
      end
    | ()
    ].

Ltac2 rec gensST_size_mon (t : constr) (ih : ident) :=
  first
    [ now eapply (@list_subset_nil (nat * G (option $t)))
    | eapply (@list_subset_cons (nat * G (option $t))) > 
      [ simpl_minus_arbitrarySizeST (); genST_size_mon @ih
      | gensST_size_mon t ih ] ]. 


Ltac2 derive_genST_SizeMonotonic (_ : unit) :=
  let s := Fresh.in_goal (id_of_string "s") in
  let ihs := Fresh.in_goal (id_of_string "Ihs") in
  let si := Fresh.in_goal (id_of_string "si") in
  intro $s;
  let s' := Control.hyp s in 

  match! goal with
  | [ |- SizeMonotonicOpt (@arbitrarySizeST ?typ ?pred ?inst _) ] =>   
    simpl_arbitrarySizeST (); generalize $s' at 1; EnumProofs.revert_params pred;
    induction $s' as [ | $s $ihs ]; EnumProofs.intro_params pred; intros $si;
    eapply backtrack_SizeMonotonicOpt; gensST_size_mon typ @IHs
  end.


(* Correctness *)

Definition empty_gen {A} : G (option A) := MkGen (fun _ _ => None).

Ltac2 make_semGen (t : constr) (enum : constr) (s : constr) :=
  let c := constr:(@semProdSizeOpt G _ ltac2:(exact $t) empty_gen ltac2:(exact $s)) in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App sem sargs => 
    let sargs' := Array.copy sargs in
    let _ := Array.set sargs' 3 enum in
    Constr.Unsafe.make (Constr.Unsafe.App sem sargs')
  | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
  end.


Ltac2 mon_expr (tapp : constr) (inst : constr) :=
  match! goal with
  | [ |- CorrectSizedST _ ?f ] =>
    match Constr.Unsafe.kind f with
    | Constr.Unsafe.Lambda b app =>
      match Constr.Unsafe.kind app with
      | Constr.Unsafe.App aux args =>

        let len := Int.sub (Array.length args) 2 in
        let inps := Array.sub args 2 len in

        let args' (s1 : constr) (s2 : constr) (offs : int) :=
            let ind := Array.mapi (fun i _ => Constr.Unsafe.make (Constr.Unsafe.Rel (Int.add i offs))) inps in
            let a := Array.make 2 s1 in
            Array.set a 1 s2; Array.append a ind
        in

        let aux_app s1 s2 offs := Constr.Unsafe.make (Constr.Unsafe.App aux (args' s1 s2 offs)) in


        (* SizeMonotonic *) 
        let dummy_app s1 s2 :=
            let args' := Array.copy args in
            let _ := Array.set args' 0 s1 in
            let _ := Array.set args' 1 s1 in
            Constr.Unsafe.make (Constr.Unsafe.App aux args')
        in

        let dummy_term := constr:(SizeMonotonicOpt (ltac2:(let t := dummy_app '0 '0 in exact $t))) in

        let make_term s1 s2 :=
            match Constr.Unsafe.kind dummy_term with
            | Constr.Unsafe.App mon margs =>
              let margs' := Array.copy margs in
              Array.set margs' 3 (aux_app s1 s2 1);
              make_prod inps (Constr.Unsafe.make (Constr.Unsafe.App mon margs'))
            | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
            end
        in 
        
        assert (_Hmon : forall (_s1 _s2 : nat), ltac2:(let s1 := Control.hyp @_s1 in
                                                      let s2 := Control.hyp @_s2 in
                                                      let t := make_term s1 s2  in exact $t)) >
        [  let s := Fresh.in_goal (id_of_string "s") in 
           let si := Fresh.in_goal (id_of_string "si") in 
           let ihs := Fresh.in_goal (id_of_string "IHs") in 
           intros $si $s;
           let s' := Control.hyp s in revert $si;
           induction $s' as [ | $s $ihs ]; intros $si;
           Array.iter (fun _ => intro) inps; eapply backtrack_SizeMonotonicOpt; now gensST_size_mon tapp ihs
        | ];

        (* SizedMonotonic, generalized *)          
        let subset (t1 : constr) (t2 : constr) :=
            let dummy := constr:(set_incl (@set0 (ltac2:(exact $tapp))) set0) in
            match Constr.Unsafe.kind dummy with
            | Constr.Unsafe.App sub sargs =>
              let sargs' := Array.copy sargs in
              let _ := Array.set sargs' 1 t1 in
              let _ := Array.set sargs' 2 t2 in
              Constr.Unsafe.make (Constr.Unsafe.App sub sargs')
            | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
            end
        in
        let mon s1 s2 s1' s2' s :=
            make_prod inps (subset (make_semGen tapp (aux_app s1' s1 1) s) (make_semGen tapp (aux_app s2' s2 1) s))
        in
        
        (* print_constr (mon '1 '2 '3 '4); set (s := ltac2:(let t := mon '1 '2 '3 '4 in exact $t)); () *)
                                                                                      
        assert (_Hmons : forall (s1 s2 s2' s1' s: nat), (s1 <= s2)%coq_nat -> (s1' <= s2')%coq_nat -> 
                                                       ltac2:(let s1 := Control.hyp @s1 in
                                                              let s1' := Control.hyp @s1' in
                                                              let s2 := Control.hyp @s2 in
                                                              let s2' := Control.hyp @s2' in 
                                                              let s' := Control.hyp @s in 
                                                              let t := mon s1 s2 s1' s2' s' in exact $t)) >
        [ let s1 := Fresh.in_goal (id_of_string "s1") in
          let s2 := Fresh.in_goal (id_of_string "s2_") in
          let ihs1 := Fresh.in_goal (id_of_string "ihs1") in
          intros $s1; simpl_arbitrarySizeST ();
          let s1' := Control.hyp s1 in
          (induction $s1' as [| $s1 $ihs1 ]; intros $s2 ? ? ? ? ? ; Array.iter (fun _ => intro) inps) >
          [ let s2' := Control.hyp s2 in base_case_st_size_mon s2' | let s2' := Control.hyp s2 in ind_case_st_sized_mon s2' ihs1 ]
        | ]
    | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
    end
  | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting a function"))))
  end
end.



Ltac2 rec genST_sound (ty : constr) (ih : ident) :=    
  match! goal with
  (* match decOpt *) 
  | [ h : semProdOpt (match @decOpt ?p ?i ?s with _ => _ end) ?x |- _ ] =>
    let hdec := Fresh.in_goal (id_of_string "Hdec") in 
    let b := Fresh.in_goal (id_of_string "b") in 
    destruct (@decOpt $p $i $s) as [ $b | ] eqn:$hdec > [ | now eapply (@semReturnOpt_None G _ _) in $h; inv $h ];
    let b' := Control.hyp b in                                                            
    destruct $b' > [ | now eapply (@semReturnOpt_None G _ _) in $h; inv $h ];
    eapply (@CheckerProofs.sound $p) in $hdec > [ | tci ]; genST_sound ty ih

 (* match input *) 
  | [ h : semProdOpt (match ?n with _ => _ end) ?x |- _ ] =>
    destruct $n; try (now eapply (@semReturnOpt_None G _ _) in $h; inv $h); genST_sound ty ih
  | (* return *)
    [ h : semProdOpt (returnGen _) _ |- _ ] =>
    eapply (@semReturnOpt G _ _) in $h; inv $h;  now eauto 20 using $ty
  | (* bindOpt *)
    [ h : semProdOpt (bindOpt _ _) _ |- _ ] =>
    eapply (@semOptBindOpt G _ _) in $h >
                                     [ let h' := Control.hyp h in
                                       (* let x := Fresh.in_goal (id_of_string "_x") in *)
                                       (* let hin1 := Fresh.in_goal (id_of_string "_Hin1") in *)
                                       (* let hin2 := Fresh.in_goal (id_of_string "_Hin2") in *)
                                       (* XXX there seems to be a bug in fresh, and it fails to freshen after a while.
                                         P     icking ? for now *) 
                                       destruct $h' as [? [$h ?]];
                                        
                                       first [ let ih' := Control.hyp ih in eapply $ih' in $h
                                             | match! goal with
                                               | [h : semProdOpt (sizedGen (@arbitrarySizeST ?t ?pred ?inst)) _ |- _ ] =>
                                                 eapply (@SuchThatCorrectOfBounded $t $pred $inst) in $h > [ | tci | tci | tci ]
                                               end ];
                                       genST_sound ty ih
                                     | find_size_mon_inst ()
                                     | intro; now genST_size_mon @Hmon ]


  | (* bind *)
    [ h : semProdOpt (bindGen _ _) _ |- _ ] =>
    eapply (@semOptBind G _ _) in $h >
                                  [ let h' := Control.hyp h in
                                    destruct $h' as [? [? ?]]; genST_sound ty ih
                                  | find_size_mon_inst ()
                                  | intro; now genST_size_mon @Hmon ]

  | [ |- _ ] => ()
  end.

Ltac2 rec sound_gens (ty : constr) (ih : ident) :=
  match! goal with
  | [ h : (\bigcup_(x in ((seq_In (_ :: _)) :&: _)) _) _ |- _ ] =>
    eapply in_bigcup_list_cons_P in $h; simpl_minus_arbitrarySizeST ();
    let h' := Control.hyp h in
    destruct $h' as [ [? ?] | ] > [ genST_sound ty ih | sound_gens ty ih  ]
  | [ h : (\bigcup_(x in seq_In Datatypes.nil :&: _) _) _ |- _ ] =>
    apply bigcup_nil_set0_P in $h; inv $h
  end. 

Ltac2 derive_sound_genST (ty : constr) (pred : constr) :=
  let s := Fresh.in_goal (id_of_string "s") in
  let si := Fresh.in_goal (id_of_string "si") in
  let ihs := Fresh.in_goal (id_of_string "ihs") in
  let hgen := Fresh.in_goal (id_of_string "Hgen") in
  intros [$s $hgen]; revert $hgen;

  let s' := Control.hyp s in

  match! goal with
    [ |- semProdOpt _ ?x -> _ ] => 
    (generalize $s' at 1; EnumProofs.revert_params pred; revert x; induction $s' as [ | $s $ihs]; intro;
     EnumProofs.intro_params pred;
     intros $si $hgen;
     eapply &Hback in $hgen) > [ sound_gens ty ihs | sound_gens ty ihs  ]
  end.

Ltac2 rec genST_complete (ty : constr):=
  let hmons := Control.hyp @_Hmons in
  first
    [ (* return *)
      subst; now eapply exists_return_Opt
    | (* match decOpt for eq *)
      (eapply (@exists_match_DecOpt $ty) > [ | | | ltac1:(now eapply Logic.eq_refl) | genST_complete ty ]) >
      [ (* decOpt mon *) tci
      | (* decOpt complete *) tci
      | (* sizedMon *) intros ? ? ? ?; genST_sized_mon @_Hmons
      | genST_complete ty ]
    | (* match decOpt *)
      (eapply (@exists_match_DecOpt $ty) > [ | | | | genST_complete ty ]) >
      [ (* decOpt mon *) tci
      | (* decOpt complete *) tci
      | (* sizedMon *) intros ? ? ? ?; genST_sized_mon @_Hmons
      | (* P *) now eauto ]
    | (* bindOpt rec call *)
      (eapply exists_bindOpt_Opt_Sized > [ | | | | | now genST_complete ty ]) >
      [ (* sizedMon *)
        intro; intros; eapply $hmons; ssromega
      | (* sizeMon *) now find_size_mon_inst ()
      | (* sizedMon *) intros ? ? ? ? ?; now genST_sized_mon @_Hmons
      | (* sizeMon *) intros ? ?; genST_size_mon @_Hmon
      | eexists; eexists; split > [ reflexivity
                                  | eapply $hmons > [ eapply Peano.le_n | | eassumption ]; ssromega ]
      ]
    | (* bindOpt sized eq *)
      eapply exists_bindOpt_Opt_Sized >
      [ tci
      | intros _; now find_size_mon_inst ()
      | (* sizedMon *) intros ? ? ? ? ?; now genST_sized_mon @_Hmons
      | (* sizeMon *) intros ? ?; genST_size_mon @_Hmon
      | match! goal with
      | [ |- exists _, semProdOpt (sizedGen (@arbitrarySizeST ?t ?pred ?inst)) _ ] =>
        exists 0; eapply (@size_CorrectST $t $pred G _ _) > [ | | | ltac1:(now eapply Logic.eq_refl) ]; tci
        end
      | now genST_complete ty
      ]
    | (* bindOpt sized *)
      (eapply exists_bindOpt_Opt_Sized > [ | | | | | now genST_complete ty ]) >
      [ tci
      | intros _; now find_size_mon_inst ()
      | (* sizedMon *) intros ? ? ? ? ?; now genST_sized_mon @_Hmons
      | (* sizeMon *) intros ? ?; genST_size_mon @_Hmon
      | match! goal with
      | [ |- exists _, semProdOpt (sizedGen (@arbitrarySizeST ?t ?pred ?inst)) _ ] =>
        exists 0; eapply (@size_CorrectST $t $pred G _ _) > [ | | | eassumption ]; tci
        end
      ]
    | (* bind *)
      match! goal with
      |  [ |- exists _ : nat, semProdOpt (bindGen arbitrary _) _ ] =>
         eapply exists_bind_Opt >
         [ tci
         | now find_size_mon_inst ()
         | intros ? ?; genST_size_mon @_Hmon | now genST_complete ty ]
      end

    | ( ) ].

Ltac2 rec try_solve_complete (ty : constr) :=
  first [ eapply exists_gen_hd; now genST_complete ty 
        | eapply exists_gen_tl; try_solve_complete ty ].


Ltac2 derive_complete_genST (ty : constr) (inst : constr) := 
  let ind := Fresh.in_goal (id_of_string "ind") in 
  intros $ind; let ind' := Control.hyp ind in induction $ind';
  eapply exists_Sn; repeat (destructIH_opt ()); try_solve_complete ty. 


Ltac2 derive_genST_Correct (_ : unit) := 
  match! goal with
  | [ |- CorrectSizedST _ (@arbitrarySizeST ?tapp ?pred ?inst) ] =>
    assert (Hback := @backtrack_correct_opt $tapp);
      
    simpl_arbitrarySizeST ();

    (* derive monotonicity *) 
    mon_expr tapp inst;

    let ty := get_ty pred in
    let x := Fresh.in_goal (id_of_string "x") in
    split; intros $x; split >
      [ derive_sound_genST ty pred | derive_complete_genST tapp inst  ]
  end.



(* Ltac tactics *)
Ltac derive_gen_SizeMonotonic := ltac2:(derive_gen_SizeMonotonic ()).
Ltac derive_gen_SizedMonotonic :=  ltac2:(derive_gen_SizedMonotonic ()).
Ltac derive_gen_Correct := ltac2:(derive_gen_Correct ()).


Ltac derive_genST_SizeMonotonic := ltac2:(derive_genST_SizeMonotonic ()).
Ltac derive_genST_SizedMonotonic :=  ltac2:(derive_genST_SizedMonotonic ()).
Ltac derive_genST_Correct := ltac2:(derive_genST_Correct ()).
