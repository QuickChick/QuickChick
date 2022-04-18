Require Import String.
Require Import List.

Require Import RoseTrees.
Require Import Show.
Require Import State.
Require Import Producer Generators Enumerators.
Require Import Classes.
Require Import DependentClasses.
Require Import Checker.
Require Import Decidability.
Require Import TacticsUtil.

From Ltac2 Require Import Ltac2.


Section TypeClasses.
    
  Class DecOptSizeMonotonic (P : Prop) {H : DecOpt P} :=
    mon : forall s1 s2 b, s1 <= s2 -> decOpt s1 = Some b -> decOpt s2 = Some b.
  
  Class DecOptDecidable (P : Prop) {H : DecOpt P} :=
    { wit : exists s a, decOpt s = Some a }.

  Class DecOptSoundPos (P : Prop) {H : DecOpt P} :=
    sound : forall s, decOpt s = Some true -> P.

  Class DecOptCompletePos (P : Prop) {H : DecOpt P} :=
    complete : P -> exists s, decOpt s = Some true.

  Class DecOptSoundNeg (P : Prop) {H : DecOpt P} :=
    sound_neg : forall s, decOpt s = Some false -> ~ P.

  Class DecOptCompleteNeg (P : Prop) {H : DecOpt P} :=
    complete_neg : ~ P -> exists s, decOpt s = Some false.
  
  Class DecOptCorrectPos (P : Prop) {H : DecOpt P} :=
    { corr_sound : forall s, decOpt s = Some true -> P; 
      corr_complete : P -> exists s, decOpt s = Some true }.

  Class DecOptCorrectNeg (P : Prop) {H : DecOpt P} :=
    { corr_sound' : forall s, decOpt s = Some false -> ~ P; 
      corr_complete' :~ P -> exists s, decOpt s = Some false }.

    
  Global Instance decSizeMonotonic (P : Prop) {_ : Dec P} : DecOptSizeMonotonic P.
  Proof. intro; intros; eapply H1. Qed.

  Global Instance decSoundPos (P : Prop) {_ : Dec P} : DecOptSoundPos P.
  Proof.
    intros s.
    unfold decOpt, dec_decOpt, Decidability.dec. destruct H.
    destruct dec; eauto. congruence.
  Qed.

  Global Instance decCompletePos (P : Prop) {_ : Dec P} : DecOptCompletePos P.
  Proof.
    intros s.
    unfold decOpt, dec_decOpt, Decidability.dec. destruct H.
    exists 0. 
    destruct dec; eauto. congruence.
  Qed.

  
  Global Instance decCorrectPos (P : Prop) {_ : Dec P} : DecOptCorrectPos P.
  Proof.
    constructor. 
    - intros s.
      unfold decOpt, dec_decOpt, Decidability.dec. destruct H.
      destruct dec; eauto. congruence.
    - intros s.
      unfold decOpt, dec_decOpt, Decidability.dec. destruct H.
      exists 0. 
      destruct dec; eauto. congruence.
  Qed.


  Global Instance decCompleteNeg (P : Prop) {_ : Dec P} : DecOptCompleteNeg P.
  Proof.
    intros s.
    unfold decOpt, dec_decOpt, Decidability.dec. destruct H.
    exists 0. 
    destruct dec; eauto. congruence.
  Qed.

  
  Global Instance decCorrectNeg (P : Prop) {_ : Dec P} : DecOptCorrectNeg P.
  Proof.
    constructor. 
    - intros s.
      unfold decOpt, dec_decOpt, Decidability.dec. destruct H.
      destruct dec; eauto. congruence.
    - intros s.
      unfold decOpt, dec_decOpt, Decidability.dec. destruct H.
      exists 0. 
      destruct dec; eauto. congruence.
  Qed.

  Global Instance decSoundNeg (P : Prop) {_ : Dec P} : DecOptSoundNeg P.
  Proof.
    intros s.
    unfold decOpt, dec_decOpt, dec. destruct H.
    destruct dec; eauto. congruence.
  Qed.

  Global Instance decOptSoundNeg (P : Prop) {H : DecOpt P}
         {Hm : DecOptSizeMonotonic P} 
         {Hc : DecOptCompletePos P} : DecOptSoundNeg P.
  Proof.
    intros s Hopt HP. eapply Hc in HP.
    destruct HP.
    edestruct (Compare_dec.le_lt_dec s x).
    + eapply Hm in Hopt; eauto. congruence.
    + eapply Hm in H0 > [ | eapply PeanoNat.Nat.lt_le_incl; eassumption ].
      congruence.
  Qed. 

  Lemma reflect_decOpt (P : Prop) {Hd : Dec P}
        {Hm : DecOptSizeMonotonic P}
        {Hc : DecOptCompletePos P}
        {Hs : DecOptCorrectPos P} s b :
    decOpt s = Some b ->
    Bool.reflect P b.
  Proof.
    intros Heq.
    destruct b.
    - constructor. eapply Hs. eassumption.
    - constructor. intros HP.
      eapply decOptSoundNeg in Heq; now eauto.
  Qed.
    
End TypeClasses.


Section Lemmas. 


  Lemma checker_backtrack_spec l :
    checker_backtrack l = Some true <->
    exists f, List.In f l /\ f tt = Some true.
  Proof.
    unfold checker_backtrack. generalize false at 2.
    induction l.
    - intros b. destruct b; split; try (intros; congruence).
      * intros H. inv H. inv H0. inv H.
      * intros H. inv H. inv H0. inv H.
    - intros b. split.
      + intros H.
        destruct (a tt) eqn:Hdec.
        * destruct b0. exists a. split; eauto. now left.
          eapply IHl in H. destruct H. inv H.
          eexists; split; eauto. now right.
        * eapply IHl in H. destruct H. inv H.
          eexists; split; eauto. now right.
      + intros H. inv H. inv H0. inv H. rewrite H1. reflexivity.
        destruct (a tt). destruct b0. reflexivity.
        * eapply IHl. eexists. split; eauto.
        * eapply IHl. eexists. split; eauto.
  Qed.

  Lemma checker_backtrack_spec_false l :
    checker_backtrack l = Some false <->
    (forall f, List.In f l -> f tt = Some false).
  Proof.
    unfold checker_backtrack.
    induction l.
    - split; eauto. intros Heq; intros f Hin; inv Hin.
    - destruct (a tt) eqn:Hdec.
      * destruct b.
        -- split. congruence.
           intros Hin.
           assert (Hc : a tt = Some false).
           { eapply Hin. now left. } congruence.
        -- split.
           ++ intros Haux f Hin. inv Hin; eauto.
              eapply IHl; eauto.
           ++ intros Hin. eapply IHl. intros.
              eapply Hin. now right. 
      * split.
        -- intros H1 f Hin.
           
           revert H1. clear. intros H1; induction l.
           congruence.
           destruct (a tt).
           ++ destruct b. congruence. eauto.
           ++ eauto.
        -- intros Hall. 
           assert (Hc : a tt = Some false).
           { eapply Hall. now left. } congruence.
  Qed.

  Lemma destruct_match_true_l (check b : option bool):
    match check with
    | Some true => b
    | Some false => Some false
    | None => None
    end = Some true ->
    check = Some true /\ b = Some true. 
  Proof.
    intros H. destruct check as [ [ | ] | ]; eauto; discriminate.
  Qed.

  Lemma destruct_match_false_l (check b : option bool):
    match check with
    | Some false => b
    | Some true => Some false
    | None => None
    end = Some true ->
    check = Some false /\ b = Some true. 
  Proof.
    intros H. destruct check as [ [ | ] | ]; eauto; discriminate.
  Qed.

  Lemma destruct_match_true_r (check b : option bool):
    check = Some true -> b = Some true ->
    match check with
    | Some true => b
    | Some false => Some false
    | None => None
    end = Some true. 
  Proof.
    intros H1 H2. destruct check as [ [ | ] | ]; eauto; discriminate.
  Qed.


  Lemma exists_match check k s1 :        
    check s1 = Some true ->
    (forall s1 s2, s1 <= s2 -> check s1 = Some true -> check s2 = Some true) ->
    (exists s, k (max s1 s) = Some true) ->
    (exists (s : nat) ,
        match check s with
        | Some true => k s
        | Some false => Some false
        | None => None
        end = Some true).
  Proof.
    intros Hch Hmon Hk. destruct Hk as [s2 Hk].
    eexists (max s1 s2).
    erewrite Hmon > [ | | eassumption ].
    eassumption. lia.
  Qed.  

  
  Lemma exists_match_decOpt P {_ : DecOpt P} { _ : DecOptSizeMonotonic P }
        s1 k :
    decOpt s1 = Some true ->
    (exists s, k (max s1 s) = Some true) ->
    (exists (s : nat),
        match decOpt s with
        | Some true => k s
        | Some false => Some false
        | None => None
        end = Some true).
  Proof.
    intros. eapply exists_match; eauto.
  Qed.

  Lemma checker_backtrack_spec_exists (l : nat -> list (unit -> option bool))  :
    (exists (f : nat -> (unit -> option bool)),
        (forall s, List.In (f s) (l s)) /\ exists s, f s tt = Some true) ->
    exists s, checker_backtrack (l s) = Some true.                               
  Proof.
    intros [f [Hall [s Heq]]].
    eexists s. eapply checker_backtrack_spec. eexists.
    split; eauto.
  Qed.

  Lemma exists_Sn (P : nat -> Prop) : 
    (exists n, P (S n)) -> exists n, P n.
  Proof.
    intros [n H]. eexists; eauto.
  Qed.


  Lemma exfalso_none_some_false (P : Prop) :
    (fun (_ : unit) => None) tt = Some false -> P. 
  Proof. congruence. Qed.

  Lemma enumerating_complete' A (e : E A) ch {Hm : SizeMonotonic e} {Hc : Correct A e} :
    (forall x s1 s2, (s1 <= s2) -> ch s1 x = Some true -> ch s2 x = Some true) ->
    (exists x s, ch s x = Some true) ->
    (exists (s : nat),
        enumerating e (ch s) s = Some true).
  Proof.
    intros Hmon [x [s Hch]].
    unfold enumerating.
    assert (Hin : semProd e x).
    { eapply Hc. reflexivity. }
    destruct Hin as [s' [_ Hsem]]. simpl in *.
    unfold semEnumSize in *.  

    assert (Hsem' : LazyList.In_ll x (Enumerators.run e (max s s'))).
    { eapply Hm > [| simpl; eassumption ]. lia. }
    clear Hsem.
    exists (max s s'). revert Hsem'.    
    generalize (Enumerators.run e (max s s')), false.
    induction l; intros b Hin; inv Hin; simpl.
    - erewrite Hmon > [ reflexivity | | eassumption ]. lia.
    - destruct (ch (Nat.max s s') a); eauto.
      destruct b0; eauto.
  Qed.

  Lemma enumeratingOpt_complete' A (e : E (option A)) ch P {Hm : SizeMonotonicOpt e} {Hc : CorrectST P e} :
    (forall x s1 s2, (s1 <= s2) -> ch s1 x = Some true -> ch s2 x = Some true) ->
    (exists x, P x /\ exists s, ch s x = Some true) ->
    (exists (s : nat),
        enumeratingOpt e (ch s) s = Some true).
  Proof.
    intros Hmon [x [Hp [s Hch]]].
    unfold enumeratingOpt.
    assert (Hin : semProdOpt e x).
    { eapply Hc. eassumption. }
    destruct Hin as [s' [_ Hsem]]. simpl in *.
    unfold semEnumSize in *.  

    assert (Hsem' : LazyList.In_ll (Some x) (Enumerators.run e (max s s'))).
    { eapply Hm > [| simpl; eassumption ]. lia. }
    clear Hsem.
    exists (max s s'). revert Hsem'.    
    generalize (Enumerators.run e (max s s')), false.
    induction l; intros b Hin; inv Hin; simpl.
    - erewrite Hmon > [ reflexivity | | eassumption ]. lia.
    - destruct a; eauto. destruct (ch (Nat.max s s') a); eauto.
      destruct b0; eauto.
  Qed.
  
  Lemma enumeratingOpt_complete_simpl' A (e : E (option A)) ch {Hm : SizeMonotonicOpt e} {Hc : Correct (option A) e} :
    (forall x s1 s2, (s1 <= s2) -> ch s1 x = Some true -> ch s2 x = Some true) ->
    (exists x s, ch s x = Some true) ->
    (exists (s : nat),
        enumeratingOpt e (ch s) s = Some true).
  Proof.
    intros Hmon [x [s Hch]].
    unfold enumeratingOpt.
    assert (Hin : semProd e (Some x)).
    { eapply Hc. reflexivity. }
    destruct Hin as [s' [_ Hsem]]. simpl in *.
    unfold semEnumSize in *.  

    assert (Hsem' : LazyList.In_ll (Some x) (Enumerators.run e (max s s'))).
    { eapply Hm > [| simpl; eassumption ]. lia. }
    clear Hsem.
    exists (max s s'). revert Hsem'.    
    generalize (Enumerators.run e (max s s')), false.
    induction l; intros b Hin; inv Hin; simpl.
    - erewrite Hmon > [ reflexivity | | eassumption ]. lia.
    - destruct a; eauto. destruct (ch (Nat.max s s') a); eauto.
      destruct b0; eauto.
  Qed.

  Lemma exists_match' check k s1 :        
    check s1 = Some true ->
    (forall s1 s2, (s1 <= s2) -> check s1 = Some true -> check s2 = Some true) ->
    (forall s1 s2, (s1 <= s2) -> k s1 = Some true -> k s2 = Some true) ->
    (exists s, k s = Some true) ->
    (exists (s : nat) ,
        match check s with
        | Some true => k s
        | Some false => Some false
        | None => None
        end = Some true).
  Proof.
    intros Hch Hmon Hmon' Hk. destruct Hk as [s2 Hk].
    eexists (max s1 s2).
    erewrite Hmon > [ | | eassumption ].
    eapply Hmon' > [ | eassumption ]. lia. lia.
  Qed.  


  Lemma exists_match_false' check k s1 :        
    check s1 = Some false ->
    (forall s1 s2, (s1 <= s2) -> check s1 = Some false -> check s2 = Some false) ->
    (forall s1 s2, (s1 <= s2) -> k s1 = Some true -> k s2 = Some true) ->
    (exists s, k s = Some true) ->
    (exists (s : nat) ,
        match check s with
        | Some false => k s
        | Some true => Some false
        | None => None
        end = Some true).
  Proof.
    intros Hch Hmon Hmon' Hk. destruct Hk as [s2 Hk].
    eexists (max s1 s2).
    erewrite Hmon > [ | | eassumption ].
    eapply Hmon' > [ | eassumption ]. lia. lia.
  Qed.  

End Lemmas. 


(** Monotonicity *)

Ltac2 revert_params (l : ident list) :=
  List.iter (fun x => try (revert $x)) l.

Ltac2 intro_params (l : ident list) :=
  List.iter (fun x => try (intro $x)) (List.rev l).

Ltac2 rec in_list_last (_ : unit) :=
  match! goal with
  | [ |- List.In _ (Datatypes.cons _ Datatypes.nil) ] => now left
  | [ |- List.In _ (Datatypes.cons _ _) ] => right; in_list_last ()
  end.

Ltac2 simpl_minus_methods (_ : unit) :=
  ltac1:(with_strategy opaque [enumSizeST enum decOpt enumSized] simplstar).


Ltac2 find_size_mon_inst (_ : unit) :=
  first [ tci
        | eapply sizedSizeMonotonicOpt; tci
        | eapply sizedSizeMonotonic; tci ].

Ltac2 find_size_fp_inst (_ : unit) :=
  first [ tci
        | eapply sizedSizeFP; tci ].

Ltac2 handle_checker_mon_t (ih : ident) (heq : ident) := 
  first
    [ (* decOpt matcing *)
      let heq1 := Fresh.in_goal heq in
      let heq' := Control.hyp heq in
      (* because apply .... in $heq doesn't work *)
      first [ assert ($heq1 := destruct_match_true_l _ _ $heq')
            | assert ($heq1 := destruct_match_false_l _ _ $heq') ];
      clear $heq;
      let heq1 := Control.hyp heq1 in
      let hdec := Fresh.in_goal (id_of_string "Hdec") in
      destruct $heq1 as [$hdec $heq];
      first
        [ (* other decOpt *)
          match! goal with
          | [ h : @decOpt ?p _ ?s = Some _ |- _ ] =>
            eapply (@mon $p _ _) in $h > [ | eassumption ];
            let hdec' := Control.hyp hdec in
            rewrite $hdec'; clear $hdec
          end
        | (* rec call *)
          let ih := Control.hyp ih in
          eapply $ih in $hdec > [ | first [ eassumption | now eapply le_S_n; eauto ] | eassumption ];
          let hdec' := Control.hyp hdec in
          rewrite $hdec'; clear $hdec ]                         
    | (* input matching *)
      match! goal with
      | [h : match ?m with _ => _  end = Some true |- _ ] =>
        destruct $m; try (congruence)
      end
    (* | (* enumerating *) *)
    (* XXX all enumerators should be OPT. This case should not arise *) 
    (*   eapply enumerating_monotonic > *)
    (*   [ now find_size_mon_inst () *)
    (*   | eassumption *)
    (*   | intro; clear $heq; simpl_minus_methods (); intro $heq *)
    (*   | eassumption ] *)
    | (* enumeratingOpt *)
      eapply enumeratingOpt_monotonic >
      [ now find_size_mon_inst ()
      | now find_size_fp_inst ()
      | eassumption
      | intro; simpl_minus_methods (); clear $heq; intro $heq
      | eassumption ]    
    | reflexivity ].



Ltac2 rec base_case_mont_aux (t : unit) (path : unit -> unit) :=
  match! goal with
  | [h : List.In _ Datatypes.nil |- _ ] => let h := Control.hyp h in destruct $h
  | [h : List.In _ (Datatypes.cons ?g Datatypes.nil) |- _ ] =>
    let h := Control.hyp h in destruct $h > [ subst; congruence | base_case_mont_aux () path ]
  | [h : List.In _ (Datatypes.cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    try (destruct $h > [ eexists;
                         split > [ path () ; left ; reflexivity | subst; now repeat (simpl_minus_methods (); handle_checker_mon_t @IH1 @Heq) ]
                       |  ]);
    base_case_mont_aux () (fun _ => path (); right)
end.

Ltac2 rec ind_case_mont_aux (ih : ident) (heq : ident) (path : unit -> unit) :=
  match! goal with
  | [h : List.In _ Datatypes.nil |- _ ] => let h := Control.hyp h in destruct $h
  | [h : List.In _ (Datatypes.cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    destruct $h > [ eexists;
                    split > [ path () ; left ; reflexivity | subst; now repeat (simpl_minus_methods (); handle_checker_mon_t @IH1 @Heq) ]
                  | ind_case_mont_aux ih heq (fun _ => path (); right) ]
                    
                    
  end.

Ltac2 base_case_mont (t : unit) := base_case_mont_aux () (fun _ => ()).

Ltac2 ind_case_mont (ih : ident) (heq : ident) :=
  ind_case_mont_aux ih heq (fun _ => ()).



Ltac2 handle_checker_mon_f (ih : ident) (heqb : ident) := 
  first
    [ congruence
    | (* decOpt matching *)
      let heqb := Fresh.in_goal @heqb in
      match! goal with
      | [ _ :  match ?e with | Some _ => match _ with | true => _ | false => _ end | None => _ end = Some false |- _ ] =>
        (destruct $e as [ [ | ] | ] eqn:$heqb > [ | | congruence ]);
          first
          [ match! goal with
            | [ h : @decOpt ?p _ ?s = Some _ |- _ ] =>
              eapply (@mon $p _ _) in $h > [ | eassumption ];
              let heqb' := Control.hyp heqb in
              rewrite $heqb'; clear $heqb; try reflexivity
            end
          | let ih := Control.hyp ih in
            eapply $ih in $heqb > [ | now eapply le_S_n; eauto | eassumption ];
            let heqb' := Control.hyp heqb in
            rewrite $heqb'; clear $heqb; try reflexivity
          ]
      end
    | (* input matching *)
      match! goal with
      | [ _ : match ?e with _ => _ end = Some false |- _ ] =>
        destruct $e; try reflexivity
      end
    (* | (* enumerating *) *)
    (* XXX all enumerators should be OPT. This case should not arise *) 
    (*   eapply enumerating_monotonic > *)
    (*   [ now find_size_mon_inst () *)
    (*   | eassumption *)
    (*   | intro; simpl_minus_methods (); clear $heqb; intro $heqb *)
    (*   | eassumption ] *)
    | (* enumeratingOpt *)
      eapply enumeratingOpt_monotonic >
      [ now find_size_mon_inst ()
      | now find_size_fp_inst ()
      | eassumption
      | intro; simpl_minus_methods (); clear $heqb; intro $heqb
      | eassumption ]
    ].


Ltac2 rec base_case_monf_aux (heqb : ident) (path : unit -> unit) :=
  match! goal with
  | [h : List.In _ Datatypes.nil |- _ ] => let h := Control.hyp h in destruct $h
  | [h : List.In _ (Datatypes.cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    first [ (destruct $h > [ eapply checker_backtrack_spec_false in Hdec (* TODO fix name ... *) > [ | path (); now left ];
                             subst; simpl_minus_methods (); now repeat (handle_checker_mon_f @dummy heqb)
                           |  base_case_monf_aux heqb (fun _ => path (); right) ] )
          | base_case_monf_aux heqb (fun _ => path (); right) ]
    end.

Ltac2 base_case_monf (heqb : ident) :=
  base_case_monf_aux heqb (fun _ => ()).

(* Zoe : if it has inductive cases this is required... *) 
Ltac2 base_case_monf_None (_ : unit) :=
  apply exfalso_none_some_false;
  (eapply checker_backtrack_spec_false with (f := (fun (_ : unit) => @None bool))) >
  [ eassumption | in_list_last () ].


Ltac2 rec ind_case_monf_aux (t : unit) (path : unit -> unit) :=
  match! goal with
  | [h : List.In _ Datatypes.nil |- _ ] => let h := Control.hyp h in destruct $h
  | [h : List.In _ (Datatypes.cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    destruct $h > [ eapply checker_backtrack_spec_false in Hdec (* TODO fix name ... *) > [ | path (); now left ]
                  | ind_case_monf_aux () (fun _ => path (); right) ]
  end.


Ltac2 ind_case_monf (ih : ident) (heqb : ident) :=
  (ind_case_monf_aux () (fun _ => ())); subst;
  repeat (simpl_minus_methods (); handle_checker_mon_f ih heqb).

Ltac2 derive_mon_aux (l : ident list) :=
  (induction s1 as [ | s1 IH1 ];
  (intro_params l;
  intros s2 b s2' s1' Hleq Hleq' Hdec);
  destruct b) >
  [ (* base case true *)
    (destruct s2;
     (* simplify and apply checker_backtrack_spec *)
     apply checker_backtrack_spec in Hdec;
     destruct Hdec as [f [Hin Heq]];
     apply checker_backtrack_spec) > 
    [ first [ eassumption | now base_case_mont () ] | now base_case_mont () ]
  | (* base case false *)  
    first
      [ now base_case_monf_None ()
      | (destruct s2; eapply checker_backtrack_spec_false; intros f Hin) >
        [ first [ eassumption | now base_case_monf @Heq ]
        | now base_case_monf @Heq ] ]
  | (* ind case true *)
    destruct s2 > [ lia | ];
    (* simplify and apply checker_backtrack_spec *)
    apply checker_backtrack_spec in Hdec;
    destruct Hdec as [f [Hin Heq]];
    apply checker_backtrack_spec;
    now ind_case_mont @IH1 @Heq
  | (* ind case false *)
    destruct s2 > [ lia | ];
    eapply checker_backtrack_spec_false;
    intros f Hin; now ind_case_monf @IH1 @Heq
  ].


Ltac2 derive_mon (_ : unit) :=
  match! goal with
  | [ |- DecOptSizeMonotonic ?e ] =>
    match Constr.Unsafe.kind e with
    | Constr.Unsafe.App ty args  =>
      let l := constrs_to_idents (Array.to_list args) in
      intros s1 s2 b Hleq; unfold decOpt; simpl_minus_methods ();
      assert (Hleq' := &Hleq); revert Hleq Hleq';
      generalize &s1 at 2 3 as s1'; generalize &s2 at 2 3 as s2';
      revert s2 b; revert_params l; derive_mon_aux l
   | _ => () 
   end
end.


(* For deriving monotonicity inside the completness proof *)

Ltac2 derive_mon_true (l : ident list) :=
  (intro s1; induction s1 as [ | s1 IH1 ];
  intros s2 s2' s1' Hleq Hleq';
  intro_params l; intro Hdec) >
  [ (* base case true *)
    (destruct s2;
     (* simplify and apply checker_backtrack_spec *)
     apply checker_backtrack_spec in Hdec;
     destruct Hdec as [f [Hin Heq]];
     apply checker_backtrack_spec) > 
    [ first [ eassumption | now base_case_mont () ] | now base_case_mont () ]
  | (* ind case true *)
    destruct s2 > [ lia | ];
    (* (* simplify and apply checker_backtrack_spec *) *)
    apply checker_backtrack_spec in Hdec;
    destruct Hdec as [f [Hin Heq]];
    apply checker_backtrack_spec;
    now ind_case_mont @IH1 @Heq
  ].


(** Soundness *)

Ltac2 find_CorrectST_inst (_ : unit) :=
  match! goal with
  | [ |- CorrectST _ (sizedEnum (@enumSizeST ?t ?pred ?inst)) ] =>
    eapply (@size_CorrectST $t $pred E _ _) >
    [ tci
    | find_size_mon_inst ()
    | eauto 20 with typeclass_instances ]
  end.

Ltac2 handle_checker_match_sound (ih : ident) (heq : ident) :=
  first
    [ (* match is the current inductive type *)
      let heq1 := Fresh.in_goal heq in
      let heq' := Control.hyp heq in
      assert ($heq1 := destruct_match_true_l _ _ $heq'); clear $heq;
      let heq1 := Control.hyp heq1 in
      let ih := Control.hyp ih in      
      let hdec := Fresh.in_goal (id_of_string "Hdec") in
      destruct $heq1 as [$hdec $heq]; eapply $ih in $hdec
    | (* match is an other inductive type *)
      let heq1 := Fresh.in_goal heq in
      let heq' := Control.hyp heq in
      first [ assert ($heq1 := destruct_match_true_l _ _ $heq')
            | assert ($heq1 := destruct_match_false_l _ _ $heq') ]; clear $heq;
      let heq1 := Control.hyp heq1 in
      let hdec := Fresh.in_goal (id_of_string "Hdec") in
      destruct $heq1 as [$hdec $heq];
      (* TODO match hdec directly *) 
      match! goal with
      | [ h : @decOpt ?p _ ?s = Some true |- _ ] =>
        eapply (@sound $p _ _) in $h
      | [ h : @decOpt ?p _ ?s = Some false |- _ ] =>
        eapply (@sound_neg $p _ _) in $h
      end
    | (* match is an input *) 
      match! goal with
      | [h : match ?m with _ => _  end = Some true |- _ ] =>
        destruct $m; try (congruence)
      end
    | (* enumeratingOpt constrained *)
      match! goal with
      | [h : enumeratingOpt _ _ _ = Some true |- _ ] =>
        eapply enumeratingOpt_sound in $h > [ | find_CorrectST_inst () ];
        let h' := Control.hyp h in
        destruct $h' as [? [? $h ]]
      end
    | (* enumeratingOpt simpl *)
      match! goal with
      | [h : enumeratingOpt _ _ _ = Some true |- _ ] =>
        eapply enumeratingOpt_sound_simpl in $h;
        let h' := Control.hyp h in
        destruct $h' as [? $h]
      end
    ].


Ltac2 rec base_case_sound (heq : ident) (ty : constr) :=
  match! goal with
  | [h : List.In _ Datatypes.nil |- _ ] => let h := Control.hyp h in destruct $h
  | [h : List.In _ (Datatypes.cons ?g Datatypes.nil) |- _ ] =>
    let h := Control.hyp h in (destruct $h > [ subst; congruence | base_case_sound heq ty])
  | [h : List.In _ (Datatypes.cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    let hdummy := Fresh.in_goal (id_of_string "Hdummy") in
    (destruct $h > [ subst; repeat (handle_checker_match_sound hdummy heq); subst; first [ eauto using $ty
                                                                                         | now (eauto 20 using $ty) ]
                   | base_case_sound heq ty ])
  end.

Ltac2 rec ind_case_sound (ih : ident) (heq : ident) (ty : constr) :=
  match! goal with
  | [h : List.In _ Datatypes.nil |- _ ] => let h := Control.hyp h in destruct $h
  | [h : List.In _ (Datatypes.cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    (destruct $h > [ subst; repeat (handle_checker_match_sound ih heq); subst; first [ eauto using $ty
                                                                                     | now (eauto 20 using $ty) ]
                   | ind_case_sound ih heq ty ])
  end.



Ltac2 derive_sound (_ : unit) :=
  match! goal with
  | [ |- DecOptSoundPos ?e ] =>
    match Constr.Unsafe.kind e with
    | Constr.Unsafe.App ty args  =>
      let l := constrs_to_idents (Array.to_list args) in
      intros s; unfold decOpt; simpl_minus_methods ();
      (* assert (Hleq' := &Hleq); revert Hleq Hleq'; *)
      generalize &s at 1 as s';
      revert_params l;
      ((induction s as [ | s IH1 ]);
       intro_params l;
       intros s' Hdec;
       eapply checker_backtrack_spec in Hdec;
       destruct Hdec as [f [Hin Htrue]]) > [ base_case_sound @Htrue ty | ind_case_sound @IH1 @Htrue ty ]
   | _ => () 
   end 
end.


(** Completeness *)

Ltac2 make_prod (bs : constr array) (c : constr) :=
  let bs := Array.map (fun b => let t := Constr.type b in
                                Constr.Binder.make (Some (constr_to_ident b)) t) bs in
  
  Array.fold_left (fun t b => Constr.Unsafe.make (Constr.Unsafe.Prod b t)) c bs.

(* Proves monotonicity assertion inside completness proof *)
Ltac2 prove_mon (_ : unit) :=
  match! goal with
  | [ |- ex ?p ] =>
    match Constr.Unsafe.kind p with
    | Constr.Unsafe.Lambda b eq =>
      match Constr.Unsafe.kind eq with
      | Constr.Unsafe.App t eq_args =>
        let app := Array.get eq_args 1 in
        match Constr.Unsafe.kind app with
        | Constr.Unsafe.App aux args =>              
          let make_eq (lhs : constr) :=
              let a := Array.copy eq_args in
              Array.set a 1 lhs; Constr.Unsafe.make (Constr.Unsafe.App t a) in
              let make_impl (t1 : constr) (t2 : constr) :=
                  let b := Constr.Binder.make None t1 in
                  Constr.Unsafe.make (Constr.Unsafe.Prod b t2)
              in
              let inner_term  (t1 : constr) (t2 : constr) :=
                  make_impl (make_eq t1) (make_eq t2)
              in
              
              let len := Int.sub (Array.length args) 2 in
              let inps := Array.sub args 2 len in
              
              let args (s1 : constr) (s2 : constr) (offs : int) :=
                  let ind := Array.mapi (fun i _ => Constr.Unsafe.make (Constr.Unsafe.Rel (Int.add i offs))) inps in
                  let a := Array.make 2 s1 in
                  Array.set a 1 s2; Array.append a ind
              in
              let term (s1 : constr) (s2 : constr) (offs : int) :=
                  Constr.Unsafe.make (Constr.Unsafe.App aux (args s1 s2 offs))
              in
              let prod_term (t1 : constr) (t2 : constr) := make_prod inps (inner_term t1 t2) in
              let mon (s1 : constr) (s2 : constr) (s1' : constr) (s2' : constr) :=
                  let t1 := (term s1' s1 1) in
                  let t2 := (term s2' s2 2) in
                  prod_term t1 t2 in
              
              let l := constrs_to_idents (Array.to_list inps) in
              assert (Hmon : forall (s1 : nat) (s2 s2' s1': nat), s1 <= s2 -> s1' <= s2' ->
                                                                  ltac2:(let s1 := Control.hyp @s1 in
                                                                         let s1' := Control.hyp @s1' in
                                                                         let s2 := Control.hyp @s2 in
                                                                         let s2' := Control.hyp @s2' in
                                                                         let t := mon s1 s2 s1' s2' in exact $t)) >
              [  List.iter clear_dependent l; now derive_mon_true l | ]
        | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
        end
      | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
      end
    | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting a lambda"))))
    end
  end.


Ltac2 prove_ih (ih : ident) :=
  match! goal with
  | [ |- ex ?p ] =>
    match Constr.Unsafe.kind p with
    | Constr.Unsafe.Lambda b eq =>
      match Constr.Unsafe.kind eq with
      | Constr.Unsafe.App t eq_args =>
        let m := Array.get eq_args 1 in          
        match Constr.Unsafe.kind m with
        | Constr.Unsafe.Case _ _ _ a _  =>            
          match Constr.Unsafe.kind a with
          | Constr.Unsafe.App f args =>
            
            let make_app (a : constr) :=
                let args' := Array.copy args in
                let _ := Array.set args' 0 a in
                let _ := Array.set args' 1 a in                 
                let a := Constr.Unsafe.App f args' in
                Constr.Unsafe.make a
            in
            
            let ih := Fresh.in_goal (id_of_string "IH") in
            let s := Fresh.in_goal (id_of_string "s") in
            (* Create the IH and prove it from the context. *)
            (* Kind of hacky because I don't know how to create a cpattern from the term. *)
            assert ($ih : exists (k : nat),
                       ltac2:(let b := Control.hyp @k in
                              let t := make_app b in exact $t) = Some true)
              by eassumption
          | _ => ()
                   (* Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an app")))) *)
          end
        | _ => ()
                 (* Control.throw (Tactic_failure (Some (Message.of_string ("Expecting a case")))) *)
        end
      | _ => ()
             (* Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an app")))) *)
      end
    | _ => ()
             (* Control.throw (Tactic_failure (Some (Message.of_string ("Expecting a lambda")))) *)
    end
  end.


Ltac2 destructIH (_ : unit) :=
  match! goal with
  | [ h : (exists s, _ = Some true) |- _ ] =>
    let h' := Control.hyp h in destruct $h'
  end.

Ltac2 rec handle_checker (hmon : ident) :=
  first [ exists 0 ; reflexivity
        | match! goal with
          | [ |- exists s, match @decOpt ?p ?i _ with _ => _ end = Some true ] =>
            let hc := Fresh.in_goal (id_of_string "Hc") in
            let s := Fresh.in_goal (id_of_string "s") in
            assert ($hc := @complete $p _ _ (ltac2:(now eauto)));
            let hc1 := Control.hyp hc in
            destruct $hc1 as [$s $hc];
            let s1 := Control.hyp s in
            eapply exists_match' with (s1 := $s1) >
                                      [ eapply (@mon $p _ _) > [ | eassumption ]; lia
                                      | intros; eapply (@mon $p _ _) > [ | eassumption ]; lia
                                      | let heq := Fresh.in_goal (id_of_string "_heq") in
                                        intros ? ? ? $heq; 
                                        now repeat (simpl_minus_methods (); handle_checker_mon_t hmon heq)
                                      | handle_checker hmon ]
          end
        | match! goal with
          | [ |- exists s, match @decOpt ?p ?i _ with _ => _ end = Some true ] =>
            let hc := Fresh.in_goal (id_of_string "Hc") in
            let s := Fresh.in_goal (id_of_string "s") in
            assert ($hc := @complete_neg $p _ _ (ltac2:(now eauto)));
            let hc1 := Control.hyp hc in
            destruct $hc1 as [$s $hc];
            let s1 := Control.hyp s in
            eapply exists_match_false' with (s1 := $s1) >
                                      [ eapply (@mon $p _ _) > [ | eassumption ]; lia
                                      | intros; eapply (@mon $p _ _) > [ | eassumption ]; lia
                                      | let heq := Fresh.in_goal (id_of_string "_heq") in
                                        intros ? ? ? $heq; 
                                        now repeat (simpl_minus_methods (); handle_checker_mon_t hmon heq)
                                      | handle_checker hmon ]
          end

       |
          (* let ih := Fresh.in_goal (id_of_string "IH") in *)
          (* let s := Fresh.in_goal (id_of_string "s") in *)
          (* prove_ih ih; *)
          (* let ih1 := Control.hyp ih in *)
          (* destruct $ih1 as [$s $ih]; *)
          (* let s1 := Control.hyp s in *)
          (* TODO remove comments when stable *)
          eapply exists_match'  >
          [ ()
          | let hmon := Control.hyp hmon in
            intros; eapply $hmon > [| | eassumption ] > [ lia | lia ]
          | let heq := Fresh.in_goal (id_of_string "_heq") in
            intros ? ? ? $heq; 
            now repeat (simpl_minus_methods (); handle_checker_mon_t hmon heq)
          | handle_checker hmon ]; eassumption                                     
        | (* enumeratingOpt constrained *)
          eapply enumeratingOpt_complete' >        
          [ now find_size_mon_inst ()
          | now find_CorrectST_inst ()
          | let heq := Fresh.in_goal (id_of_string "_heq") in
            intros ? ? ? ? $heq; 
            now repeat (simpl_minus_methods (); handle_checker_mon_t hmon heq)
          | eexists; split > [ | handle_checker hmon ] ]; eassumption
        | (* enumeratingOpt constrained alt *)
          eapply enumeratingOpt_complete' >        
          [ now find_size_mon_inst ()
          | now find_CorrectST_inst ()
          | let heq := Fresh.in_goal (id_of_string "_heq") in
            intros ? ? ? ? $heq; 
            now repeat (simpl_minus_methods (); handle_checker_mon_t hmon heq)
          | eexists; split > [ eassumption | handle_checker hmon ] ]
        | (* enumeratingOpt simpl *)
          eapply enumeratingOpt_complete_simpl' >
          [ now find_size_mon_inst ()
          | tci
          | let heq := Fresh.in_goal (id_of_string "_heq") in
            intros ? ? ? ? $heq; 
            now repeat (simpl_minus_methods (); handle_checker_mon_t hmon heq)
          | eexists; handle_checker hmon ]

        ].

Ltac2 rec path_aux (m : int) (n : int) :=
  match Int.equal n m with
  | true => left
  | false => right; path_aux m (Int.add n 1)
end.

Ltac2 rec path (n : int) := path_aux n 0.


Ltac2 handle_base_case (hmon : ident) := handle_checker hmon.


Ltac2 rec solve_ind_case (hmon : ident) (n : int) :=
  first [ now eexists; split > [ intros ?; path n; reflexivity | 
                                 simpl_minus_methods (); repeat (destructIH ()); handle_checker hmon ]
        | solve_ind_case hmon (Int.add n 1) ].

Ltac2 rec handle_ind_case (hmon : ident) :=
  match! goal with
  | [ |- ?e ] =>
    match Constr.Unsafe.kind e with
    | Constr.Unsafe.App ex p =>
      let pr := Array.get p 1 in
      match Constr.Unsafe.kind pr with
      | Constr.Unsafe.Lambda b eq =>
        match Constr.Unsafe.kind eq with
        | Constr.Unsafe.App t eq_args =>
          let app := Array.get eq_args 1 in
          match Constr.Unsafe.kind app with
          | Constr.Unsafe.App aux args => 
            set (auxt := ltac2:(exact $aux));
            let succ (c : constr) :=
                match Constr.Unsafe.kind (constr:(S 0)) with
                | Constr.Unsafe.App s n =>
                  let n' := Array.copy n in
                  let _ := Array.set n' 0 c in
                  Constr.Unsafe.make (Constr.Unsafe.App s n')
                | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
                end
            in
            
            let args' := Array.copy args in
            let _ := Array.set args' 1 (succ (Array.get args 1)) in
            let aux' := Control.hyp @auxt in
            let app' := Constr.Unsafe.make (Constr.Unsafe.App aux' args') in
            let eq_args' := Array.copy eq_args in
            let _ := Array.set eq_args' 1 app' in
            let pr' := Constr.Unsafe.make (Constr.Unsafe.Lambda b (Constr.Unsafe.make (Constr.Unsafe.App t eq_args'))) in
            let p' := Array.make 2 (Array.get p 0) in
            let _ := Array.set p' 1 pr' in
            
            let e' := Constr.Unsafe.make (Constr.Unsafe.App ex p') in
            
            let s := Fresh.in_goal (id_of_string "s") in
            let hyp := Fresh.in_goal (id_of_string "Hyp") in
            assert (Hsuff : ltac2:(exact $e')) >
            [ | destruct Hsuff as [$s $hyp];
                let s1 := Control.hyp s in
                let hmon := Control.hyp hmon in 
                eexists (S $s1); eapply $hmon > [ | | eassumption ]; lia ];
                eapply checker_backtrack_spec_exists; solve_ind_case hmon 0                                     
          | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
          end
        | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
        end
      | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting a lambda"))))
      end
    | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
    end
  end.

Ltac2 derive_complete (_ : unit ) := 
  intros __H; unfold decOpt; simpl_minus_methods (); 
  prove_mon ();
  induction __H; first [ now handle_base_case @Hmon | now handle_ind_case @Hmon ].


(* Ltac tactics *)
Ltac derive_mon := ltac2:(derive_mon ()).
Ltac derive_sound := ltac2:(derive_sound ()).
Ltac derive_complete := ltac2:(derive_complete ()).
