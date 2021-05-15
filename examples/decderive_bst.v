From Coq Require Import Init.Nat Lia.
From QuickChick Require Import QuickChick.
From mathcomp Require Import ssreflect ssreflect.eqtype.
Import QcNotation. Import QcDefaultNotation.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.
From Ltac2 Require Import Constr.

Require Import ExtLib.Structures.Monads.
Open Scope monad_scope.
Open Scope qc_scope.
Open Scope nat_scope.



Ltac2 ltac1_congruence () := Ltac1.run (Ltac1.ref [ident:(Coq); ident:(Init); ident:(Prelude); ident:(congruence)]).
Ltac2 Notation "congruence" := ltac1_congruence ().

(* From https://github.com/tchajed/coq-ltac2-experiments/blob/master/src/Ltac2Lib.v *)
Local Ltac2 inv_tac (h: ident) := Std.inversion Std.FullInversion (Std.ElimOnIdent h) None None; subst; Std.clear [h].
Ltac2 Notation "inv" h(ident) := inv_tac h.

Local Ltac2 exfalso_tac () := ltac1:(exfalso).
Ltac2 Notation "exfalso" := exfalso_tac ().

Local Ltac2 lia_ltac1 () := ltac1:(micromega.Lia.lia).
Ltac2 Notation "lia" := lia_ltac1 ().

Ltac2 inv := fun (h : ident) =>  inversion h; subst.

Ltac2 eassumption_ltac2 () := ltac1:(eassumption).
Ltac2 Notation "eassumption" := eassumption_ltac2 ().

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

  
  (* Not true: *) 
  (* Class DecOptCorrect (P : Prop) {H : DecOpt P} := *)
  (*   { refl_decOpt : forall s, ssrbool.reflect P (decOpt s == Some true) }. *)

  
  (* Coersions from [Dec] *)
  
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

  Global Instance decCorrectNeg (P : Prop) {_ : Dec P} : DecOptCorrectNeg P.
  Proof.
    constructor. 
    - intros s.
      unfold decOpt, dec_decOpt, dec. destruct H.
      destruct dec; eauto. congruence.
    - intros s.
      unfold decOpt, dec_decOpt, dec. destruct H.
      exists 0.
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

  Inductive wf_list : list nat -> Prop :=
  | lnil : wf_list nil
  | lcons :
      forall l,
        wf_list l -> wf_list l.
  
  Derive DecOpt for (wf_list l).
  Print DecOptwf_list.

  Inductive wf_list2 : list nat -> Prop :=
  | lcons2 :
      forall l,
        wf_list2 l -> wf_list2 l.

  Derive DecOpt for (wf_list2 l).
  
  (* Counter-example for completess *) 
  Goal (forall l, ~ wf_list2 l).
  Proof.
    intros l Hwf. induction Hwf; eauto.
  Qed. 
  
End TypeClasses.

(* Lemmas for checkers *)
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


End Lemmas. 

From Ltac2 Require Import Fresh.

(* Tactics for deriving monotonicity. TODO move to some library *)
Ltac2 constr_to_ident (a : Init.constr) :=
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.Var i => i
  | _ => Control.throw (Tactic_failure (Some (Message.of_string ("constr is not a var"))))
  end.

Ltac2 constrs_to_idents (a : Init.constr list) := List.map constr_to_ident a.

Opaque dec_decOpt.


Ltac2 rec in_list_last (_ : unit) :=
  match! goal with
  | [ |- List.In _ (cons _ nil) ] => now left
  | [ |- List.In _ (cons _ _) ] => right; in_list_last ()
  end.

Lemma exfalso_none_some_false (P : Prop) :
  (fun (_ : unit) => None) tt = Some false -> P. 
Proof. congruence. Qed.

Ltac simplstar := simpl in *.

Ltac2 simpl_minus_decOpt (_ : unit) :=
  ltac1:(with_strategy opaque [decOpt] simplstar).

Ltac2 id_of_string (s : string) :=
  match Ident.of_string s with
  | Some i => i
  | None => Control.throw (Tactic_failure (Some (Message.of_string ("Not a valid string for identifier"))))
  end.

Ltac2 handle_checker_mon_t (ih : ident) (heq : ident) := 
  first
    [ let heq1 := Fresh.in_goal heq in
      let heq' := Control.hyp heq in
      (* because apply .... in $heq doesn't work *)
      assert ($heq1 := destruct_match_true_l _ _ $heq'); clear $heq;
      let heq1 := Control.hyp heq1 in
      let ih := Control.hyp ih in
      let hdec := Fresh.in_goal (id_of_string "Hdec") in
      destruct $heq1 as [$hdec $heq];
      first
        [ match! goal with
          | [ h : @decOpt ?p _ ?s = Some true |- _ ] =>
            eapply (@mon $p _ _) in $h > [ | eassumption ];
            let hdec' := Control.hyp hdec in
            rewrite $hdec'; clear $hdec
          end
        | eapply $ih in $hdec > [ | now eapply le_S_n; eauto | eassumption ];
          let hdec' := Control.hyp hdec in
          rewrite $hdec'; clear $hdec ]                         
    | match! goal with
      | [h : match ?m with _ => _  end = Some true |- _ ] =>
        destruct $m; try (congruence)
      end
    | reflexivity ].



Ltac2 rec base_case_mont_aux (t : unit) (path : unit -> unit) :=
  match! goal with
  | [h : List.In _ nil |- _ ] => let h := Control.hyp h in destruct $h
  | [h : List.In _ (cons ?g nil) |- _ ] =>
    let h := Control.hyp h in destruct $h > [ subst; congruence | base_case_mont_aux () path ]
  | [h : List.In _ (cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    try (destruct $h > [ eexists;
                         split > [ path () ; left ; reflexivity | subst; now repeat (handle_checker_mon_t @IH1 @Heq) ]
                       |  ]);
    base_case_mont_aux () (fun _ => path (); right)
end.

Ltac2 rec ind_case_mont_aux (ih : ident) (heq : ident) (path : unit -> unit) :=
  match! goal with
  | [h : List.In _ nil |- _ ] => let h := Control.hyp h in destruct $h
  | [h : List.In _ (cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    destruct $h > [ eexists;
                    split > [ path () ; left ; reflexivity | subst; now repeat (handle_checker_mon_t @IH1 @Heq) ]
                  | ind_case_mont_aux ih heq (fun _ => path (); right) ]
                    
                    
  end.

Ltac2 base_case_mont (t : unit) := base_case_mont_aux () (fun _ => ()).

Ltac2 ind_case_mont (ih : ident) (heq : ident) :=
  ind_case_mont_aux ih heq (fun _ => ()).

Ltac2 base_case_monf (_ : unit) :=
  apply exfalso_none_some_false;
  (eapply checker_backtrack_spec_false with (f := (fun (_ : unit) => @None bool))) >
  [ eassumption | in_list_last () ].


Ltac2 handle_ind_checkerf (ih : ident) (heqb : ident) := 
  first
    [ match! goal with
      | [ _ : match ?e with _ => _ end = Some false |- _ ] =>
        destruct $e > [ reflexivity | ]
      end
    | let ih := Control.hyp ih in
      let heqb := Fresh.in_goal @Heq in
      match! goal with
      | [ _ :  match ?e with _ => _ end = Some false |- _ ] =>
        (destruct $e as [ [ | ] | ] eqn:$heqb > [ | | congruence ])
      end;
      first
        [ match! goal with
          | [ h : @decOpt ?p _ ?s = Some _ |- _ ] =>
            eapply (@mon $p _ _) in $h > [ | eassumption ];
            let heqb' := Control.hyp heqb in
            rewrite $heqb'; clear $heqb; try reflexivity
          end
         | eapply $ih in $heqb > [ | now eapply le_S_n; eauto | eassumption ];
           let heqb' := Control.hyp heqb in
           rewrite $heqb'; clear $heqb; try reflexivity
        ]
    | congruence
    ].

Ltac2 rec ind_case_monf_aux (t : unit) (path : unit -> unit) :=
  match! goal with
  | [h : List.In _ nil |- _ ] => let h := Control.hyp h in destruct $h
  | [h : List.In _ (cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    destruct $h > [ eapply checker_backtrack_spec_false in Hdec > [ | path (); now left ] (* for inductive cases *)
                  | ind_case_monf_aux () (fun _ => path (); right) ]
  end.

Ltac2 ind_case_monf (ih : ident) (heqb : ident) :=
  (ind_case_monf_aux () (fun _ => ())); subst;
  simpl_minus_decOpt ();
  repeat (handle_ind_checkerf @IH1 @Heqb).


Ltac2 derive_mon (_ : unit) :=
  match! goal with
  | [ |- DecOptSizeMonotonic ?e ] =>
    match Constr.Unsafe.kind e with
    | Constr.Unsafe.App ty args  =>
      let l := constrs_to_idents (Array.to_list args) in
      intros s1 s2 b Hleq; unfold decOpt; simpl_minus_decOpt ();
      assert (Hleq' := &Hleq); revert Hleq Hleq';
      generalize &s1 at 2 3 as s1'; generalize &s2 at 2 3 as s2';
      revert s2 b;
      List.map (fun x => revert $x) l;
      (induction s1 as [ | s1 IH1 ];
       (List.map (fun x => intro $x) (List.rev l);
        intros s2 b s2' s1' Hleq Hleq' Hdec);
         destruct b) >
       [ (* base case true *)
         destruct s2 > [ assumption | ];
         (* simplify and apply checker_backtrack_spec *)
         apply checker_backtrack_spec in Hdec;
         destruct Hdec as [f [Hin Heq]];
         apply checker_backtrack_spec;
         now base_case_mont ()
       | (* base case false *)
          now base_case_monf ()
       | (* ind case true *)
          destruct s2 > [ lia | ];
         (* (* simplify and apply checker_backtrack_spec *) *)
         apply checker_backtrack_spec in Hdec;
         destruct Hdec as [f [Hin Heq]];
         apply checker_backtrack_spec;
         now ind_case_mont @IH1 @Heq
             
      | (* ind case false *)
        destruct s2 > [ lia | ];
        eapply checker_backtrack_spec_false;
        intros f Hin; now ind_case_monf @IH1 @Heq
      ]
    | _ => () 
       end
  end.


(* Soundness *)

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
    | (* match is the an other inductive type *)
      let heq1 := Fresh.in_goal heq in
      let heq' := Control.hyp heq in
      assert ($heq1 := destruct_match_true_l _ _ $heq'); clear $heq;
      let heq1 := Control.hyp heq1 in
      let ih := Control.hyp ih in      
      let hdec := Fresh.in_goal (id_of_string "Hdec") in
      destruct $heq1 as [$hdec $heq];
      (* TODO match hdec directly *) 
      match! goal with
      | [ h : @decOpt ?p _ ?s = Some true |- _ ] =>
        eapply (@sound $p _ _) in $h
      end
    | (* match is an input *) 
      match! goal with
      | [h : match ?m with _ => _  end = Some true |- _ ] =>
        destruct $m; try (congruence)
      end
    ].

Ltac2 rec try_constructors_aux (n : int) :=
  first [ now (econstructor n; eauto)
        | try_constructors_aux (Int.add n 1) ].


Ltac2 try_constructors (_ : unit) := try_constructors_aux 1.

Ltac2 eauto_using (e : constr) := eauto using $e. 

  Inductive test :=
  | Many_evars :
      forall n m x y,
        n <= m ->
        x <= y ->
        odd x = true ->
        test.

  Goal (forall n m x y, n <= m -> x <= y -> odd n = true -> test).
  Proof.
    eauto_using 'test.
  Qed. 
        
  (* Goal (bst 0 0 Leaf). *)
  (*   eauto_using 'bst. *)


Ltac2 rec base_case_sound (heq : ident) (ty : constr) :=
  match! goal with
  | [h : List.In _ nil |- _ ] => let h := Control.hyp h in destruct $h
  | [h : List.In _ (cons ?g nil) |- _ ] =>
    let h := Control.hyp h in (destruct $h > [ subst; congruence | base_case_sound heq ty])
  | [h : List.In _ (cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    let hdummy := Fresh.in_goal (id_of_string "Hdummy") in
    (destruct $h > [ subst; repeat (handle_checker_match_sound hdummy heq); now (eauto 20 using $ty)
                   | base_case_sound heq ty ])
  end.

Ltac2 rec ind_case_sound (ih : ident) (heq : ident) (ty : constr) :=
  match! goal with
  | [h : List.In _ nil |- _ ] => let h := Control.hyp h in destruct $h
  | [h : List.In _ (cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    (destruct $h > [ subst; repeat (handle_checker_match_sound ih heq); now (eauto 20 using $ty)
                   | ind_case_sound ih heq ty ])
  end.



Ltac2 derive_sound (_ : unit) :=
  match! goal with
  | [ |- DecOptSoundPos ?e ] =>
    match Constr.Unsafe.kind e with
    | Constr.Unsafe.App ty args  =>
      let l := constrs_to_idents (Array.to_list args) in
      intros s; unfold decOpt; simpl_minus_decOpt ();
      (* assert (Hleq' := &Hleq); revert Hleq Hleq'; *)
      generalize &s at 1 as s';
      List.map (fun x => revert $x) l;
      ((induction s as [ | s IH1 ]);
       (List.map (fun x => intro $x) (List.rev l));
       intros s' Hdec;
       eapply checker_backtrack_spec in Hdec;
       destruct Hdec as [f [Hin Htrue]]) > [ base_case_sound @Htrue ty | ind_case_sound @IH1 @Htrue ty ]
   | _ => () 
   end 
end.

Inductive tree :=
| Leaf : tree
| Node : nat -> tree -> tree -> tree.
Derive Show for tree.
Derive Arbitrary for tree.

Derive ArbitrarySizedSuchThat for (fun n => le n n').
Derive ArbitrarySizedSuchThat for (fun n' => le n n').

Inductive bst : nat -> nat -> tree -> Prop :=
| BstLeaf : forall n1 n2, bst n1 n2 Leaf
| BstNode : forall min max n t1 t2,
    le min max -> le min n -> le n max ->
    bst min n t1 -> bst n max t2 ->
    bst min max (Node n t1 t2).

(* Derive DecOpt for (le n m). *)
Derive DecOpt for (bst min max t).

Derive ArbitrarySizedSuchThat for (fun b => bst min max b).


Instance decOptbstSizeMonotonic m n t : DecOptSizeMonotonic (bst m n t).
Proof. derive_mon (). Qed. 
                       
Instance DecOptbst_sound m n t : DecOptSoundPos (bst m n t).
Proof. derive_sound (). Qed.

(* Compute (sample (@arbitrarySizeST _ (fun t => bst 0 30 t) _ 10)). *)


Conjecture expand_range : forall t,
    bst 0 30 t ->
    bst 0 40 t.
QuickChick expand_range.
Conjecture contract_range : forall t,
    bst 0 30 t ->
    bst 0 1 t.
QuickChick expand_range.
(* this shouldn't work *)

Fixpoint insert t x :=
  match t with
  | Leaf => Node x Leaf Leaf
  | Node a l r =>
    if a <= x ? then
      Node x (insert l x) r
    else
      Node x r (insert r x)
  end.


Inductive inrange : nat -> nat -> tree -> nat -> Prop :=
| InRange : forall t n max x,
    le n max ->
    bst 0 max t ->
    le x max ->
    inrange n max t x.
Derive DecOpt for (inrange n m t x).
Derive ArbitrarySizedSuchThat for (fun n => inrange n m t x).


(* Testing here doesn't work *)
(* Conjecture insert_invariant : *)
(*   forall t, *)
(*     inrange 30 30 t 30 -> *)
(*     bst 0 30 t. *)
(* QuickChick insert_invariant. *)


Inductive list_len : nat -> list nat -> Prop :=
| nil_len : list_len 0 nil
| cons_len :
    forall n x l,
      list_len n l ->
      wf_list l ->
      list_len (S n) (x :: l). 

Derive DecOpt for (list_len n l).

Instance DecOptwf_listSizeMonotonic l : DecOptSizeMonotonic (wf_list l).
Proof. derive_mon (). Qed. 

Instance DecOptwf_list_sound l : DecOptSoundPos (wf_list l).
Proof. derive_sound (). Qed.


Ltac2 rec ind_case_mont_aux' (ih : ident) (heq : ident) (path : unit -> unit) :=
  match! goal with
  | [h : List.In _ nil |- _ ] => let h := Control.hyp h in inversion $h
  | [h : List.In _ (cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    destruct $h > [ eexists; split > [ path () ; left ; reflexivity | subst ]
                  | ind_case_mont_aux' ih heq (fun _ => path; right) ]                    
  end.

Ltac2 ind_case_mont' (ih : ident) (heq : ident) :=
  ind_case_mont_aux' ih heq (fun _ => ()).

Instance DecOptlist_lenSizeMonotonic n l : DecOptSizeMonotonic (list_len n l).
Proof. derive_mon (). Qed. 

Instance DecOptlist_len_sound n l : DecOptSoundPos (list_len n l).
Proof. derive_sound (). Qed.


Section BSTProofs.
   
  Lemma DecOptwf_list_complete l :
    wf_list l -> 
    exists k, @decOpt _ (DecOptwf_list l) k = Some true.
  Proof.
  (*   intros H. induction H. *)
  (*   - exists 0. reflexivity. *)
  (*   - destruct IHwf_list as [k1 IH1]. *)
  (*     exists (S k1). *)
  (*     unfold decOpt, DecOptwf_list in *. *)
  (*     eapply checker_backtrack_spec. *)
  (*     eexists. *)
  (*     split. right. now left. *)
  (*     rewrite IH1.  reflexivity. *)
  (* Qed. *)
  Abort. 

  Lemma checker_backtrack_spec_exists (l : nat -> list (unit -> option bool))  :
    (exists (f : nat -> (unit -> option bool)),
        (forall s, List.In (f s) (l s)) /\ exists s, f s tt = Some true) ->
    exists s, checker_backtrack (l s) = Some true.                                                     
  Proof. Admitted.
  (*   unfold checker_backtrack. generalize false at 2. *)
  (*   induction l. *)
  (*   - intros b. destruct b; split; try (intros; congruence). *)
  (*     * intros H. inv H. inv H0. inv H. *)
  (*     * intros H. inv H. inv H0. inv H. *)
  (*   - intros b. split. *)
  (*     + intros H. *)
  (*       destruct (a tt) eqn:Hdec. *)
  (*       * destruct b0. exists a. split; eauto. now left. *)
  (*         eapply IHl in H. destruct H. inv H. *)
  (*         eexists; split; eauto. now right. *)
  (*       * eapply IHl in H. destruct H. inv H. *)
  (*         eexists; split; eauto. now right. *)
  (*     + intros H. inv H. inv H0. inv H. rewrite H1. reflexivity. *)
  (*       destruct (a tt). destruct b0. reflexivity. *)
  (*       * eapply IHl. eexists. split; eauto. *)
  (*       * eapply IHl. eexists. split; eauto. *)
  (* Qed. *)


  Lemma exists_Sn (P : nat -> Prop) : 
    (exists n, P (S n)) -> exists n, P n.
  Proof.
    intros [n H]. eexists; eauto.
  Qed.


  Transparent dec_decOpt.
  
  Lemma DecOptle_complete k m n :
    le m n -> @decOpt (le m n) _ k = Some true.
  Proof.
    unfold decOpt, dec_decOpt, dec.
    destruct (DecidableClass.Decidable_le_nat _ _). intros Hleq.
    simpl. destruct Decidable_witness; eauto.
    f_equal. eapply Decidable_spec. assumption. 
  Qed.

  Opaque dec_decOpt.

  Set Nested Proofs Allowed. 

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



  Lemma DecOptbst_complete m n t :
    bst m n t ->
    exists k, @decOpt _ (DecOptbst m n t) k = Some true.
  Proof.
    (* intros H. induction H. *)
    (* - exists 0. reflexivity. *)
    (* - revert min max H H0 H1 H2 H3 IHbst1 IHbst2; *)
    (*     intros m1 m2 H H0 H1 H2 H3 IHbst1 IHbst2. *)
    (*   eapply exists_Sn. *)
    (*   simpl. eapply checker_backtrack_spec_exists. *)
    (*   eexists. split. *)

    (*   intros s. right. left. reflexivity. simpl. *)

    (*   eapply DecOptle_complete with (k := 42) in H. *)
    (*   rewrite H.  *)
    (*   eapply DecOptle_complete with (k := 42) in H0. *)
    (*   rewrite H0.  *)
    (*   eapply DecOptle_complete with (k := 42) in H1. *)
    (*   rewrite H1.  *)
      
    (*   destruct IHbst1 as [s1' Hs1']. simpl in Hs1'.  *)
    (*   eapply exists_match. *)
    (*   + eassumption. *)
    (*   + intros s1 s2 Hleq. assert (Hm := @mon (bst m1 n t1) _ _ s1 s2 true Hleq). *)
    (*     simpl in Hm. eassumption. *)
    (*   + destruct IHbst2 as [s2' Hs2']. simpl in Hs2'.  *)
    (*     eapply exists_match with (s1 := s2'). *)
    (*     * assert (Hm := @mon (bst n m2 t2) _ _). *)
    (*       simpl in Hm. eapply Hm> [ | eassumption ]. lia. *)
    (*     * assert (Hm := @mon (bst n m2 t2) _ _). simpl in Hm.  *)
    (*       intros s1 s2 Hleq Heq. eapply Hm > [ | eassumption ]. lia. *)
    (*     * exists 0. reflexivity. *)
  Abort.

  
  Lemma DecOptbst_complete_false m n t :
    ~ bst m n t ->
    exists k, @decOpt _ (DecOptbst m n t) k = Some false.
  Proof.
  Abort.
  
(*
  Instance decOptbstCorrect m n t : DecOptCorrectPos (bst m n t).
  Proof.
    constructor.
    - intros. eapply DecOptbst_correct. eassumption.
    - intros. eapply DecOptbst_complete. eassumption.
  Qed.
 *)
  
End BSTProofs.
 
