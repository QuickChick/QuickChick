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

Section TypeClasses.
    
  Class DecOptSizeMonotonic (P : Prop) {H : DecOpt P} :=
    mon_true : forall s1 s2, s1 <= s2 -> decOpt s1 = Some true -> decOpt s2 = Some true.
    (* size_mon : forall s1 s2 b, s1 <= s2 -> decOpt s1 = Some b -> decOpt s2 = Some b. *)    
  
  Class DecOptDecidable (P : Prop) {H : DecOpt P} :=
    { wit : exists s a, decOpt s = Some a }.

  Class DecOptCorrectPos (P : Prop) {H : DecOpt P} :=
    { sound : forall s, decOpt s = Some true -> P; 
      complete : P -> exists s, decOpt s = Some true }.

  Class DecOptCorrectNeg (P : Prop) {H : DecOpt P} :=
    { sound' : forall s, decOpt s = Some false -> ~ P; 
      complete' :~ P -> exists s, decOpt s = Some false }.

  (* Not true: *) 
  (* Class DecOptCorrect (P : Prop) {H : DecOpt P} := *)
  (*   { refl_decOpt : forall s, ssrbool.reflect P (decOpt s == Some true) }. *)

  
  (* Coersions from [Dec] *)
  
  Global Instance decSizeMonotonic (P : Prop) {_ : Dec P} : DecOptSizeMonotonic P.
  Proof.
    intro; intros. eapply H1.
    (* firstorder. (* unbound value?? *) *)
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

  (* Global Instance decOptCorrectNeg (P : Prop) {H : DecOpt P} *)
  (*        {Hmon : DecOptSizeMonotonic P}  *)
  (*        {Hdec : DecOptDecidable P} *)
  (*        {Hcor : DecOptCorrectPos P} : DecOptCorrectNeg P. *)
  (* Proof. *)
  (*   constructor.  *)
  (*   - intros s Hopt. intros HP. eapply Hcor in HP. *)
  (*     destruct HP. *)
  (*     edestruct (Compare_dec.le_lt_dec s x). *)
  (*     + eapply Hmon in Hopt; eauto. congruence. *)
  (*     + eapply Hmon in H0. *)
  (*       2:{ eapply PeanoNat.Nat.lt_le_incl. eassumption. } congruence. *)
  (*   - intros Hn. *)
  (*     destruct Hdec. destruct wit0 as [s [a Hopt]]. *)
  (*     destruct a; eauto. *)
  (*     eapply Hcor in Hopt. contradiction.  *)
  (* Qed. *)


  Inductive wf_list : list nat -> Prop :=
  | lnil : wf_list nil
  | lcons :
      forall l,
        wf_list l -> wf_list l.

  Derive DecOpt for (wf_list l).  

  
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


(* Tactics for deriving monotonicity. TODO move to some library *)
Ltac2 constr_to_ident (a : Init.constr) :=
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.Var i => i
  | _ => Control.throw (Tactic_failure (Some (Message.of_string ("constr is not a var"))))
  end.

Ltac2 constrs_to_idents (a : Init.constr list) := List.map constr_to_ident a.

Opaque dec_decOpt.

Ltac2 eassumption_ltac2 () := ltac1:(eassumption).
Ltac2 Notation "eassumption" := eassumption_ltac2 ().

Ltac2 rec base_case_mon_aux (t : unit) (path : unit -> unit) :=
  match! goal with
  | [h : List.In _ nil |- _ ] => let h := Control.hyp h in destruct $h
  | [h : List.In _ (cons ?g nil) |- _ ] =>
    let h := Control.hyp h in destruct $h > [ subst; congruence | base_case_mon_aux () path ]
  | [h : List.In _ (cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    try (destruct $h > [ eexists; split > [ path () ; left ; eassumption | eassumption ]
                       | ]);
base_case_mon_aux () (fun _ => path; right)
end.

(* TODO check if it works with reversed order of constructors *)

Ltac2 base_case_mon (t : unit) := base_case_mon_aux () (fun _ => ()).

From Ltac2 Require Import Fresh.

Ltac2 handle_ind_checker (ih : ident) (heq : ident) := 
  first
    [ let heq1 := Fresh.in_goal heq in
      let heq' := Control.hyp heq in
      (* because apply .... in $heq doesn't work *)
      assert ($heq1 := destruct_match_true_l _ _ $heq'); clear $heq;
    let heq1 := Control.hyp heq1 in
    let ih := Control.hyp ih in
    (* XXX fresh names in as [ ... ] *)     
    destruct $heq1 as [Hdeq Heq]; try (eapply $ih in Hdeq > [ | now eapply le_S_n; eauto ]);
    rewrite &Hdeq; clear Hdeq 
    | match! goal with
      | [h : match ?m with _ => _  end = Some true |- _ ] =>
        destruct $m; try (congruence)
      end
    | reflexivity ].



Ltac2 rec ind_case_mon_aux (t : unit) (path : unit -> unit) :=
  match! goal with
  | [h : List.In _ nil |- _ ] => let h := Control.hyp h in destruct $h
  | [h : List.In _ (cons ?g ?gs) |- _ ] =>
    let h := Control.hyp h in
    destruct $h > [ eexists; try (split > [ path () ; left ; eassumption | eassumption ]) (* succeds for base cases *); 
                  split > [ path () ; left ; reflexivity | ] (* leaves one goal for each inductive case *)
                  | ind_case_mon_aux () (fun _ => path; right) ]
                    
                    
  end.

Ltac2 ind_case_mon (ih : ident) (heq : ident) :=
  (ind_case_mon_aux () (fun _ => ()));
subst; repeat (handle_ind_checker @IH1 @Heq).

Ltac2 id_of_string (s : string) :=
  match Ident.of_string s with
  | Some i => i
  | None => Control.throw (Tactic_failure (Some (Message.of_string ("Not a valid string for identifier"))))
  end.

Ltac2 derive_mon (_ : unit) :=
  match! goal with
  | [ |- DecOptSizeMonotonic ?e ] =>
    match Constr.Unsafe.kind e with
    | Constr.Unsafe.App ty args  =>
      let l := constrs_to_idents (Array.to_list args) in
      intro s1;          
      List.map (fun x => revert $x) l;
      (induction s1 as [ | s1 IH1 ]; (List.map (fun x => intro $x) l; intros s2 Hleq Hdec);
      (* for each case destruct the second size. Zero cases are trivial *)
      destruct s2) > [ assumption | | lia | ];
      (* simplify and apply checker_backtrack_spec *)
      simpl in *; apply checker_backtrack_spec in Hdec;
      (* XXX fresh? *)
      destruct Hdec as [f [Hin Heq]];
      apply checker_backtrack_spec
    | _ => () 
    end
 end > [ now base_case_mon () | ind_case_mon @IH1 @Heq ].    

(* TODO remove warnings. *)


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
      list_len (S n) (x :: l). 

Derive DecOpt for (list_len n l).

Instance DecOptlist_lenSizeMonotonic n l : DecOptSizeMonotonic (list_len n l).
Proof. derive_mon (). Qed. 

Section BSTProofs.

   
  Lemma DecOptwf_list_correct k l :
    @decOpt _ (DecOptwf_list l) k = Some true ->
    wf_list l.
  Proof.
    revert l. induction k; intros l Hdec.
    + destruct l. now constructor.
      inversion Hdec.
    + unfold decOpt, DecOptwf_list in *.
      eapply checker_backtrack_spec in Hdec.
      destruct Hdec as [f [Hin Htrue]]. destruct Hin; subst.
      * destruct l. now constructor. congruence.
      * destruct H; subst.
        eapply IHk.
        match!goal with
        | [ |- (?e = _) ] => destruct $e
        end.
        destruct b; eauto. congruence.
        inv H. 
  Qed.


  Lemma DecOptwf_list_complete l :
    wf_list l -> 
    exists k, @decOpt _ (DecOptwf_list l) k = Some true.
  Proof.
    intros H. induction H.
    - exists 0. reflexivity.
    - destruct IHwf_list as [k1 IH1].
      exists (S k1).
      unfold decOpt, DecOptwf_list in *.
      eapply checker_backtrack_spec.
      eexists.
      split. right. now left.
      rewrite IH1.  reflexivity.
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

  Lemma DecOptbst_monotonic :
    forall k1 k2 m n t,
      k1 <= k2 ->
      @decOpt _ (DecOptbst m n t) k1 = Some true ->
      @decOpt _ (DecOptbst m n t) k2 = Some true.
  Proof.
  Abort. 
        
 (*        destruct Hdec as [f [[H1 | [ H2 | [] ]] H3]]. *)
 (*        +         Show Proof.  *)
 (* destruct t; subst; try congruence. *)
 (*          subst. eapply checker_backtrack_spec. *)
 (*          eexists. split. now left. reflexivity. *)

 (*        + subst. destruct t; try congruence. *)
           
 (*          eapply checker_backtrack_spec. *)
 (*          eexists. split. right. now left. *)
          
          
 (*          destruct (@decOpt (m <= n0) _ 42) eqn:Hdle'; [ | congruence ]. *)
 (*          destruct b; [ | congruence ]. *)

 (*          destruct (@decOpt (n0 <= n) _ 42) eqn:Hdle''; [ | congruence ]. *)
 (*          destruct b; [ | congruence ]. *)

 (*          match goal with *)
 (*          | [ H : (match ?e with _ => _ end = Some true) |- _ ] => *)
 (*            destruct e eqn:Heqb *)
 (*          end; [ | congruence ]. *)
 (*          destruct b; [ | congruence ].  *)
 (*          match goal with *)
 (*          | [ H : (match ?e with _ => _ end = Some true) |- _ ] => *)
 (*            destruct e eqn:Heqb' *)
 (*          end; [ | congruence ]. *)
 (*          destruct b; [ | congruence ]. *)
 (*          rewrite (IHk1 true). rewrite (IHk1 true). *)
 (*          reflexivity. lia. eassumption. lia. eassumption. } *)


 (*      { (* b = false *) *)
 (*        unfold decOpt, DecOptbst in *. *)
 (*        assert (Hf := proj1 (checker_backtrack_spec_false _) Hdec).  *)
 (*        eapply checker_backtrack_spec_false. *)
 (*        intros f Hin. destruct Hin. *)
 (*        - subst; destruct t; eauto. *)
 (*        - destruct H; eauto. 2:{ now inv H. } subst. *)
 (*          destruct t. reflexivity. *)
          
 (*          destruct (@decOpt (m <= n) _ 42) eqn:Hdle. *)
 (*          2:{ assert (Hc : (fun (_ : unit) => @None bool) tt = Some false). *)
 (*              { eapply Hf with (f := (fun (_ : unit) => @None bool)). *)
 (*                right. left. reflexivity. } *)
 (*              congruence. }   *)

 (*          destruct b; [ | congruence ]. *)
          
 (*          destruct (@decOpt (m <= n0) _ 42) eqn:Hdle'. *)
 (*          2:{ assert (Hc : (fun (_ : unit) => @None bool) tt = Some false). *)
 (*              { eapply Hf with (f := (fun (_ : unit) => @None bool)). *)
 (*                right. left. reflexivity. } *)
 (*              congruence. }   *)

 (*          destruct b; [ | congruence ]. *)

 (*          destruct (@decOpt (n0 <= n) _ 42) eqn:Hdle''. *)
 (*          2:{ assert (Hc : (fun (_ : unit) => @None bool) tt = Some false). *)
 (*              { eapply Hf with (f := (fun (_ : unit) => @None bool)). *)
 (*                right. left. reflexivity. } *)
 (*              congruence. }   *)
          
 (*          destruct b; [ | congruence ]. *)
          
 (*          match goal with  *)
 (*          | [ |- match ?g ?k ?m ?n ?t with _ => _ end = Some false ] => set (ch := g) *)
 (*          end. *)

 (*          destruct (ch k1 m n0 t1) as [ b1 | ] eqn:Heq1. *)

 (*          2:{ unfold ch in *. rewrite Heq1 in Hf.  *)
 (*              assert (Hc : (fun (_ : unit) => @None bool) tt = Some false). *)
 (*              { eapply Hf with (f := (fun (_ : unit) => @None bool)). *)
 (*                right. left. reflexivity. } *)
 (*              congruence. } *)
            
 (*          assert (Heq2 := Heq1). *)
 (*          eapply IHk1 with (k2 := k2) in Heq2; [ | lia ]. *)
          
 (*          unfold ch in Heq1. rewrite Heq1 in Hf. *)

 (*          unfold ch. rewrite Heq2.   *)
 (*          destruct b1. 2:{ reflexivity. }  *)
          
 (*          destruct (ch k1 n0 n t2) as [ b2 | ] eqn:Heq1'. *)
          
 (*          2:{ unfold ch in *. rewrite Heq1' in Hf.  *)
 (*              assert (Hc : (fun (_ : unit) => @None bool) tt = Some false). *)
 (*              { eapply Hf with (f := (fun (_ : unit) => @None bool)). *)
 (*                right. left. reflexivity. } *)
 (*              congruence. } *)


 (*          assert (Heq2' := Heq1'). *)
 (*          eapply IHk1 with (k2 := k2) in Heq2'; [ | lia ]. *)

 (*          unfold ch in Heq1'. rewrite Heq1' in Hf. *)
          
 (*          rewrite Heq2'. *)

 (*          destruct b2; [| reflexivity ]. *)

          
 (*          eapply Hf with (f := (fun _ : unit => if b2 then Some true else Some false)). *)
 (*          right. left. reflexivity. } *)
          
 (*  Qed. *)

(* 
  
  Instance decOptbstSizeMonotonic m n t : DecOptSizeMonotonic (bst m n t).
  Proof. intro; intros. eapply DecOptbst_monotonic; eauto. Qed.

  
  Lemma DecOptbst_correct k m n t :
    @decOpt _ (DecOptbst m n t) k = Some true ->
    bst m n t.
  Proof.
    revert m n t. induction k; intros m n t Hdec.
    + destruct t. now constructor.
      inversion Hdec.
    + unfold decOpt, DecOptbst in *.
      eapply checker_backtrack_spec in Hdec.
      destruct Hdec as [f [Hin Htrue]]. destruct Hin; subst.
      * destruct t. now constructor. congruence.
      * destruct H; subst; [ | contradiction ]. 
        destruct t. congruence.      

        destruct (@decOpt (m <= n) _ 42) eqn:Hdle; [ | congruence ].
        destruct b; [ | congruence ].
        
        destruct (@decOpt (m <= n0) _ 42) eqn:Hdle'; [ | congruence ].
        destruct b; [ | congruence ].

        destruct (@decOpt (n0 <= n) _ 42) eqn:Hdle''; [ | congruence ].
        destruct b; [ | congruence ].
        
        eapply sound in Hdle.
        eapply sound in Hdle'.
        eapply sound in Hdle''.

        match goal with
        | [ H : (match ?e with _ => _ end = Some true) |- _ ] =>
          remember e as x
        end.
        destruct x eqn:Hdec; [ | congruence ].
        destruct b; [ | congruence ].

        constructor. eassumption. eassumption. eassumption.
        
        now eapply IHk; eauto.

        match goal with
        | [ H : (match ?e with _ => _ end = Some true) |- _ ] =>
          remember e as y
        end.
        destruct y eqn:Hdec'; [ | congruence ].
        destruct b; [ | congruence ].
        now eapply IHk; eauto.
  Qed.

  Lemma DecOptbst_complete m n t :
    bst m n t ->
    exists k, @decOpt _ (DecOptbst m n t) k = Some true.
  Proof.
    intros H. induction H.
    - exists 0. reflexivity.
    - destruct IHbst1 as [k1 IH1].
      destruct IHbst2 as [k2 IH2].    
      exists (S (Nat.max k1 k2)).
      unfold decOpt, DecOptbst.
      eapply checker_backtrack_spec.
      eexists.
      split. right. now left.
      
      erewrite !DecOptle_complete; eauto.
      
      assert (Hmax1 : @decOpt (bst min n t1) _ (Nat.max k1 k2) = Some true).
      { eapply DecOptbst_monotonic; [ | eassumption ]. lia. }

      assert (Hmax2 : @decOpt (bst n max t2) _ (Nat.max k1 k2) = Some true).
      { eapply DecOptbst_monotonic; [ | eassumption ]. lia. }

      unfold decOpt, DecOptbst in Hmax1, Hmax2. 
      rewrite Hmax1 Hmax2.

      reflexivity.
  Qed.

  Instance decOptbstCorrect m n t : DecOptCorrectPos (bst m n t).
  Proof.
    constructor.
    - intros. eapply DecOptbst_correct. eassumption.
    - intros. eapply DecOptbst_complete. eassumption.
  Qed.
  


  Lemma DecOptbst_correct_false k m n t :
    @decOpt _ (DecOptbst m n t) k = Some false ->
    ~ bst m n t.
  Proof.
    intros Hdec Hbst.
    eapply DecOptbst_complete in Hbst.
    destruct Hbst as [k' Hbst].
    edestruct (Compare_dec.le_lt_dec k k').

    + eapply decOptbstSizeMonotonic in Hdec; [ | eassumption ].
      congruence.

    + eapply decOptbstSizeMonotonic in Hbst; [ | eapply PeanoNat.Nat.lt_le_incl; eassumption ].
      congruence.
  Qed.

  Lemma DecOptbst_complete_false m n t :
    ~ bst m n t ->
    exists k, @decOpt _ (DecOptbst m n t) k = Some false.
  Proof.
    revert m n; induction t; intros m1 n2 Hbst.
    - exfalso. eapply Hbst. constructor.
    - 

    intros H. revert m n. 
    assert (Hnot : ~ forall k, ~ @decOpt _ (DecOptbst m n t) k = Some false).
    { intros Hnot. eapply H.
      

      admit. }

    
    exfalso. eapply Hnot.
    intros k Hfalse. eapply DecOptbst_correct_false in Hfalse. 
    eapply DecOptbst_sound.

              induction H.
    - exists 0. reflexivity.
    - destruct IHbst1 as [k1 IH1].
      destruct IHbst2 as [k2 IH2].    
      exists (S (Nat.max k1 k2)).
      unfold decOpt, DecOptbst.
      eapply checker_backtrack_spec.
      eexists.
      split. right. now left.
      
      erewrite !DecOptle_complete; eauto.
      
      assert (Hmax1 : @decOpt (bst min n t1) _ (Nat.max k1 k2) = Some true).
      { eapply DecOptbst_monotonic; [ | eassumption ]. lia. }

      assert (Hmax2 : @decOpt (bst n max t2) _ (Nat.max k1 k2) = Some true).
      { eapply DecOptbst_monotonic; [ | eassumption ]. lia. }

      unfold decOpt, DecOptbst in Hmax1, Hmax2. 
      rewrite Hmax1 Hmax2.

      reflexivity.
  Qed.

  Instance decOptbstCorrect m n t : DecOptCorrectPos (bst m n t).
  Proof.
    constructor.
    - intros. eapply DecOptbst_correct. eassumption.
    - intros. eapply DecOptbst_complete. eassumption.
  Qed.
 *)
  
End BSTProofs.
 
