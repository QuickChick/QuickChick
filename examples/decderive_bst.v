From Coq Require Import Init.Nat Lia.
From QuickChick Require Import QuickChick.
From mathcomp Require Import ssreflect ssreflect.eqtype.
Import QcNotation. Import QcDefaultNotation.
Require Import ExtLib.Structures.Monads.
Open Scope monad_scope.
Open Scope qc_scope.
Open Scope nat_scope.

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


Compute (sample (@arbitrarySizeST _ (fun t => bst 0 30 t) _ 10)).


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


Section TypeClasses.
    
  Class DecOptSizeMonotonic (P : Prop) {H : DecOpt P} :=
    size_mon : forall s1 s2 b, s1 <= s2 -> decOpt s1 = Some b -> decOpt s2 = Some b.
  
  
  
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
  Proof. firstorder. Qed.

  
  Global Instance decCorrectPos (P : Prop) {_ : Dec P} : DecOptCorrectPos P.
  Proof.
    constructor. 
    - intros s.
      unfold decOpt, dec_decOpt, Decidability.dec. destruct H.
      destruct dec. now firstorder. congruence.
    - intros s.
      unfold decOpt, dec_decOpt, Decidability.dec. destruct H.
      exists 0. 
      destruct dec. now firstorder. congruence.
  Qed.

  Global Instance decCorrectNeg (P : Prop) {_ : Dec P} : DecOptCorrectNeg P.
  Proof.
    constructor. 
    - intros s.
      unfold decOpt, dec_decOpt, dec. destruct H.
      destruct dec. now firstorder. congruence.
    - intros s.
      unfold decOpt, dec_decOpt, dec. destruct H.
      exists 0. 
      destruct dec. now firstorder. congruence.
  Qed.

  Global Instance decOptCorrectNeg (P : Prop) {H : DecOpt P}
         {Hmon : DecOptSizeMonotonic P} 
         {Hdec : DecOptDecidable P}
         {Hcor : DecOptCorrectPos P} : DecOptCorrectNeg P.
  Proof.
    constructor. 
    - intros s Hopt. intros HP. eapply Hcor in HP.
      destruct HP.
      edestruct (Compare_dec.le_lt_dec s x).
      + eapply Hmon in Hopt; eauto. congruence.
      + eapply Hmon in H0.
        2:{ eapply PeanoNat.Nat.lt_le_incl. eassumption. } congruence.
    - intros Hn.
      destruct Hdec. destruct wit0 as [s [a Hopt]].
      destruct a; eauto.
      eapply Hcor in Hopt. contradiction. 
  Qed.


  Inductive wf_list : list nat -> Prop :=
  | lnil : wf_list nil
  | lcons :
      forall l,
        wf_list l -> wf_list l.

  Derive DecOpt for (wf_list l).  

  
End TypeClasses.


Section BSTProofs.

  Ltac inv H := inversion H; subst.

  Lemma checker_backtrack_spec l :
    checker_backtrack l = Some true <->
    exists f, List.In f l /\ f tt = Some true.
  Proof.
    unfold checker_backtrack. generalize false at 2.
    induction l.
    - intros b. destruct b; split; try (intros; congruence).
      * intros H. inv H. inv H0. inv H1.
      * intros H. inv H. inv H0. inv H1.
    - intros b. split.
      + intros H.
        destruct (a tt) eqn:Hdec.
        * destruct b0. exists a. split; eauto. now left.
          eapply IHl in H. destruct H. inv H.
          eexists; split; eauto. now right.
        * eapply IHl in H. destruct H. inv H.
          eexists; split; eauto. now right.
      + intros H. inv H. inv H0. inv H1. rewrite H2. reflexivity.
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
        -- split; try congruence.
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
           exfalso. 
           revert H1. clear. intros H1; induction l.
           congruence.
           destruct (a tt).
           ++ destruct b. congruence. eauto.
           ++ eauto.
        -- intros Hall. 
           assert (Hc : a tt = Some false).
           { eapply Hall. now left. } congruence.
  Qed.


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
      * destruct H; subst; [ | contradiction ]. 
        eapply IHk.
        match goal with
        | [ |- ?e = _ ] => destruct e
        end.
        destruct b; eauto. congruence.
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
  

  Lemma DecOptle_complete k m n :
    le m n -> @decOpt (le m n) _ k = Some true.
  Proof.
    unfold decOpt, dec_decOpt, dec.
    destruct DecidableClass.Decidable_le_nat. intros Hleq.
    simpl. destruct Decidable_witness; firstorder.
    congruence.
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

  Lemma DecOptbst_monotonic :
    forall k1 k2 m n t,
      k1 <= k2 ->
      @decOpt _ (DecOptbst m n t) k1 = Some true ->
      @decOpt _ (DecOptbst m n t) k2 = Some true.
  Proof.
    refine (fun k1 : nat =>
              nat_ind
                (fun k2 : nat =>
                   forall (k3 m n : nat) (t : tree),
                     k2 <= k3 -> decOpt k2 = Some true -> decOpt k3 = Some true) 
                (fun k2 m n t Hleq Hdec =>
                   match k2 with
                   | 0 => Hdec
                   | S k2 => _
                   end)
                (fun (k2 : nat)
                     (IHk1 : forall (k3 m n : nat) (t : tree),
                         k2 <= k3 -> decOpt k2 = Some true -> decOpt k3 = Some true) k2 m n t Hleq Hdec =>
                   match k2 with
                   | 0 => fun Hleq => False_ind _ (PeanoNat.Nat.nle_succ_0 _ Hleq)
                   | S k2 => fun Hleq => _
                   end Hleq
                ) k1).
    -
 
      refine (let ls := ((fun _ : unit =>
                           match t with
                           | Leaf => Some true
                           | Node _ _ _ => Some false
                           end)
                          :: (fun _ : unit =>
                                match t with
                                | Leaf => Some false
                                | Node n0 t1 t2 =>
                                  match decOpt 42 with
                                  | Some true =>
                                    match decOpt 42 with
                                    | Some true =>
                                      match decOpt 42 with
                                      | Some true =>
                                        match
                                          (fix aux_arb
                                               (size0 min_ max_ : nat) (t_ : tree) {struct size0} :
                                             option bool :=
                                             match size0 with
                                             | 0 =>
                                               checker_backtrack
                                                 ((fun _ : unit =>
                                                     match t_ with
                                                     | Leaf => Some true
                                                     | Node _ _ _ => Some false
                                                     end) :: (fun _ : unit => None) :: nil)
                                             | S size' =>
                                               checker_backtrack
                                                 ((fun _ : unit =>
                                                     match t_ with
                                                     | Leaf => Some true
                                                     | Node _ _ _ => Some false
                                                     end)
                                                    :: (fun _ : unit =>
                                                          match t_ with
                                                          | Leaf => Some false
                                                          | Node n t3 t4 =>
                                                            match decOpt 42 with
                                                            | Some true =>
                                                              match decOpt 42 with
                                                              | Some true =>
                                                                match decOpt 42 with
                                                                | Some true =>
                                                                  match
                                                                    aux_arb size' min_ n t3
                                                                  with
                                                                  | Some true =>
                                                                    match
                                                                      aux_arb size' n max_ t4
                                                                    with
                                                                    | Some true => Some true
                                                                    | Some false => Some false
                                                                    | None => None
                                                                    end
                                                                  | Some false => Some false
                                                                  | None => None
                                                                  end
                                                                | Some false => Some false
                                                                | None => None
                                                                end
                                                              | Some false => Some false
                                                              | None => None
                                                              end
                                                            | Some false => Some false
                                                            | None => None
                                                            end
                                                          end) :: nil)
                                             end) k2 m n0 t1
                                        with
                                        | Some true =>
                                          match
                                            (fix aux_arb
                                                 (size0 min_ max_ : nat) 
                                                 (t_ : tree) {struct size0} : 
                                               option bool :=
                                               match size0 with
                                               | 0 =>
                                                 checker_backtrack
                                                   ((fun _ : unit =>
                                                       match t_ with
                                                       | Leaf => Some true
                                                       | Node _ _ _ => Some false
                                                       end) :: (fun _ : unit => None) :: nil)
                                               | S size' =>
                                                 checker_backtrack
                                                   ((fun _ : unit =>
                                                       match t_ with
                                                       | Leaf => Some true
                                                       | Node _ _ _ => Some false
                                                       end)
                                                      :: (fun _ : unit =>
                                                            match t_ with
                                                            | Leaf => Some false
                                                            | Node n t3 t4 =>
                                                              match decOpt 42 with
                                                              | Some true =>
                                                                match decOpt 42 with
                                                                | Some true =>
                                                                  match decOpt 42 with
                                                                  | Some true =>
                                                                    match
                                                                      aux_arb size' min_ n t3
                                                                    with
                                                                    | Some true =>
                                                                      match
                                                                        aux_arb size' n max_ t4
                                                                      with
                                                                      | Some true => Some true
                                                                      | Some false => Some false
                                                                      | None => None
                                                                      end
                                                                    | Some false => Some false
                                                                    | None => None
                                                                    end
                                                                  | Some false => Some false
                                                                  | None => None
                                                                  end
                                                                | Some false => Some false
                                                                | None => None
                                                                end
                                                              | Some false => Some false
                                                              | None => None
                                                              end
                                                            end) :: nil)
                                               end) k2 n0 n t2
                                          with
                                          | Some true => Some true
                                          | Some false => Some false
                                          | None => None
                                          end
                                        | Some false => Some false
                                        | None => None
                                        end
                                      | Some false => Some false
                                      | None => None
                                      end
                                    | Some false => Some false
                                    | None => None
                                    end
                                  | Some false => Some false
                                  | None => None
                                  end
                                end) :: nil)%list in
             match
               proj1
                 (checker_backtrack_spec
                    ((fun _ : unit =>
                        match t with
                        | Leaf => Some true
                        | Node _ _ _ => Some false
                        end) :: (fun _ : unit => None) :: nil)) Hdec
             with
             | ex_intro _ f (conj Hin Heq) =>
               proj2 (checker_backtrack_spec ls)
                     match Hin with
                     | or_introl Hin1 =>
                       (* (* let Hin':= eq_ind_r (fun f0 => f0 tt = Some true) *) *)
                       (* (*                     Heq Hin1 in *) *)
                       
                       ex_intro _ _
                       (conj (or_introl Hin1) Heq)
                     | or_intror (or_introl Hin1) =>
                       let Hin':= eq_ind_r (fun f0 => f0 tt = Some true)
                                           Heq Hin1 in
                       (* (False_ind _ (match Hin' with Logic.eq_refl => I end)) *)
                     | or_intror (or_intror Hin1) =>
                       False_ind _ Hin1
                     end
             end).
    - refine (match k2 with
              | 0 => fun Hleq => False_ind _ (PeanoNat.Nat.nle_succ_0 _ Hleq)
              | S k2 => fun Hleq => _
              end Hleq).
             
      unfold decOpt, DecOptbst in *.
      
      Set Printing Depth 100.
      
      refine (let ls1 := (((fun _ : unit =>
                              match t with
                              | Leaf => Some true
                              | Node _ _ _ => Some false
                              end)
                             :: (fun _ : unit =>
                                   match t with
                                   | Leaf => Some false
                                   | Node n0 t1 t2 =>
                                     match decOpt 42 with
                                     | Some true =>
                                       match decOpt 42 with
                                       | Some true =>
                                         match decOpt 42 with
                                         | Some true =>
                                           match
                                             (fix aux_arb
                                                  (size0 min_ max_ : nat) 
                                                  (t_ : tree) {struct size0} : 
                                                option bool :=
                                                match size0 with
                                                | 0 =>
                                                  checker_backtrack
                                                    ((fun _ : unit =>
                                                        match t_ with
                                                        | Leaf => Some true
                                                        | Node _ _ _ => Some false
                                                        end) :: (fun _ : unit => None) :: nil)
                                                | S size' =>
                                                  checker_backtrack
                                                    ((fun _ : unit =>
                                                        match t_ with
                                                        | Leaf => Some true
                                                        | Node _ _ _ => Some false
                                                        end)
                                                       :: (fun _ : unit =>
                                                             match t_ with
                                                             | Leaf => Some false
                                                             | Node n t3 t4 =>
                                                               match decOpt 42 with
                                                               | Some true =>
                                                                 match decOpt 42 with
                                                                 | Some true =>
                                                                   match decOpt 42 with
                                                                   | Some true =>
                                                                     match
                                                                       aux_arb size' min_ n t3
                                                                     with
                                                                     | Some true =>
                                                                       match
                                                                         aux_arb size' n max_ t4
                                                                       with
                                                                       | Some true => Some true
                                                                       | Some false => Some false
                                                                       | None => None
                                                                       end
                                                                     | Some false => Some false
                                                                     | None => None
                                                                     end
                                                                   | Some false => Some false
                                                                   | None => None
                                                                   end
                                                                 | Some false => Some false
                                                                 | None => None
                                                                 end
                                                               | Some false => Some false
                                                               | None => None
                                                               end
                                                             end) :: nil)
                                                end) k3 m n0 t1
                                           with
                                           | Some true =>
                                             match
                                               (fix aux_arb
                                                    (size0 min_ max_ : nat) 
                                                    (t_ : tree) {struct size0} :
                                                  option bool :=
                                                  match size0 with
                                                  | 0 =>
                                                    checker_backtrack
                                                      ((fun _ : unit =>
                                                          match t_ with
                                                          | Leaf => Some true
                                                          | Node _ _ _ => Some false
                                                          end)
                                                         :: (fun _ : unit => None) :: nil)
                                                  | S size' =>
                                                    checker_backtrack
                                                      ((fun _ : unit =>
                                                          match t_ with
                                                          | Leaf => Some true
                                                          | Node _ _ _ => Some false
                                                          end)
                                                         :: (fun _ : unit =>
                                                               match t_ with
                                                               | Leaf => Some false
                                                               | Node n t3 t4 =>
                                                                 match decOpt 42 with
                                                                 | Some true =>
                                                                   match decOpt 42 with
                                                                   | Some true =>
                                                                     match decOpt 42 with
                                                                     | Some true =>
                                                                       match
                                                                         aux_arb size' min_ n t3
                                                                       with
                                                                       | Some true =>
                                                                         match
                                                                           aux_arb size' n max_ t4
                                                                         with
                                                                         | Some true => Some true
                                                                         | Some false => Some false
                                                                         | None => None
                                                                         end
                                                                       | Some false => Some false
                                                                       | None => None
                                                                       end
                                                                     | Some false => Some false
                                                                     | None => None
                                                                     end
                                                                   | Some false => Some false
                                                                   | None => None
                                                                   end
                                                                 | Some false => Some false
                                                                 | None => None
                                                                 end
                                                               end) :: nil)
                                                  end) k3 n0 n t2
                                             with
                                             | Some true => Some true
                                             | Some false => Some false
                                             | None => None
                                             end
                                           | Some false => Some false
                                           | None => None
                                           end
                                         | Some false => Some false
                                         | None => None
                                         end
                                       | Some false => Some false
                                       | None => None
                                       end
                                     | Some false => Some false
                                     | None => None
                                     end
                                   end) :: nil)%list) in
              let ls2 := ((fun _ : unit =>
                             match t with
                             | Leaf => Some true
                             | Node _ _ _ => Some false
                             end)
                            :: (fun _ : unit =>
                                  match t with
                                  | Leaf => Some false
                                  | Node n0 t1 t2 =>
                                    match decOpt 42 with
                                    | Some true =>
                                      match decOpt 42 with
                                      | Some true =>
                                        match decOpt 42 with
                                        | Some true =>
                                          match
                                            (fix aux_arb
                                                 (size0 min_ max_ : nat) (t_ : tree) {struct size0} :
                                               option bool :=
                                               match size0 with
                                               | 0 =>
                                                 checker_backtrack
                                                   ((fun _ : unit =>
                                                       match t_ with
                                                       | Leaf => Some true
                                                       | Node _ _ _ => Some false
                                                       end) :: (fun _ : unit => None) :: nil)
                                               | S size' =>
                                                 checker_backtrack
                                                   ((fun _ : unit =>
                                                       match t_ with
                                                       | Leaf => Some true
                                                       | Node _ _ _ => Some false
                                                       end)
                                                      :: (fun _ : unit =>
                                                            match t_ with
                                                            | Leaf => Some false
                                                            | Node n1 t0 t3 =>
                                                              match decOpt 42 with
                                                              | Some true =>
                                                                match decOpt 42 with
                                                                | Some true =>
                                                                  match decOpt 42 with
                                                                  | Some true =>
                                                                    match
                                                                      aux_arb size' min_ n1 t0
                                                                    with
                                                                    | Some true =>
                                                                      match
                                                                        aux_arb size' n1 max_ t3
                                                                      with
                                                                      | Some true => Some true
                                                                      | Some false => Some false
                                                                      | None => None
                                                                      end
                                                                    | Some false => Some false
                                                                    | None => None
                                                                    end
                                                                  | Some false => Some false
                                                                  | None => None
                                                                  end
                                                                | Some false => Some false
                                                                | None => None
                                                                end
                                                              | Some false => Some false
                                                              | None => None
                                                              end
                                                            end) :: nil)
                                               end) k2 m n0 t1
                                          with
                                          | Some true =>
                                            match
                                              (fix aux_arb
                                                   (size0 min_ max_ : nat) 
                                                   (t_ : tree) {struct size0} : 
                                                 option bool :=
                                                 match size0 with
                                                 | 0 =>
                                                   checker_backtrack
                                                     ((fun _ : unit =>
                                                         match t_ with
                                                         | Leaf => Some true
                                                         | Node _ _ _ => Some false
                                                         end) :: (fun _ : unit => None) :: nil)
                                                 | S size' =>
                                                   checker_backtrack
                                                     ((fun _ : unit =>
                                                         match t_ with
                                                         | Leaf => Some true
                                                         | Node _ _ _ => Some false
                                                         end)
                                                        :: (fun _ : unit =>
                                                              match t_ with
                                                              | Leaf => Some false
                                                              | Node n1 t0 t3 =>
                                                                match decOpt 42 with
                                                                | Some true =>
                                                                  match decOpt 42 with
                                                                  | Some true =>
                                                                    match decOpt 42 with
                                                                    | Some true =>
                                                                      match
                                                                        aux_arb size' min_ n1 t0
                                                                      with
                                                                      | Some true =>
                                                                        match
                                                                          aux_arb size' n1 max_ t3
                                                                        with
                                                                        | Some true => Some true
                                                                        | Some false => Some false
                                                                        | None => None
                                                                        end
                                                                      | Some false => Some false
                                                                      | None => None
                                                                      end
                                                                    | Some false => Some false
                                                                    | None => None
                                                                    end
                                                                  | Some false => Some false
                                                                  | None => None
                                                                  end
                                                                | Some false => Some false
                                                                | None => None
                                                                end
                                                              end) :: nil)
                                                 end) k2 n0 n t2
                                            with
                                            | Some true => Some true
                                            | Some false => Some false
                                            | None => None
                                            end
                                          | Some false => Some false
                                          | None => None
                                          end
                                        | Some false => Some false
                                        | None => None
                                        end
                                      | Some false => Some false
                                      | None => None
                                      end
                                    | Some false => Some false
                                    | None => None
                                    end
                                  end) :: nil)%list in
              match
                proj1
                  (checker_backtrack_spec ls1) Hdec
              with
              | ex_intro _ f (conj Hin Heq) =>
                
                proj2 (checker_backtrack_spec ls2) _
              end).


      unfold ls1, ls2 in *. clear ls1 ls2. 
      refine (match Hin with
              | or_introl Hin =>
                ex_intro _ f (conj (or_introl Hin) Heq)
              | or_intror Hin =>
                match Hin with
                | or_introl Hin =>
                  let Hin':= eq_ind_r (fun f0 : unit -> option bool => f0 tt = Some true)
                                      Heq Hin in _

                | or_intror Hfalse => False_ind _ Hfalse
                end
              end).
      refine (ex_intro _ _ (conj (or_intror (or_introl Logic.eq_refl)) _)).
      refine (match t with
              | Leaf => fun Hin' => _
              | Node n0 t1 t2 => fun Hin' => _
              end Hin').
      exact (False_ind _ (match Hin' with Logic.eq_refl => I end)).

      refine (match destruct_match_true_l _ _ Hin' with
              | conj Heq1 Hin' =>
                destruct_match_true_r _ _ Heq1
                                      (match destruct_match_true_l _ _ Hin' with
                                       | conj Heq1 Hin' =>
                                         destruct_match_true_r _ _ Heq1
                                                               (match destruct_match_true_l _ _ Hin' with
                                                                | conj Heq1 Hin' =>
                                                                  destruct_match_true_r _ _ Heq1 _
                                                                end)
                                       end)
              end).

      refine (match destruct_match_true_l _ _ Hin' with
              | conj Heqg1 Hin' => destruct_match_true_r _ _ (IHk1 _ _ _ _ (le_S_n _ _ Hleq) Heqg1) _
              end).
      refine (match destruct_match_true_l _ _ Hin' with
              | conj Heqg2 Hin' => destruct_match_true_r _ _ (IHk1 _ _ _ _ (le_S_n _ _ Hleq) Heqg2) _
              end).
      reflexivity. 
      suchThatMaybeOpt

      2:{ 
      
      eapply (checker_backtrack_spec ls1). in Hdec.
        
        destruct Hdec as [f [[H1 | [ H2 | [] ]] H3]].
        +         Show Proof. 
 destruct t; subst; try congruence.
          subst. eapply checker_backtrack_spec.
          eexists. split. now left. reflexivity.

        + subst. destruct t; try congruence.
           
          eapply checker_backtrack_spec.
          eexists. split. right. now left.
          
          
          destruct (@decOpt (m <= n0) _ 42) eqn:Hdle'; [ | congruence ].
          destruct b; [ | congruence ].

          destruct (@decOpt (n0 <= n) _ 42) eqn:Hdle''; [ | congruence ].
          destruct b; [ | congruence ].

          match goal with
          | [ H : (match ?e with _ => _ end = Some true) |- _ ] =>
            destruct e eqn:Heqb
          end; [ | congruence ].
          destruct b; [ | congruence ]. 
          match goal with
          | [ H : (match ?e with _ => _ end = Some true) |- _ ] =>
            destruct e eqn:Heqb'
          end; [ | congruence ].
          destruct b; [ | congruence ].
          rewrite (IHk1 true). rewrite (IHk1 true).
          reflexivity. lia. eassumption. lia. eassumption. }


      { (* b = false *)
        unfold decOpt, DecOptbst in *.
        assert (Hf := proj1 (checker_backtrack_spec_false _) Hdec). 
        eapply checker_backtrack_spec_false.
        intros f Hin. destruct Hin.
        - subst; destruct t; eauto.
        - destruct H; eauto. 2:{ now inv H. } subst.
          destruct t. reflexivity.
          
          destruct (@decOpt (m <= n) _ 42) eqn:Hdle.
          2:{ assert (Hc : (fun (_ : unit) => @None bool) tt = Some false).
              { eapply Hf with (f := (fun (_ : unit) => @None bool)).
                right. left. reflexivity. }
              congruence. }  

          destruct b; [ | congruence ].
          
          destruct (@decOpt (m <= n0) _ 42) eqn:Hdle'.
          2:{ assert (Hc : (fun (_ : unit) => @None bool) tt = Some false).
              { eapply Hf with (f := (fun (_ : unit) => @None bool)).
                right. left. reflexivity. }
              congruence. }  

          destruct b; [ | congruence ].

          destruct (@decOpt (n0 <= n) _ 42) eqn:Hdle''.
          2:{ assert (Hc : (fun (_ : unit) => @None bool) tt = Some false).
              { eapply Hf with (f := (fun (_ : unit) => @None bool)).
                right. left. reflexivity. }
              congruence. }  
          
          destruct b; [ | congruence ].
          
          match goal with 
          | [ |- match ?g ?k ?m ?n ?t with _ => _ end = Some false ] => set (ch := g)
          end.

          destruct (ch k1 m n0 t1) as [ b1 | ] eqn:Heq1.

          2:{ unfold ch in *. rewrite Heq1 in Hf. 
              assert (Hc : (fun (_ : unit) => @None bool) tt = Some false).
              { eapply Hf with (f := (fun (_ : unit) => @None bool)).
                right. left. reflexivity. }
              congruence. }
            
          assert (Heq2 := Heq1).
          eapply IHk1 with (k2 := k2) in Heq2; [ | lia ].
          
          unfold ch in Heq1. rewrite Heq1 in Hf.

          unfold ch. rewrite Heq2.  
          destruct b1. 2:{ reflexivity. } 
          
          destruct (ch k1 n0 n t2) as [ b2 | ] eqn:Heq1'.
          
          2:{ unfold ch in *. rewrite Heq1' in Hf. 
              assert (Hc : (fun (_ : unit) => @None bool) tt = Some false).
              { eapply Hf with (f := (fun (_ : unit) => @None bool)).
                right. left. reflexivity. }
              congruence. }


          assert (Heq2' := Heq1').
          eapply IHk1 with (k2 := k2) in Heq2'; [ | lia ].

          unfold ch in Heq1'. rewrite Heq1' in Hf.
          
          rewrite Heq2'.

          destruct b2; [| reflexivity ].

          
          eapply Hf with (f := (fun _ : unit => if b2 then Some true else Some false)).
          right. left. reflexivity. }
          
  Qed.

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
  
End BSTProofs.
