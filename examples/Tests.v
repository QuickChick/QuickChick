
(* TODO: Make genTreeS_correct work again *)

(* TODO: Use point-free reasoning in generator proofs. *)

(* CH: Split this file into its component examples? *)

Require Import QuickChick.

Require Import List seq ssreflect ssrbool ssrnat ZArith eqtype.
Import ListNotations.

(* Currently, these two have to be imported manually. Can we avoid this?? *)
Import GenLow GenHigh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Small example with default arbitrary instances *)

Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if beq_nat h x then t else h :: remove x t
  end.

Definition removeP (x : nat) (l : list nat) :=
  collect x (~~ (existsb (pred1 x) (remove x l))).

QuickChick removeP.

Definition propLength (A : Type) (l : list A) :=
  (List.length l) <= 20.

QuickChick propLength.

(* Tree example showing custom datatypes *)

Inductive tree (A : Type) :=
| Leaf : tree A
| Node : A -> tree A -> tree A -> tree A.

Arguments Leaf {A}.
Arguments Node {A} _ _ _.

Fixpoint eq_tree (A : eqType) (t1 t2 : tree A) :=
  match t1, t2 with
  | Leaf, Leaf => true
  | Node x1 l1 r1, Node x2 l2 r2 => [&& x1 == x2, eq_tree l1 l2 & eq_tree r1 r2]
  | _, _ => false
  end.

Lemma eq_treeP (A : eqType) : Equality.axiom (@eq_tree A).
Proof.
  move=> t1 t2; apply/(iffP idP) => [|<-].
  elim: t1 t2 => [|x1 l1 IHl1 r1 IHr1] [|x2 l2 r2] //=.
    by case/and3P=> /eqP-> /IHl1-> /IHr1->.
    by elim: t1 => //= x ? -> ? ->; rewrite eqxx.
Qed.

Canonical tree_eqMixin (A : eqType) := EqMixin (@eq_treeP A).
Canonical tree_eqType (A : eqType) := Eval hnf in EqType (tree A) (tree_eqMixin A).

(* Step one: Write custom generators *)

Fixpoint genTreeS {A} (g : G A) (n : nat) : G (tree A) :=
  match n with
    | O => returnGen Leaf
    | S n' =>
      frequency (returnGen Leaf)
                 [(1, returnGen Leaf);
                  (n, liftGen3 Node g (genTreeS g n') (genTreeS g n'))]
  end.

(* CH: I'm a bit surprised that we don't use sized here,
       that seems equivalent anyway, right? *)
Definition genTree {A : Type} (g : G A) : G (tree A) :=
  bindGen arbitrary (genTreeS g).


Instance arbTree {A} `{Arbitrary A} : Arbitrary (tree A) :=
{|
  arbitrary := genTree arbitrary;
  shrink t :=
      let fix shrinkTree (t : tree A) :=
          match t with
            | Leaf => []
            | Node x l r => [l] ++ [r] ++
              map (fun x' => Node x' l r) (shrink x) ++
              map (fun l' => Node x l' r) (shrinkTree l) ++
              map (fun r' => Node x l r') (shrinkTree r)
          end
      in shrinkTree t
|}.


Require Import Coq.Strings.String.
Open Scope string.

Instance showTree {A : Type} `{_ : Show A} : Show (tree A) :=
{|
  show t :=
    let fix showTree (t : tree A) :=
        match t with
          | Leaf => "Leaf"
          | Node x l r => "Node " ++ show x
                                  ++ " ( " ++ showTree l ++ " ) "
                                  ++ " ( " ++ showTree r ++ " ) "
        end
    in showTree t
|}.

Open Scope list.

(* Step 2: Test a simple property about mirroring trees *)

(* Faulty mirror function *)
Fixpoint mirror {A : Type} (t : tree A) : tree A :=
  match t with
    | Leaf => Leaf
    | Node x l r => Node x (mirror l) (mirror l)
  end.

Definition mirrorK (t : tree nat) := mirror (mirror t) == t.

QuickChick mirrorK.

(* Step 3 : Prove generators correct   *)

Fixpoint height {A} (t : tree A) :=
  match t with
    | Leaf => 0
    | Node a t1 t2 =>
      (maxn (height t1) (height t2)) + 1
  end.

Lemma genTreeS_correct :
  forall {A} (g : G A) n s,
    semGenSize g s <--> (fun _ => True) ->
    (semGenSize (genTreeS g n) s) <--> (fun t => (height t) <= n).
Proof.
  move=> A g n.
  elim : n => //= [| n IHn] s Hg t.
  * split.
    + rewrite (semReturnSize _ _ _). by move => <-.
    + case: t => [| t1 t2] //= a . by rewrite (semReturnSize _ _ _).
      by rewrite addn1 ltn0.
  * move/IHn : (Hg)=> HgenT. split => [| Hheight].
Admitted.
(* TODO: fix this
    + move/semFrequencySize. move =>
      [[n' [gtree [[[Heq1 Heq2] | [[Heq1 Heq2] | //=]] [H2 _]]]] | [H1 H2]]; subst;
      (try by apply semReturnSize in H2; subst).
      apply semLiftGen3Size in H2.
      move : H2 => [a1 [ga1 [t1 [/HgenT Hgt1 [t2 [/HgenT Hgt2 Heq]]]]]]; subst.
      simpl. rewrite -[X in _ <= X]addn1 leq_add2r.
        by rewrite geq_max Hgt1 Hgt2.
    + apply/semFrequencySize. left.
      case: t Hheight => [| a t1 t2] //=.
      - move => _. exists 1. eexists. split. by constructor.
        split => //. by apply semReturnSize.
      - rewrite -[X in _ <= X]addn1 leq_add2r.
        rewrite geq_max => /andP [leq1 le2].
        exists n.+1. exists (liftGen3 Node g (genTreeS g n) (genTreeS g n)).
        split => //=. by right; left.
        split => //=. apply semLiftGen3Size.
        exists a; split; first exact/Hg.
        exists t1; split; first exact/IHn.
        by exists t2; split; first exact/IHn.
Qed.
*)

Lemma genTree_correct:
  forall {A} (g : G A) s,
    semGenSize g s <--> (fun _ => True) ->
    semGenSize (genTree g) s <--> (fun t => height t <= s).
Proof.
  move=> A g s Hg t. rewrite /genTree.
  - split => //= [/semBindSize [n [/arbNat_correctSize/leP H1 /genTreeS_correct H2]]
                 | H].
    eapply leq_trans; try eassumption. auto.
  - apply semBindSize. exists s.
    split; first by apply arbNat_correctSize.
    apply genTreeS_correct; auto.
Qed.

(* Step 4: Proving correctness of checkers *)

Definition max_elem :=
  fix f l :=
  match l with
    | [] => 0
    | x :: xs => (max x (f xs))
  end.

Lemma below_max_elem:
  forall (l : list nat) x,
    In x l -> x <= (max_elem l).
Proof.
  intros l.
  elim : l => //= [x1 xs IHxs] x2 [Heq | HIn]; subst.
  - apply/leP. by apply Max.le_max_l.
  - apply IHxs in HIn. apply Max.max_case_strong => H; auto.
    apply/leP. eapply le_trans; try eassumption. by apply/leP.
Qed.

(* CH: Why is this so complicated?
   CH: Would it help if we split out a reflect lemma about
       `(~~ (existsb (pred1 x) (remove x l)))`?
   CH: also split out proof about generator for lists
   CH: TODO: try to understand how the sizes appear here
   CH: TODO: try to see whether going via `proposition` really helps or not *)
Theorem removeP_correct:
  semCheckable removeP <-> (forall (x : nat) l, ~ In x (remove x l)).
Proof.
  unfold semCheckable, semChecker. setoid_rewrite <- proposition_equiv.
  simpl; split. unfold removeP.
  - move => H x l cont.
    set size := max x (max (max_elem l) (List.length l)).
    have Hnat : semGenSize arbitraryNat size x
      by apply arbNat_correctSize; apply Max.le_max_l.
    have Hlist: semGenSize arbitraryList size l.
    { eapply arbList_correct with (P := fun x y => (y <= x)%coq_nat).
      move => n. by rewrite (arbNat_correctSize _ _).
      split. apply Max.max_case_strong => H'; auto. apply/leP.
      eapply Max.max_lub_r; eassumption. by apply/leP; apply Max.le_max_r.
      move => x' /below_max_elem /leP Helem.
      apply Max.max_case_strong => H'; auto.
      eapply le_trans; try eassumption. eapply Max.max_lub_l. by eapply H'.
      apply Max.max_case_strong => H''; auto.
      eapply le_trans; try eassumption. }
    specialize (H size x Hnat l Hlist).
    setoid_rewrite semCollect_idSize in H. apply semCheckableBoolSize in H.
    have contra : existsb (pred1 x) (remove x l).
      { apply existsb_exists. exists x. split => //. by rewrite /= eq_refl. }
    rewrite contra in H. discriminate.
  -  move => H a HIn Hsize l Hsize'.
     rewrite /removeP. rewrite semCollect_idSize semCheckableBoolSize. apply Bool.eq_true_not_negb.
     move => /existsb_exists contra.
     move : contra => [n [HIn' /=/eqP Hpred]]; subst. eapply H.
     eassumption.
Qed.

(* TODO: Also prove mirrorK, it should be trivial, right *)
