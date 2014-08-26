Require Import ZArith. (* omega *)
Require Import List.

(** * Useful tactics *)
Ltac inv H := inversion H; clear H; subst.
Ltac gdep x := generalize dependent x.

(* inv by name of the Inductive relation *)
Ltac invh f :=
    match goal with
      [ id: f |- _ ] => inv id
    | [ id: f _ |- _ ] => inv id
    | [ id: f _ _ |- _ ] => inv id
    | [ id: f _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    end.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(* ---------------------------------------------------------------- *)
(* Tactics for replacing definitional equality with provable equality *)
Module EqualityTactics.
(* NC: Using a module here to show where these equality related defs
start and end.  It appears that [Ltac] defs don't escape from sections
... *)

Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof.
auto. Qed.

(* Existentially instantiate a hypothesis. *)
Ltac exploit x :=
 refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).

Ltac try_exploit l :=
  try (exploit l;
       try solve [eauto];
       let H := fresh "H" in intros H;
       repeat match goal with
                | [H : (exists _, _) |- _ ] => destruct H
                | [H : _ /\ _ |- _ ] => destruct H
              end;
       subst).

(* NC: need to change the order of the premises, versus [modusponens],
so I can get at the implication [P -> Q] first; the proof of [P] may
generate arbitrarily many subgoals. *)
Lemma cut': forall (P Q: Prop), (P -> Q) -> P -> Q.
Proof. auto. Qed.

(* Like [exploit], but using [cut']. *)
Ltac ecut' x :=
    refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _))
 || refine (cut' _ _ _ (x _ _))
 || refine (cut' _ _ _ (x _))
 || refine (cut' _ _ _ (x)).

(* Like [exact H], but allow indexes to be definitionally different if
   they are provably equal.

   For example, a goal

     H : T a1 ... an
     ---------------
     T b1 ... bn

   is reduced to proving

     a1 = b1, ..., an = bn

   by [exact_f_equal H].
*)
Ltac exact_f_equal h :=
  let h_eq := fresh "h_eq" in
  let t := type of h in
  match goal with
  | [ |- ?g ] =>
    cut (g = t); [ intro h_eq; rewrite h_eq; exact h | f_equal; auto ]
  end.

(* A generalization of [exact_f_equal] to implications.

   This is like [applys_eq] from LibTactics.v, except you do not need
   to specify which vars you want equalities for.  See Software
   Foundations for a description of [applys_eq]:
   http://www.cis.upenn.edu/~bcpierce/sf/UseTactics.html#lab869

*)
Ltac apply_f_equal h :=
  let h_specialized := fresh "h_specialized" in
  let t := intro h_specialized; exact_f_equal h_specialized in
  (ecut' h; [t|..]).

(* Solve sub goals with [tac], using [f_equal] to make progress when
   possible
*)
Ltac rec_f_equal tac :=
  tac || (progress f_equal; rec_f_equal tac).

Section Test.

Open Scope nat.

Lemma test_apply_f_equal:
  forall (n1 n2: nat) (P: nat -> list (list nat) -> nat -> Prop),
  (forall a, 0 = a -> a = 0 ->
             P a (((n1+1)::nil)::nil) (n1+n2)) ->
  forall b, P (b - b) (((1+n1)::nil)::nil) (n2+n1).
Proof.
  intros ? ? ? HP ?.
  apply_f_equal HP; rec_f_equal auto.
Qed.

Lemma test_exact_f_equal: forall (n1 n2: nat) (P: nat -> nat -> Prop),
  P (n1+1) (n1+n2) -> P (1+n1) (n2+n1).
Proof.
  intros ? ? ? HP. exact_f_equal HP; omega.
Qed.

Lemma test_rec_f_equal:
  forall (n1 n2: nat) (P: list (list nat) -> nat -> Prop),
  P (((n1+1)::nil)::nil) (n1+n2) -> P (((1+n1)::nil)::nil) (n2+n1).
Proof.
  intros ? ? ? HP. exact_f_equal HP; rec_f_equal omega.
Qed.

End Test.

End EqualityTactics.
Export EqualityTactics.

(* Borrowed from CPDT *)
(* Instantiate a quantifier in a hypothesis [H] with value [v], or,
if [v] doesn't have the right type, with a new unification variable.
Also prove the lefthand sides of any implications that this exposes,
simplifying [H] to leave out those implications. *)

Ltac guess v H :=
 repeat match type of H with
          | forall x : ?T, _ =>
            match type of T with
              | Prop =>
                (let H' := fresh "H'" in
                  assert (H' : T); [
                    solve [ eauto 6 ]
                    | specialize (H H'); clear H' ])
                || fail 1
              | _ =>
                specialize (H v)
                || let x := fresh "x" in
                  evar (x : T);
                  let x' := eval unfold x in x in
                    clear x; specialize (H x')
            end
        end.


Ltac eq_H_intros :=
  repeat
    (match goal with
      | [  |- _ = _ -> _ ] =>
        intros ?Heq
    end).

Ltac eq_H_getrid :=
  repeat
    (match goal with
       | [  |- _ = _ -> _ ] =>
         intros _
     end).

Ltac decEq :=
  match goal with
  | [ |- _ = _ ] => f_equal
  | [ |- (?X ?A <> ?X ?B) ] =>
      cut (A <> B); [intro; congruence | try discriminate]
  end.

Ltac allinv :=
  repeat
    match goal with
      | [ H: Some _ = Some _ |- _ ] => inv H
      | [ H: Some _ = None |- _ ] => inv H
      | [ H: None = Some _ |- _ ] => inv H
      | _ => idtac
    end.

Ltac allinv' :=
  allinv ;
    (match goal with
       | [ H1:  ?f _ _ = _ ,
           H2:  ?f _ _ = _ |- _ ] => rewrite H1 in H2 ; inv H2
     end).

(* NC: Ltac is not exported from [Section]. This is for simplifying
the existential in [predicted_outcome]. *)
Ltac simpl_exists_tag :=
  match goal with
  | [ H: exists _, ?x = (_,_) |- _ ] => destruct H; subst x; simpl
  end.


(* And basic lemmas *)
Lemma rev_nil_nil (A: Type) : forall (l: list A),
  rev l = nil ->
  l = nil.
Proof.
  induction l; intros ; auto.
  simpl in *.
  exploit app_eq_nil ; eauto.
  intros [Hcont1 Hcont2].
  inv Hcont2.
Qed.

(* Monad notation *)

Definition bind (A B:Type) (f:A->option B) (a:option A) : option B :=
    match a with
      | None => None
      | Some a => f a
    end.

Module DoNotation.

Notation "'do' X <- A ; B" :=
  (bind _ _ (fun X => B) A)
  (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' X : T <- A ; B" :=
  (bind _ _ (fun X : T => B) A)
  (at level 200, X ident, A at level 100, B at level 200).

End DoNotation.

(* Useful functions on lists *)

Set Implicit Arguments.

(* What I wanted to write for group_by (taken from ghc stdlib)
Fixpoint span A (p : A -> bool) (xs : list A) : list A * list A :=
  match xs with
  | nil => (nil,nil)
  | x :: xs' =>
      if p x then
        let (ys,zs) := span p xs' in (x::ys,zs)
      else
        (nil,xs)
  end.

Fixpoint group_by A (e : A -> A -> bool) (xs : list A) : list (list A) :=
  match xs with
  | nil => nil
  | x::xs' => let (ys,zs) := span (e x) xs' in (x::ys) :: group_by e zs
  end.
Error: Cannot guess decreasing argument of fix. *)

(* What I ended up writing for group_by *)
Require Import Omega.
Require Import Recdef.

Definition span' X (p : X -> bool) : forall (xs : list X),
    {x : list X * list X | le (length (snd x)) (length xs)}.
  refine(
    fix span xs :=
      match xs
      return {x : list X * list X | le (length (snd x)) (length xs)}
      with
        | nil => exist _ (nil,nil) _
        | x :: xs' =>
            if p x then
              exist _ (x :: fst (proj1_sig (span xs')),
                       snd (proj1_sig (span xs'))) _
            else
              exist _ (nil,x::xs') _
      end).
  simpl. omega.
  simpl in *. destruct (span xs'). simpl. omega.
  simpl. omega.
Defined.

Function group_by (A : Type) (e : A -> A -> bool)
                  (xs : list A) {measure length xs}
  : list (list A) :=
  match xs with
  | nil => nil
  | x::xs' => (x :: fst (proj1_sig (span' (e x) xs')))
              :: group_by e (snd (proj1_sig (span' (e x) xs')))
  end.
intros. destruct (span' (e x) xs'). simpl. omega.
Defined.

(*
Eval compute in group_by beq_nat (1 :: 2 :: 2 :: 3 :: 3 :: 3 :: nil).
*)

Fixpoint zip_with_keep_rests (A B C : Type) (f : A -> B -> C)
    (xs : list A) (ys : list B) : (list C * (list A * list B)) :=
  match xs, ys with
  | x::xs', y::ys' =>
      let (zs, rest) := zip_with_keep_rests f xs' ys' in
        (f x y :: zs, rest)
  | nil, _ => (nil, (nil, ys))
  | _, nil => (nil, (xs, nil))
  end.

(*
Eval compute in zip_with_keep_rests plus (1 :: 2 :: 3 :: nil)
                                         (1 :: 1 :: nil).

Eval compute in zip_with_keep_rests plus (1 :: 1 :: nil)
                                         (1 :: 2 :: 3 :: nil).
*)

Definition zip_with (A B C : Type) (f : A -> B -> C)
    (xs : list A) (ys : list B) : list C :=
  fst (zip_with_keep_rests f xs ys).

Fixpoint consecutive_with (A B : Type) (f : A -> A -> B) (xs : list A)
    : list B :=
  match xs with
  | nil => nil
  | x1 :: xs' =>
    match xs' with
    | nil => nil
    | x2 :: xs'' => f x1 x2 :: consecutive_with f xs'
    end
  end.

Definition consecutive (A : Type) := consecutive_with (@pair A A).

(*
Eval compute in consecutive (1 :: 2 :: 3 :: 4 :: 5 :: nil).
*)

Fixpoint last_with (A B : Type) (f : A -> B) (l : list A) (d : B) : B :=
  match l with
  | nil => d
  | a :: nil => f a
  | a :: l => last_with f l d
  end.

Definition last_opt (A : Type) xs := last_with (@Some A) xs None.

(*
Eval compute in last_opt (1 :: 2 :: 3 :: nil).
Eval compute in last_opt (@nil nat).
*)

Fixpoint snoc (A : Type) (xs : list A) (y : A) : list A :=
  match xs with
  | nil => y :: nil
  | x :: xs' => x :: (snoc xs' y)
  end.

Fixpoint init (X : Type) (xs : list X) : list X :=
  match xs with
  | nil => nil
  | x1 :: xs' =>
    match xs' with
    | nil => nil
    | x2 :: xs'' => x1 :: (init xs')
    end
  end.

(*
Eval compute in init (1 :: 2 :: 3 :: nil).
Eval compute in init (1 :: nil).
Eval compute in init (@nil nat).
*)
(** * Finite and infinite traces *)

CoInductive trace (A : Type) : Type :=
  | TNil : trace A
  | TCons : A -> trace A -> trace A.

Implicit Arguments TNil [A].

Fixpoint list_to_trace (A : Type) (xs : list A) : trace A :=
  match xs with
  | nil => TNil
  | x :: xs' => TCons x (list_to_trace xs')
  end.

CoFixpoint map_trace (A B: Type) (f: A -> B) (t: trace A) : trace B :=
  match t with
    | TNil => TNil
    | TCons a ta => TCons (f a) (map_trace f ta)
  end.

Definition frob A (t : trace A) : trace A :=
  match t with
    | TCons h t' => TCons h t'
    | TNil => TNil
  end.

Theorem frob_eq : forall A (t : trace A), t = frob t.
  destruct t; reflexivity.
Qed.

Definition nth_error_Z {A:Type} (l:list A) (n:Z) : option A :=
  if Z.ltb n 0 then None
  else nth_error l (Z.to_nat n).

Lemma nth_error_nil : forall A pc,
  nth_error nil pc = @None A .
Proof.
  induction pc; auto.
Qed.

Lemma nth_error_Z_nil : forall A i,
  nth_error_Z nil i = @None A .
Proof.
  intros. unfold nth_error_Z. destruct (i <? 0)%Z. auto. apply nth_error_nil.
Qed.

Lemma nth_error_Z_nat (A: Type) :
  forall l i (v:A),
    nth_error_Z l i = Some v ->
    nth_error l (Z.to_nat i) = Some v.
Proof.
  intros. unfold nth_error_Z in *. destruct (i <? 0)%Z. congruence. 
auto.
Qed.

Lemma nth_error_cons (T: Type): forall n a (l:list T),
 nth_error l n = nth_error (a :: l) (n+1)%nat.
Proof.
  intros.
  replace ((n+1)%nat) with (S n) by omega.
  gdep n. induction n; intros.
  destruct l ; simpl; auto.
  destruct l. auto.
  simpl. eauto.
Qed.

Lemma nth_error_Z_cons (T: Type): forall i (l1: list T) a,
  (i >= 0)%Z ->
  nth_error_Z l1 i = nth_error_Z (a::l1) (i+1).
Proof.
  induction i; intros.
  auto.
  unfold nth_error_Z. simpl.
  replace (Pos.to_nat (p + 1)) with ((Pos.to_nat p)+1)%nat by (zify; omega).
  eapply nth_error_cons with (l:= l1) (a:= a) ; eauto.
  zify; omega.
Qed.

Lemma nth_error_Z_app:
  forall (T : Type)  (l1 l2: list T) (i : Z),
  i = Z.of_nat (length l1) -> nth_error_Z (l1 ++ l2) i = nth_error_Z l2 0.
Proof.
  induction l1; intros.
  simpl in *. subst. auto.
  simpl (length (a::l1)) in H.  zify.
  simpl.
  replace i with (i - 1 + 1)%Z by omega.
  erewrite <- nth_error_Z_cons by try omega.
  eapply IHl1. omega.
Qed.


Lemma nth_error_Z_eq (T: Type) : forall (l1 l2: list T),
  (forall i, nth_error_Z l1 i = nth_error_Z l2 i) ->
  l1 = l2.
Proof.
  induction l1; intros.
  destruct l2 ; auto.
  assert (HCont:= H 0%Z). inv HCont.
  destruct l2.
  assert (HCont:= H 0%Z). inv HCont.
  assert (a = t).
  assert (Helper:= H 0%Z). inv Helper. auto.
  inv H0.
  erewrite IHl1 ; eauto.
  intros. destruct i.
  erewrite nth_error_Z_cons with (a:= t); eauto; try omega.
  erewrite H ; eauto.
  erewrite nth_error_Z_cons with (a:= t); eauto; try (zify ; omega).
  erewrite H ; eauto. symmetry. eapply nth_error_Z_cons; eauto. zify; omega.
  destruct l1, l2 ; auto.
Qed.

Lemma nth_error_valid (T:Type): forall n (l:list T) v,
   nth_error l n = Some v -> n < length l.
Proof.
  induction n; intros; destruct l; simpl in H.
     inv H.
     inv H.  simpl.  omega.
     inv H.
     pose proof (IHn _ _ H). simpl. omega.
Qed.


Lemma nth_error_Z_valid (T:Type): forall i (l:list T) v,
   nth_error_Z l i = Some v -> (0 <= i)%Z  /\ (Z.to_nat i < length l)%nat.
Proof.
   intros.
   unfold nth_error_Z in H.  destruct ((i <? 0)%Z) eqn:?. inv H.
   split. apply Z.ltb_ge; auto.
   eapply nth_error_valid; eauto.
Qed.


Fixpoint update_list A (xs : list A) (n : nat) (y : A) : option (list A) :=
  match xs, n with
  | nil, _ => None
  | _ :: xs', 0 => Some (y :: xs')
  | a :: xs', S n' =>
    match update_list xs' n' y with
      | None => None
      | Some l => Some (a::l)
    end
  end.

Lemma update_some_not_nil : forall A (v:A) l a l',
  update_list l a v = Some l' ->
  l' = nil ->
  False.
Proof.
  destruct l; intros.
  destruct a ; simpl in * ; congruence.
  destruct a0 ; simpl in *. congruence.
  destruct update_list.  inv H.
  congruence.
  congruence.
Qed.

Definition update_list_Z A (xs: list A) i y : option (list A) :=
  if Z.ltb i 0 then
    None
  else
    update_list xs (Z.to_nat i) y.

Lemma update_Z_some_not_nil : forall A (v:A) l i l',
  update_list_Z l i v = Some l' ->
  l' = nil ->
  False.
Proof.
  intros. unfold update_list_Z in *.  destruct (i <? 0)%Z. congruence.
  eapply update_some_not_nil; eauto.
Qed.


Lemma update_list_Z_nat (A: Type) (v:A) l i l':
  update_list_Z l i v = Some l' ->
  update_list l (Z.to_nat i) v = Some l'.
Proof.
  intros. unfold update_list_Z in *. destruct (i <? 0)%Z. congruence.
  auto.
Qed.

Lemma update_list_spec (T: Type) : forall (v: T) l a l',
  update_list l a v = Some l' ->
  nth_error l' a = Some v.
Proof.
  induction l ; intros.
  destruct a ; simpl in *; inv H.
  destruct a0 ; simpl in *; inv H; auto.
  case_eq (update_list l a0 v) ; intros ; rewrite H in * ; inv H1.
  auto.
Qed.

Lemma update_list_Z_spec (T: Type) : forall (v: T) l a l',
  update_list_Z l a v = Some l' ->
  nth_error_Z l' a = Some v.
Proof.
  unfold update_list_Z, nth_error_Z. intros.
  destruct (a <? 0)%Z.  congruence.
  eapply update_list_spec; eauto.
Qed.

Lemma update_list_spec2 (T:Type) : forall (v:T) l n n' l',
  update_list l n v = Some l' ->
  n <> n' ->
  nth_error l n' = nth_error l' n'.
Proof.
  induction l; intros.
  destruct n; simpl in *; inv H.
  destruct n.
    destruct n'.
      exfalso; omega.
      destruct l'; inv H.
      simpl. auto.
    destruct n'.
      destruct l'; inv H.
        destruct (update_list l n v); inv H2.
        destruct (update_list l n v); inv H2.
        auto.
      destruct l'; inv H.
        destruct (update_list l n v); inv H2.
        simpl.
        destruct  (update_list l n v) eqn:?; inv H2.
        eapply IHl; eauto.
Qed.


Lemma update_list_Z_spec2 (T:Type) : forall (v:T) l a a' l',
  update_list_Z l a v = Some l' ->
  a' <> a ->
  nth_error_Z l a' = nth_error_Z l' a'.
Proof.
  unfold update_list_Z, nth_error_Z. intros.
  destruct (a <? 0)%Z eqn:?. congruence.
  destruct (a' <? 0)%Z eqn:?. auto.
  eapply update_list_spec2; eauto.
  apply Z.ltb_ge in Heqb.
  apply Z.ltb_ge in Heqb0.
  intro. apply H0. apply Z2Nat.inj; eauto.
Qed.

Lemma update_list_Some (T: Type): forall (v: T) l n,
  n < length l ->
  exists l', update_list l n v = Some l'.
Proof.
  induction l; intros.
  - inv H.
  - destruct n.
    + simpl.  eauto.
    + simpl. edestruct IHl as [l' E]. simpl in H. instantiate (1:= n). omega.
      eexists. rewrite E. eauto.
Qed.

Lemma valid_update :
  forall T i (l : list T) x x',
    nth_error_Z l i = Some x ->
    exists l',
      update_list_Z l i x' = Some l'.
Proof.
  intros.
  unfold nth_error_Z, update_list_Z in *.
  destruct (i <? 0)%Z; try congruence.
  - remember (Z.to_nat i) as n; clear Heqn.
    generalize dependent n.
    generalize dependent l.
    induction l; intros.
    + destruct n; simpl in H; discriminate.
    + destruct n; simpl in *.
      * simpl; eauto.
      * simpl in *.
        edestruct IHl as [l' Hl']; eauto.
        rewrite Hl'. eauto.
Qed.

Definition swap T n (l : list T) : option (list T) :=
  match l with
    | nil => None
    | y :: l' =>
      match nth_error (y :: l') n with
        | Some x => update_list (x :: l') n y
        | None => None
      end
  end.

Lemma filter_cons_inv_strong :
  forall X (l1 : list X) x2 l2
         (f : X -> bool),
    x2 :: l2 = filter f l1 ->
    exists l11 l12,
      l1 = l11 ++ l12 /\
      filter f l11 = x2 :: nil /\
      filter f l12 = l2.
Proof.
  intros X l1.
  induction l1 as [|x1 l1 IH]; simpl; try congruence.
  intros.
  destruct (f x1) eqn:E.
  - exists (x1 :: nil).
    exists l1.
    simpl.
    rewrite E.
    inv H.
    eauto.
  - exploit IH; eauto.
    clear IH.
    intros [l11 [l12 [H1 [H2 H3]]]].
    subst.
    exists (x1 :: l11).
    exists l12.
    simpl.
    rewrite E. eauto.
Qed.

Lemma filter_cons_inv :
  forall A (f : A -> bool) a l1 l2,
    a :: l1 = filter f l2 ->
    exists l2', l1 = filter f l2'.
Proof.
  induction l2 as [|a' l2 IH]; simpl. congruence.
  destruct (f a'); intros H; auto.
  inv H. eauto.
Qed.

Lemma filter_app :
  forall X (l1 l2 : list X) (f : X -> bool),
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1 as [|x l1 IH]; simpl; intros. trivial.
  rewrite IH. destruct (f x); auto.
Qed.

Lemma update_list_Z_Some (T:Type): forall (v:T) l (i:Z),
  (0 <= i)%Z ->
  Z.to_nat i < length l ->
  exists l', update_list_Z l i v = Some l'.
Proof.
  intros. unfold update_list_Z.
  destruct (i <? 0)%Z eqn:?.
  - rewrite Z.ltb_lt in Heqb. omega.
  - eapply update_list_Some; eauto.
Qed.

Lemma update_preserves_length: forall T a (vl:T) m m',
  update_list m a vl = Some m' ->
  length m' = length m.
Proof.
  induction a; intros.
  - destruct m; simpl in *.
    + inv H.
    + inversion H; subst; reflexivity.
  - destruct m; simpl in *.
    + inv H.
    + destruct (update_list m a vl) eqn:?.
      * exploit IHa; eauto.
        inversion H; subst.
        intros eq; rewrite <- eq; reflexivity.
      * inv H.
Qed.

Lemma app_same_length_eq (T: Type): forall (l1 l2 l3 l4: list T),
  l1++l2 = l3++l4 ->
  length l1 = length l3 ->
  l1 = l3.
Proof.
  induction l1; intros; simpl in *.
  destruct l3; auto. inv H0.
  destruct l3. inv H0. simpl in *.
  inv H. erewrite IHl1 ; eauto.
Qed.

Lemma app_same_length_eq_rest (T: Type): forall (l1 l2 l3 l4: list T),
  l1++l2 = l3++l4 ->
  length l1 = length l3 ->
  l2 = l4.
Proof.
  intros.
  exploit app_same_length_eq; eauto.
  intro Heq ; inv Heq.
  gdep l3. induction l3 ; intros; auto.
  simpl in *.
  inv H. eauto.
Qed.

Definition is_some T (o : option T) :=
  match o with
    | Some _ => true
    | None => false
  end.

Definition remove_none {T} (l : list (option T)) :=
  filter (@is_some _) l.

Inductive with_silent {T:Type} := | E (e:T) | Silent.
Notation "T +τ" := (@with_silent T) (at level 1).

Inductive match_actions {T1 T2} (match_events : T1 -> T2 -> Prop) : T1+τ -> T2+τ -> Prop :=
| match_actions_silent : match_actions match_events Silent Silent
| match_actions_event : forall e1 e2,
  match_events e1 e2 -> match_actions match_events (E e1) (E e2).

(** Reflexive transitive closure. *)
Definition op_cons (E: Type) (oe: E+τ) (l: list E) :=
  match oe with
      | E e => e::l
      | Silent => l
  end.


Inductive star (S E: Type) (Rstep: S -> E+τ -> S -> Prop): S -> list E -> S -> Prop :=
  | star_refl: forall s,
      star Rstep s nil s
  | star_step: forall s1 s2 s3 e t t',
      Rstep s1 e s2 -> star Rstep s2 t s3 ->
      t' = (op_cons e t) ->
      star Rstep s1 t' s3.
Hint Constructors star.

Lemma op_cons_app : forall E (e: E+τ) t t', (op_cons e t)++t' = op_cons e (t++t').
Proof. intros. destruct e; reflexivity. Qed.

Lemma star_right : forall S E (Rstep: S -> E+τ -> S -> Prop) s1 s2 t,
                     star Rstep s1 t s2 ->
                     forall s3 e t',
                       Rstep s2 e s3 ->
                       t' = (t++(op_cons e nil)) ->
                       star Rstep s1 t' s3.
Proof.
  induction 1; intros.
  eapply star_step; eauto.
  exploit IHstar; eauto. intros.
  inv H3. rewrite op_cons_app; eauto.
Qed.

Inductive plus (S E: Type) (Rstep: S -> E+τ -> S -> Prop): S -> list E -> S -> Prop :=
  | plus_step: forall s t s' e,
      Rstep s e s' ->
      t = (op_cons e nil) ->
      plus Rstep s t s'
  | plus_trans: forall s1 s2 s3 e t t',
      Rstep s1 e s2 -> plus Rstep s2 t s3 ->
      t' = (op_cons e t) ->
      plus Rstep s1 t' s3.

Hint Constructors star.
Hint Constructors plus.

Lemma plus_right : forall E S (Rstep: S -> E+τ -> S -> Prop) s1 s2 t,
                     plus Rstep s1 t s2 ->
                     forall s3 e t',
                       t' = (t++(op_cons e nil)) ->
                       Rstep s2 e s3 -> plus Rstep s1 t' s3.
Proof.
  induction 1; intros.
  inv H1.
  rewrite op_cons_app. simpl.
  eapply plus_trans; eauto.
  exploit IHplus; eauto.
  inv H2. rewrite op_cons_app.  eauto.
Qed.

Lemma step_star_plus :
  forall (S E: Type)
         (Rstep: S -> E+τ -> S -> Prop) s1 t s2
         (STAR : star Rstep s1 t s2)
         (NEQ : s1 <> s2),
    plus Rstep s1 t s2.
Proof.
  intros. inv STAR. congruence.
  clear NEQ.
  gdep e. gdep s1.
  induction H0; subst; eauto.
Qed.
Hint Resolve step_star_plus.

Lemma star_trans: forall S E (Rstep: S -> E+τ -> S -> Prop) s0 t s1,
  star Rstep s0 t s1 ->
  forall t' s2,
  star Rstep s1 t' s2 ->
  star Rstep s0 (t++t') s2.
Proof.
  induction 1.
  - auto.
  - inversion 1.
    + rewrite app_nil_r.
      subst; econstructor; eauto.
    + subst; econstructor; eauto.
      rewrite op_cons_app; reflexivity.
Qed.

Fixpoint replicate T (a: T) n : list T :=
  match n with
    | O => nil
    | S n => a::(replicate a n)
  end.

Lemma nth_error_In :
  forall T n (l : list T) (x : T),
    nth_error l n = Some x ->
    In x l.
Proof.
  intros.
  gdep l.
  induction n as [|n IH]; intros l H; destruct l as [|x' l]; simpl in *;
  try solve [inv H].
  - inv H. auto.
  - auto.
Qed.
Hint Resolve nth_error_In.

Lemma update_list_In :
  forall T n x y (l l' : list T)
         (UPD: update_list l n x = Some l')
         (IN: In y l'),
    y = x \/ In y l.
Proof.
  induction n as [|n IH]; intros; destruct l as [|x' l]; simpl in *;
  try solve [inv UPD].
  - inv UPD. destruct IN; eauto.
  - destruct (update_list l n x) as [l''|] eqn:UPD'; inv UPD.
    destruct IN; auto.
    exploit IH; eauto.
    intros []; eauto.
Qed.

Lemma swap_In :
  forall T n (l l' : list T) x
         (SWAP : swap n l = Some l')
         (IN : In x l'),
    In x l.
Proof.
  unfold swap.
  intros.
  destruct l as [|y l]; try congruence.
  destruct n as [|n]; simpl in *.
  - inv SWAP. eauto.
  - destruct (nth_error l n) as [x'|] eqn:IDX; try congruence.
    destruct (update_list l n y) as [l''|] eqn:UPD; try congruence.
    inv SWAP.
    destruct IN as [H | H]; subst; eauto.
    clear - UPD H.
    exploit update_list_In; eauto.
    intros []; auto.
Qed.

Lemma nth_error_app :
  forall T n (l1 l2 : list T) x,
    nth_error l1 n = Some x ->
    nth_error (l1 ++ l2) n = Some x.
Proof.
  induction n as [|n IH]; intros [|x' l1] l2 x H; simpl in *;
  try solve [inv H]; auto.
Qed.

Lemma update_list_app :
  forall T n x (l1 l1' l2 : list T)
         (UPD : update_list l1 n x = Some l1'),
    update_list (l1 ++ l2) n x = Some (l1' ++ l2).
Proof.
  induction n; intros;
  destruct l1 as [|x' l1]; simpl in *; allinv; auto.
  destruct (update_list l1 n x) as [l1''|] eqn:UPD'; allinv.
  erewrite IHn; eauto.
  simpl.
  reflexivity.
Qed.

Lemma swap_app :
  forall T n (l1 l1' l2 : list T)
         (SWAP : swap n l1 = Some l1'),
    swap n (l1 ++ l2) = Some (l1' ++ l2).
Proof.
  unfold swap.
  intros.
  destruct l1 as [|y l1]; simpl; try congruence.
  destruct (nth_error (y :: l1) n) as [x|] eqn:SWAP'; allinv.
  eapply nth_error_app in SWAP'.
  simpl in SWAP'.
  rewrite SWAP'.
  eapply update_list_app in SWAP.
  simpl in *.
  eauto.
Qed.

Lemma swap_forall :
  forall T (P : T -> Prop) n l l'
         (SWAP : swap n l = Some l')
         (FORALL : forall x, In x l -> P x),
    forall x, In x l' -> P x.
Proof.
  unfold swap.
  intros.
  destruct l as [|y l]; try congruence.
  destruct (nth_error (y :: l) n) as [x'|] eqn:IDX; try congruence.
  destruct n as [|n]; simpl in *; allinv; simpl in *; eauto.
  match goal with
    | H : (match ?UP with _ => _ end) = _ |- _ =>
      destruct UP as [l''|] eqn:?; simpl in *; try congruence
  end.
  allinv.
  destruct H.
  - subst. eauto.
  - exploit update_list_In; eauto.
    intros [? | ?]; subst; eauto.
Qed.

Fixpoint drop {X:Type} (n:nat) (xs:list X) : list X :=
match n with
| O => xs
| S n' => match xs with
          | nil => nil
          | (x::xs') => drop n' xs'
          end
end.

Definition dropZ {X:Type} (z:Z) (xs:list X) : list X :=
  if (z <? 0)%Z then
    xs
  else drop (Z.to_nat z) xs.


Lemma length_drop : forall {X:Type} n (xs:list X),
           length (drop n xs) = ((length xs) -  n)%nat.
Proof.
  intros X n. induction n; intros xs.
    simpl. omega.
    destruct xs. simpl.
       auto.
       simpl. auto.
Qed.

Lemma drop_cons : forall {X:Type} p (l : list X),
    (p < length l)%nat ->
    exists x,
      drop p l = x :: drop (S p) l.
Proof.
  induction p; intros [|x l] H; simpl in *; try omega; eauto.
  apply IHp.
  omega.
Qed.

Import ListNotations.

Lemma dropZ_all: forall {X:Type} (xs:list X),
  (dropZ (Z.of_nat (length xs)) xs = []).
Proof.
  intros.
  destruct (dropZ (Z.of_nat (length xs)) xs) eqn:E. auto.
  exfalso.
  unfold dropZ in E.  destruct (Z.of_nat (length xs) <? 0)%Z eqn:M.
    apply Z.ltb_lt in M.  omega.
    rewrite Nat2Z.id in E.
    assert (length (drop (length xs) xs) = length (x::l)). rewrite E; auto.
    rewrite length_drop in H. simpl in H. replace (length xs - length xs)%nat with O in H by omega. inv H.
Qed.

Lemma dropZ_nil :
  forall X (i : Z) (l : list X)
         (POS : (i >= 0)%Z)
         (BOUNDS : dropZ i l = []),
    (i >= Z.of_nat (length l))%Z.
Proof.
  intros.
  destruct (Z_lt_dec i (Z.of_nat (length l))) as [H|]; try omega.
  unfold dropZ in *.
  destruct (Z.ltb_spec0 i 0); try omega.
  rewrite Z2Nat.inj_lt in H; try omega.
  rewrite Nat2Z.id in H.
  apply drop_cons in H.
  destruct H.
  congruence.
Qed.

Lemma nth_error_drop_zero :
  forall X (i : nat) (l : list X),
    nth_error l i = nth_error (drop i l) 0.
Proof.
  intros X i.
  induction i as [|i IH].
  - intros [|a l]; reflexivity.
  - intros [|a l]; try reflexivity.
    simpl. rewrite IH. reflexivity.
Qed.

Lemma nth_error_Z_dropZ_zero :
  forall X (i : Z) (l : list X)
         (POS : (i >= 0)%Z),
    nth_error_Z l i = nth_error_Z (dropZ i l) 0.
Proof.
  intros.
  unfold nth_error_Z, dropZ.
  destruct (Z.ltb_spec0 i 0); try omega.
  rewrite nth_error_drop_zero.
  reflexivity.
Qed.

Lemma nth_error_drop :
  forall X (i i' : nat) (l : list X),
    nth_error l (i + i') = nth_error (drop i' l) i.
Proof.
  intros X i.
  induction i as [|i IH]; auto using nth_error_drop_zero.
  intros [|i'] [|a l]; try reflexivity.
  - rewrite plus_0_r. reflexivity.
  - simpl.
    rewrite IH.
    destruct (lt_dec i' (length l)) as [LT|GTE].
    + apply drop_cons in LT.
      destruct LT as [x H]. rewrite H. reflexivity.
    + assert (LEN := length_drop i' l).
      replace (length l - i')%nat with 0%nat in LEN by omega.
      assert (LEN' := length_drop (S i') l).
      replace (length l - S i')%nat with 0%nat in LEN' by omega.
      destruct (drop i' l), (drop (S i') l); simpl in *; try discriminate.
      destruct i; reflexivity.
Qed.

Lemma nth_error_Z_dropZ :
  forall X (i i' : Z) (l : list X)
         (POS1 : (i' >= 0)%Z)
         (POS2 : (i >= 0)%Z),
    nth_error_Z l (i + i') = nth_error_Z (dropZ i' l) i.
Proof.
  intros.
  unfold nth_error_Z, dropZ.
  destruct (Z.ltb_spec0 i' 0); try omega.
  destruct (Z.ltb_spec0 i 0); try omega.
  destruct (Z.ltb_spec0 (i + i') 0); try omega.
  rewrite Z2Nat.inj_add; try omega.
  apply nth_error_drop.
Qed.

Lemma dropZ_cons :
  forall X i (l : list X)
         (BOUNDS : (0 <= i < Z.of_nat (length l))%Z),
    exists x, dropZ i l = x :: dropZ (Z.succ i) l.
Proof.
  intros.
  unfold dropZ.
  destruct (Z.ltb_spec0 i 0); try omega.
  destruct (Z.ltb_spec0 (Z.succ i) 0); try omega.
  rewrite Z2Nat.inj_succ; try omega.
  apply drop_cons.
  rewrite <- Nat2Z.id.
  rewrite <- Z2Nat.inj_lt; omega.
Qed.

Inductive match_options {A B} (R : A -> B -> Prop) : option A -> option B -> Prop :=
| mo_none : match_options R None None
| mo_some : forall a b, R a b -> match_options R (Some a) (Some b).

Lemma Forall2_length :
  forall A B (R : A -> B -> Prop) l1 l2,
    Forall2 R l1 l2 -> length l1 = length l2.
Proof.
  induction 1; eauto; simpl; congruence.
Qed.

Fixpoint take {T} (n : nat) (l : list T) : list T :=
  match n with
    | O => []
    | S n' =>
      match l with
        | [] => []
        | x :: l' => x :: take n' l'
      end
  end.

Lemma nth_error_app' X : forall (l1 l2 : list X) (x : X),
                            nth_error (l1 ++ x :: l2) (length l1) = Some x.
Proof.
  induction l1 as [|x' l1 IH]; intros; simpl in *; subst; eauto.
Qed.

(* List helpers *)
Fixpoint concat {A : Type} (l : list (list A)) : (list A) :=
  match l with
    | [] => []
    | (h :: t) => h ++ concat t
  end.

Fixpoint forallb2 {A : Type} (f : A -> A -> bool) (l1 l2 :list A) : bool :=
  match l1, l2 with
    | nil, nil => true
    | h1::t1, h2::t2 => f h1 h2 && forallb2 f t1 t2
    | _, _ => false
  end%bool.

Fixpoint list_of_option {A : Type} (l : list (option A)) : list A :=
  match l with
    | nil => nil
    | Some h :: t => h :: list_of_option t
    | None :: t => list_of_option t
  end.

Fixpoint optOfList {A : Type} (l : list (option A)) (acc : list A)
: option (list A) :=
  match l with
    | nil  => Some acc
    | None::_ => None
    | Some h :: t => optOfList t (h :: acc)
  end.

Definition option_bind {X Y} (f : X -> option Y) (o : option X) :=
  match o with
  | Some x => f x
  | None => None
  end.

Fixpoint powerset {A : Type} (l : list A) : (list (list A)) :=
  match l with
    | [] => [[]]
    | h::t =>
      let p := powerset t in
      map (cons h) p ++ p
  end.

(* Helper functions *)
Definition flip {A B C : Type} (f : A -> B -> C) (x : B) (y : A) : C := f y x.
Definition compose {A B C : Type} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).
Notation " f << g " := (compose f g) (at level 42). (* F# style, because . *)
