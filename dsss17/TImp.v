Set Warnings "-notation-overridden,-parsing".
Set Warnings "-extraction-opaque-accessed,-extraction".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.

From QuickChick Require Import QuickChick Tactics.
Import QcDefaultNotation. Open Scope qc_scope.

Set Bullet Behavior "Strict Subproofs".
(* /IMPORTS *)

(* TODO: This should be imported *)
(** ** ATOM *)

Require Import Equalities.
Module Type ATOM <: UsualDecidableType.

  Parameter t : Set.
  Parameter eq_dec : forall (x y:t), {x = y} + {x <> y}.
  Parameter fresh : list t -> t.
  Parameter fresh_not_in : forall l, ~ In (fresh l) l.
  Parameter nat_of: t -> nat.

  Include HasUsualEq <+ UsualIsEq.

End ATOM.

(** ** Atom *)
(** Implements the [ATOM] signature. *)

Module Atom : ATOM.

  Definition t := nat.
  Definition eq_dec := eq_nat_dec.
  
  Fixpoint max_elt (al:list t) : t :=
    match al with
      | nil => 0
      | n'::al' => max n' (max_elt al')
    end.

  Definition fresh (al:list t) : t :=
    S (max_elt al).

  Lemma max_elt_spec : forall al b,
    In b al -> b <= max_elt al.
(* FOLD *)
  Proof.
    intros. induction al. inversion H.
      inversion H; subst; simpl. apply Nat.le_max_l.
      eapply le_trans; auto with arith. (* apply Nat.le_max_r. *)
  Qed.
(* /FOLD *)
    
  Lemma fresh_not_in : forall l, 
    ~ In (fresh l) l.
(* FOLD *)
  Proof.
    unfold fresh, not. intros l Hin.
    specialize (max_elt_spec _ _ Hin). intro Ha.
    contradict Ha; apply le_Sn_n.
  Qed.
(* /FOLD *)

  Include HasUsualEq <+ UsualIsEq.

  Definition nat_of (a : nat) := a.
  
End Atom.

(* Automatically unfold Atom.eq *)
Global Arguments Atom.eq /.

Instance show_atom : Show Atom.t :=
  {| show x := show (Atom.nat_of x) |}.

Fixpoint get_fresh_atoms n l :=
  match n with
  | 0 => l
  | S n' => get_fresh_atoms n' ((Atom.fresh l) :: l)
  end.

Definition fresh_store : list Atom.t := get_fresh_atoms 100 [].
Definition gen_fresh (atom_store : list Atom.t) : G Atom.t := 
  oneof (returnGen (Atom.fresh [])) (List.map returnGen atom_store).

Fixpoint index_of_atom_in_list (a : Atom.t) (l : list Atom.t) : option nat :=
  match l with
  | [] => None
  | (a' :: l') => if Atom.eq_dec a a' then Some 0 else
                   match index_of_atom_in_list a l' with
                   | Some n => Some (S n)
                   | None => None
                   end
  end.
(* All of the above should be imported *)

Module Type Map (K:UsualDecidableType).

Section withv.
Variable V : Type.

Parameter t : Type -> Type.
Parameter empty : t V.
Parameter get : t V -> K.t -> option V.
Parameter set : t V -> K.t -> V -> t V.
Parameter rem : t V -> K.t -> t V.
Parameter dom : t V -> list K.t.
Parameter forallb2 : (K.t -> V -> bool) -> t V -> bool.


Axiom update_eq : forall v k1 k2 m, k2 = k1 -> get (set m k1 v) k2 = Some v.
Axiom update_neq : forall v k1 k2 m, k2 <> k1 -> get (set m k1 v) k2 = get m k2.
Axiom get_in_dom : forall m k v, get m k = Some v -> In k (dom m).
Axiom dom_in_get : forall m k, In k (dom m) -> exists v, get m k = Some v.
Axiom get_forallb2 : forall m f,
                       (forall k v, get m k = Some v -> f k v = true) 
                       <-> forallb2 f m = true.
End withv.

End Map.


Module ListMap (K:UsualDecidableType) <: Map K.

Section withv.
Context {V : Type}.

Definition t := list (K.t * V).

Definition empty : t := [].

Fixpoint get m k : option V := 
  match m with
    | [] => None
    | (k', v) :: m' => if K.eq_dec k k'
                       then Some v
                       else get m' k
  end.

Definition set (m:t) (k:K.t) (v:V) : t :=
  (k, v) :: m.


Fixpoint rem (m:t) (k:K.t) : t :=
  match m with
    | [] => []
    | (k', v) :: m' => if K.eq_dec k k'
                       then rem m' k
                       else (k', v) :: rem m' k
  end.

Fixpoint dom (m:t) : list K.t :=
  match m with
    | [] => []
    | (k', v) :: m' => k' :: dom m'
  end.

Fixpoint forallb2' (f:K.t -> V -> bool) (m:t) (d:list K.t) : bool :=
     match d with
       | [] => true
       | k :: d' => match get m k with
                      | None => false
                      | Some v => f k v && forallb2' f m d'
                    end
     end.  

Definition forallb2 (f:K.t -> V -> bool) (m:t) : bool :=
  forallb2' f m (dom m).


Lemma update_eq : forall v k1 k2 m,

    k2 = k1 -> get (set m k1 v) k2 = Some v.
Proof.
  intros; simpl. destruct (K.eq_dec _ _); intuition.
Qed.


Lemma update_neq : forall v k1 k2 m,
  k2 <> k1 -> get (set m k1 v) k2 = get m k2.
Proof.
  intros; simpl. destruct (K.eq_dec _ _); intuition.
Qed.

Lemma get_in_dom : forall m k v,
  get m k = Some v -> In k (dom m).
Proof.
  induction m; intros k v. inversion 1.
  destruct a as [k' v']; simpl in *. intros. destruct (K.eq_dec k k'); intuition eauto. 
Qed.

Lemma dom_in_get : forall m k,
  In k (dom m) -> exists v, get m k = Some v.
Proof.
  induction m. inversion 1.
  destruct a as [k' v']; simpl in *. 
  intro k. destruct (K.eq_dec k k') as [|Heq]; intros. intuition eauto.
  inversion H; eauto; contradict Heq; auto.
Qed.

Lemma get_forallb2' : forall m f P,
  (forall k v, P k v <-> f k v = true) ->
  ((forall k v, get m k = Some v -> P k v)
   <-> forallb2 f m = true).
Proof.
  intros until 0. intro Hpf. unfold forallb2.
  split; intros.

  - (* Case "->". *)
  pose proof (dom_in_get m) as Hd.
  set (d := dom m) in *. clearbody d.

  induction d. reflexivity. simpl. 
  destruct (get m a) eqn:Hget.
  rewrite IHd; auto. assert (f a v = true).
  apply Hpf. eapply H; eauto. rewrite H0. simpl. reflexivity.
  intros. apply Hd. simpl. right. auto.
  
  ecase (Hd a) as [v Hv]; try (left; auto). 
  rewrite Hv in Hget. inversion Hget.

  - (* Case "<-". *)
  pose proof (get_in_dom m _ _ H0) as Hd.
  set (d:=dom m) in *. clearbody d.

  induction d. inversion Hd.
  simpl in H.
  destruct (K.eq_dec a k). subst a. rewrite H0 in H.
  apply Hpf; auto. destruct (f k v); auto. 
  apply IHd. destruct (get m a); try solve [inversion H].
  destruct (f a v0).
  destruct (forallb2' f m d); auto.
  destruct (forallb2' f m d); auto.
  inversion Hd; intuition.
Qed.  

Lemma get_forallb2 : forall m f,
  (forall k v, get m k = Some v -> f k v = true) 
  <-> 
  forallb2 f m = true.
Proof.
  intros. unfold forallb2.
  split; intros.

  - (* Case "->". *)
  pose proof (dom_in_get m) as Hd.
  set (d := dom m) in *. clearbody d.

  induction d. reflexivity. simpl. 
  destruct (get m a) eqn:Hget.
  rewrite H; auto. rewrite IHd; auto. intros.
  apply Hd. simpl. right; auto.
  
  ecase (Hd a) as [v Hv]; try (left; auto). 
  rewrite Hv in Hget. inversion Hget.

  - (* Case "<-". *)
  pose proof (get_in_dom m _ _ H0) as Hd.
  set (d:=dom m) in *. clearbody d.

  induction d. inversion Hd.
  simpl in H.
  destruct (K.eq_dec a k). subst a. rewrite H0 in H.
  destruct (f k v); auto.
  apply IHd.
  destruct (get m a); try solve [inversion H].
  destruct (forallb2' f m d); auto.
  destruct (f a v0); auto.
  inversion Hd; intuition.
Qed.  

End withv.

End ListMap.

(* Types *)

Inductive ty := TBool | TNat. 

(* TODO: Actual Generators? *)
Derive (Arbitrary, Show) for ty.
Instance eq_dec_ty (x y : ty) : Dec (x = y).
constructor; unfold ssrbool.decidable; decide equality.
Defined.

Module AtomMap := ListMap (Atom).

Definition context := @AtomMap.t ty.

Inductive bind_in {A} : @AtomMap.t A -> Atom.t -> A -> Prop :=
  | Bind : forall x Gamma T, AtomMap.get Gamma x = Some T -> bind_in Gamma x T.

Ltac solve_left  := try solve [left; constructor; eauto].
Ltac solve_right := 
  let Contra := fresh "Contra" in
  try solve [right; intro Contra; inversion Contra; subst; clear Contra; eauto; congruence].
Ltac solve_sum := solve_left; solve_right.

Instance dec_bind_in {A : Type} Gamma x (T : A) `{D : forall (x y : A), Dec (x = y)}
  : Dec (bind_in Gamma x T).
Proof. 
constructor; unfold ssrbool.decidable.
destruct (AtomMap.get Gamma x) eqn:Get.       
- destruct (D a T) eqn:Eq; destruct dec; simpl in *; subst;
    solve_sum.
- solve_sum.
Defined.

Definition gen_typed_atom_from_context (Gamma : context) (T : ty) : G (option Atom.t) :=
  oneof (returnGen None) (List.map (fun aT' => returnGen (Some (fst aT'))) 
                                   (List.filter (fun aT' => T = (snd aT')?) Gamma)).

(* Hide for lecture? *)
Instance genST_bind_in (Gamma : context) (T : ty) 
  : GenSuchThat Atom.t (fun x => bind_in Gamma x T) :=
  { arbitraryST := gen_typed_atom_from_context Gamma T }.

(* Too many sigs *)
Definition gen_context (n : nat) : G context := 
  let domain := get_fresh_atoms n [] in
  bindGen (vectorOf n arbitrary) (fun (range : list ty) => 
  returnGen (List.fold_left (fun (m : context) (kv : Atom.t * ty) => 
                               let (k,v) := kv in 
                               AtomMap.set m k v) 
                            (List.combine domain range) AtomMap.empty)).

(* Expressions *)

Inductive exp : Type :=
  | EVar : Atom.t -> exp
  | ENum : nat -> exp
  | EPlus : exp -> exp -> exp
  | EMinus : exp -> exp -> exp
  | EMult : exp -> exp -> exp
  | ETrue : exp
  | EFalse : exp
  | EEq : exp -> exp -> exp
  | ELe : exp -> exp -> exp
  | ENot : exp -> exp
  | EAnd : exp -> exp -> exp.
Derive Show for exp.

Inductive has_type : context -> exp -> ty -> Prop := 
| Ty_Var : forall x T Gamma, bind_in Gamma x T -> has_type Gamma (EVar x) T
| Ty_Num : forall Gamma n, has_type Gamma (ENum n) TNat
| Ty_Plus : forall Gamma e1 e2, has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
                                has_type Gamma (EPlus e1 e2) TNat
| Ty_Minus : forall Gamma e1 e2, has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
                                has_type Gamma (EMinus e1 e2) TNat
| Ty_Mult : forall Gamma e1 e2, has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
                                has_type Gamma (EMult e1 e2) TNat
| Ty_True : forall Gamma, has_type Gamma ETrue TBool
| Ty_False : forall Gamma, has_type Gamma EFalse TBool
| Ty_Eq : forall Gamma e1 e2, has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
                              has_type Gamma (EEq e1 e2) TBool
| Ty_Le : forall Gamma e1 e2, has_type Gamma e1 TNat -> has_type Gamma e2 TNat ->
                              has_type Gamma (ELe e1 e2) TBool
| Ty_Not : forall Gamma e, has_type Gamma e TBool ->
                              has_type Gamma (ENot e) TBool
| Ty_And : forall Gamma e1 e2, has_type Gamma e1 TBool -> has_type Gamma e2 TBool ->
                               has_type Gamma (EAnd e1 e2) TBool.

Import QcDoNotation.
(* This is so pedantic I want to derive it :) *)
Fixpoint gen_exp_typed_sized (size : nat) (Gamma : context) (T : ty) : G (option exp) :=
  let gen_typed_evar := 
      doM! x <- gen_typed_atom_from_context Gamma T;
        returnGen (Some (EVar x)) in
  let base :=
      match T with 
      | TNat  => [ (2, do! n <- arbitrary; returnGen (Some (ENum n)))]
      | TBool => [ (1, returnGen (Some ETrue))
                 ; (1, returnGen (Some EFalse)) ]
      end in 
  let recs size' := 
      match T with 
      | TNat => [ (1, doM! e1 <- gen_exp_typed_sized size' Gamma TNat; 
                      doM! e2 <- gen_exp_typed_sized size' Gamma TNat; 
                      returnGen (Some (EPlus e1 e2))) 
                ; (1, doM! e1 <- gen_exp_typed_sized size' Gamma TNat; 
                      doM! e2 <- gen_exp_typed_sized size' Gamma TNat; 
                      returnGen (Some (EMinus e1 e2))) 
                ; (1, doM! e1 <- gen_exp_typed_sized size' Gamma TNat; 
                      doM! e2 <- gen_exp_typed_sized size' Gamma TNat; 
                      returnGen (Some (EMult e1 e2))) ]
      | TBool => [ (1, doM! e1 <- gen_exp_typed_sized size' Gamma TNat; 
                       doM! e2 <- gen_exp_typed_sized size' Gamma TNat; 
                       returnGen (Some (EEq e1 e2))) 
                 ; (1, doM! e1 <- gen_exp_typed_sized size' Gamma TNat; 
                       doM! e2 <- gen_exp_typed_sized size' Gamma TNat; 
                       returnGen (Some (ELe e1 e2))) 
                 ; (1, doM! e1 <- gen_exp_typed_sized size' Gamma TBool; 
                       returnGen (Some (ENot e1)))
                 ; (1, doM! e1 <- gen_exp_typed_sized size' Gamma TBool; 
                       doM! e2 <- gen_exp_typed_sized size' Gamma TBool; 
                       returnGen (Some (EAnd e1 e2))) ]
      end in
  match size with 
  | O => 
    backtrack ( (1, gen_typed_evar) :: base )
  | S size' => 
    backtrack ( (1, gen_typed_evar) :: (base ++ recs size'))
  end.

Fixpoint shrink_exp_typed (T : ty) (e : exp) : list exp :=
  match e with 
  | EVar _ => 
    match T with 
    | TNat => [ENum 0]
    | TBool => [ETrue ; EFalse]
    end
  | ENum _ => []
  | ETrue => []
  | EFalse => [ETrue]
  | EPlus e1 e2 => 
    e1 :: e2 
       :: (List.map (fun e1' => EPlus e1' e2) (shrink_exp_typed T e1))
       ++ (List.map (fun e2' => EPlus e1 e2') (shrink_exp_typed T e2))
  | EMinus e1 e2 => 
    e1 :: e2 :: (EPlus e1 e2)
       :: (List.map (fun e1' => EMinus e1' e2) (shrink_exp_typed T e1))
       ++ (List.map (fun e2' => EMinus e1 e2') (shrink_exp_typed T e2))
  | EMult e1 e2 => 
    e1 :: e2 :: (EPlus e1 e2)
       :: (List.map (fun e1' => EMult e1' e2) (shrink_exp_typed T e1))
       ++ (List.map (fun e2' => EMult e1 e2') (shrink_exp_typed T e2))
  | EEq e1 e2 => 
    ETrue :: EFalse 
       :: (List.map (fun e1' => EEq e1' e2) (shrink_exp_typed TNat e1))
       ++ (List.map (fun e2' => EEq e1 e2') (shrink_exp_typed TNat e2))
  | ELe e1 e2 => 
    ETrue :: EFalse :: (EEq e1 e2)
       :: (List.map (fun e1' => ELe e1' e2) (shrink_exp_typed TNat e1))
       ++ (List.map (fun e2' => ELe e1 e2') (shrink_exp_typed TNat e2))
  | ENot e => 
    ETrue :: EFalse :: e :: (List.map ENot (shrink_exp_typed T e))
  | EAnd e1 e2 => 
    ETrue :: EFalse :: e1 :: e2 
       :: (List.map (fun e1' => EAnd e1' e2) (shrink_exp_typed TBool e1))
       ++ (List.map (fun e2' => EAnd e1 e2') (shrink_exp_typed TBool e2))

  end.


Ltac solve_inductives Gamma :=
  repeat (match goal with 
      [ IH : forall _ _, _ |- _ ] =>
      let H1 := fresh "H1" in 
      pose proof (IH TNat Gamma) as H1;
      let H2 := fresh "H2" in 
      pose proof (IH TBool Gamma) as H2;
      clear IH;
      destruct H1; destruct H2; solve_sum
    end).

(* Too much automation? *)
Instance dec_has_type (e : exp) (Gamma : context) (T : ty) : Dec (has_type Gamma e T) :=
  { dec := _ }.
Proof with solve_sum.
  (* I need move: *)
  generalize dependent Gamma.
  generalize dependent T.
  induction e; intros T Gamma; unfold ssrbool.decidable;
    try solve [destruct T; solve_sum];
    try solve [destruct T; solve_inductives Gamma].
  (* bind_in case *)
  destruct (dec_bind_in Gamma t T); destruct dec; solve_sum.
Defined.

(* Sanity checks *)
(* Generation sanity check *)
Definition gen_typed_has_type :=
  let num_vars := 4 in
  let top_level_size := 3 in 
  forAll (gen_context num_vars) (fun Gamma =>
  forAll arbitrary (fun T =>                                   
  forAll (gen_exp_typed_sized top_level_size Gamma T) (fun me =>
  match me with 
  | Some e => (has_type Gamma e T)?
  | _ => false (* this should NEVER fail *)
  end))).

QuickChick gen_typed_has_type.

(* Shrinking sanity check *)
Definition shrink_typed_has_type :=
  let num_vars := 4 in
  let top_level_size := 3 in 
  forAll (gen_context num_vars) (fun Gamma =>
  forAll arbitrary (fun T =>                                   
  forAll (gen_exp_typed_sized top_level_size Gamma T) (fun me =>
  match me with 
  | Some e => 
    List.forallb (fun e' => (has_type Gamma e' T)?) (shrink_exp_typed T e)
  | _ => false (* this should NEVER fail *)
  end))).

QuickChick shrink_typed_has_type.


Inductive value := VNat : nat -> value | VBool : bool -> value.

Derive Show for value.
  
Inductive has_type_value : value -> ty -> Prop :=
  | TyVNat  : forall n, has_type_value (VNat  n) TNat
  | TyVBool : forall b, has_type_value (VBool b) TBool.

Instance dec_has_type_value v T : Dec (has_type_value v T).
Proof. constructor; unfold ssrbool.decidable.
destruct v; destruct T; solve_sum.
Defined.

Definition gen_typed_value (T : ty) : G value :=
  match T with 
  | TNat  => do! n <- arbitrary; returnGen (VNat n)
  | TBool => do! b <- arbitrary; returnGen (VBool b)
  end.

Definition state := @AtomMap.t value.

(* Similar structure *)
Inductive typed_state : context -> state -> Prop :=
| TS_Empty : typed_state AtomMap.empty AtomMap.empty
| TS_Elem  : forall x v T st Gamma, 
    has_type_value v T -> typed_state Gamma st ->
    typed_state ((x,T)::Gamma) ((x,v)::st).

Instance dec_typed_state Gamma st : Dec (typed_state Gamma st).
Proof. 
constructor; unfold ssrbool.decidable.
generalize dependent Gamma.
induction st; intros; destruct Gamma; solve_sum.
destruct a as [a v]; destruct p as [a' T].
destruct (Atom.eq_dec a a'); solve_sum.
subst; specialize (IHst Gamma); destruct IHst; solve_sum.
destruct (dec_has_type_value v T); destruct dec; solve_sum.
Defined.

Definition gen_typed_state (Gamma : context) : G state := 
  sequenceGen (List.map (fun '(x, T) =>
                           do! v <- gen_typed_value T; 
                           returnGen (x, v)) Gamma).

(* More monads? :/ *)
(*
Definition bindOption {A B : Type} (m : option A) (k : A -> option B) : option B :=
  match m with 
  | Some a => k a 
  | _ => None 
  end.
Notation "'do!' X <- A ; B" :=
  (bindOption A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).
*)

Fixpoint eval (st : state) (e : exp) : option value :=
  match e with
  | EVar x => AtomMap.get st x
  | ENum n => Some (VNat n)
  | EPlus e1 e2 => 
    match eval st e1, eval st e2 with 
    | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 + n2))
    | _, _ => None
    end
  | EMinus e1 e2 => 
    match eval st e1, eval st e2 with 
    | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 - n2))
    | _, _ => None
    end
  | EMult e1 e2 => 
    match eval st e1, eval st e2 with 
    | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 * n2))
    | _, _ => None
    end
  | ETrue       => Some (VBool true  )
  | EFalse      => Some (VBool false )
  | EEq e1 e2 => 
    match eval st e1, eval st e2 with 
    | Some (VNat n1), Some (VNat n2) => Some (VBool (n1 =? n2))
    | _, _ => None
    end
  | ELe e1 e2 => 
    match eval st e1, eval st e2 with 
    | Some (VNat n1), Some (VNat n2) => Some (VBool (n1 <? n2))
    | _, _ => None
    end
  | ENot e => 
    match eval st e with 
    | Some (VBool b) => Some (VBool (negb b))
    | _ => None
    end
  | EAnd e1 e2  => 
    match eval st e1, eval st e2 with 
    | Some (VBool b1), Some (VBool b2) => Some (VBool (andb b1 b2))
    | _, _ => None
    end
  end.

Definition isNone {A : Type} (m : option A) :=
  match m with 
  | None => true
  | _ => false
  end.

(* Soundness for expressions *)
Conjecture expression_soundness : 
  forall Gamma st e T, typed_state Gamma st -> has_type Gamma e T -> isNone (eval st e) = false.

Definition lift_shrink {A : Type} (shr : A -> list A) (m : option A) : list (option A) :=
  match m with 
  | Some x => List.map Some (shr x)
  | _ => []
  end.

Definition expression_soundness_exec := 
  let num_vars := 4 in 
  let top_level_size := 3 in
  forAll (gen_context num_vars)  (fun Gamma =>
  forAll (gen_typed_state Gamma) (fun st =>
  forAll arbitrary (fun T =>                                    
  forAllShrink (gen_exp_typed_sized 3 Gamma T) (lift_shrink (shrink_exp_typed T)) (fun me => 
  match me with 
  | Some e => negb (isNone (eval st e))
  | _ => false
  end)))).   

QuickChick expression_soundness_exec.

(* Start exercise here *)


Inductive com : Type :=
  | CSkip  : com
  | CAss   : Atom.t -> exp -> com
  | CSeq   : com    -> com -> com
  | CIf    : exp    -> com -> com -> com
  | CWhile : exp    -> com -> com.

Derive Show for com.

(** As usual, we can use a few [Notation] declarations to make things
    more readable.  To avoid conflicts with Coq's built-in notations,
    we keep this light -- in particular, we don't introduce any
    notations for [exps] and [exps] to avoid confusion with the
    numeric and boolean operators we've already defined. *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(* This is so pedantic I want to derive it :) *)
Fixpoint gen_com_typed_sized (size : nat) (Gamma : context) : G (option com) :=
  let assgn := 
                (List.map (fun '(x,T) =>
                             (1, doM! e <- gen_exp_typed_sized size Gamma T;
                                returnGen (Some (CAss x e))))
                          Gamma)
  in 
  let skip :=
      returnGen (Some SKIP) in
  let recs size' := 
      [ (1, doM! c1 <- gen_com_typed_sized size' Gamma;
            doM! c2 <- gen_com_typed_sized size' Gamma;
            returnGen (Some (CSeq c1 c2))) 
      ; (1, doM! c <- gen_com_typed_sized size' Gamma;
            doM! b <- gen_exp_typed_sized size' Gamma TBool;
            returnGen (Some (CWhile b c)))
      ; (1, doM! b <- gen_exp_typed_sized size' Gamma TBool;
            doM! c1 <- gen_com_typed_sized size' Gamma;
            doM! c2 <- gen_com_typed_sized size' Gamma;
            returnGen (Some (CIf b c1 c2)))
      ] in
  match size with 
  | O => backtrack ((1, skip) :: assgn)
  | S size' => backtrack ((1, skip) :: (assgn ++ recs size'))
  end.

Fixpoint shrink_com_typed (Gamma : context) (c : com) : list com := 
  match c with 
  | SKIP => []
  | CAss x e => 
    match AtomMap.get Gamma x with
    | Some T => SKIP :: List.map (fun e' => CAss x e) (shrink_exp_typed T e)
    | _ => []
    end
  | CSeq c1 c2 =>
    c1 :: c2 
       :: (List.map (fun c1' => CSeq c1' c2) (shrink_com_typed Gamma c1))
       ++ (List.map (fun c2' => CSeq c1 c2') (shrink_com_typed Gamma c2))
  | CIf b c1 c2 =>
    c1 :: c2 
       :: (List.map (fun c1' => CIf b c1' c2) (shrink_com_typed Gamma c1))
       ++ (List.map (fun c2' => CIf b c1 c2') (shrink_com_typed Gamma c2))
       ++ (List.map (fun b' => CIf b' c1 c2) (shrink_exp_typed TBool b))
  | CWhile b c =>
    c :: (CIf b c c) 
      :: (List.map (fun b' => CWhile b' c) (shrink_exp_typed TBool b))
      ++ (List.map (fun c' => CWhile b c') (shrink_com_typed Gamma c))
  end.
  
Inductive result := 
| Success : state -> result
| Fail : result 
| OutOfGas : result. 

(* State monad like fuel, or depth-like? *)
Fixpoint ceval (fuel : nat) (st : state) (c : com) : result :=
  match fuel with 
  | O => OutOfGas
  | S fuel' => 
    match c with
    | SKIP =>
        Success st
    | x ::= e =>
        match eval st e with 
        | Some v => Success (AtomMap.set st x v)
        | _ => Fail 
        end
    | c1 ;; c2 =>
        match ceval fuel' st c1 with 
        | Success st' =>  ceval fuel' st' c2 
        (* Bug : On OutOfGas should out of Gas :
        | _ => Fail 
        *)
        | r => r
        end
    | IFB b THEN c1 ELSE c2 FI =>
      match eval st b with 
      | Some (VBool b) =>
        ceval fuel' st (if b then c1 else c2)
      | _ => Fail
      end
    | WHILE b DO c END =>
      match eval st b with 
      | Some (VBool b') =>
        if b' then ceval fuel' st (c;; WHILE b DO c END) else Success st
      | _ => Fail
      end
    end
  end.

Definition isFail r := 
  match r with 
  | Fail => true
  | _ => false
  end.

Conjecture well_typed_state_never_stuck : 
  forall Gamma st, typed_state Gamma st ->
  forall fuel c, isFail (ceval fuel st c) = false.

Definition well_typed_state_never_stuck_exec := 
  let num_vars := 4 in 
  let top_level_size := 5 in
  forAll (gen_context num_vars)  (fun Gamma =>
  forAll (gen_typed_state Gamma) (fun st =>
  forAllShrink arbitrary shrink (fun fuel =>
  forAllShrink (gen_com_typed_sized 3 Gamma) (lift_shrink (shrink_com_typed Gamma)) (fun mc => 
  match mc with 
  | Some c => negb (isFail (ceval fuel st c))
  | _ => false
  end)))).                      

QuickChick well_typed_state_never_stuck_exec.                          
  
(* Unreadable bug? 
QuickChecking well_typed_state_never_stuck_exec
[(1,TBool), (2,TBool), (3,TNat), (4,TBool)]
[(1,VBool false), (2,VBool false), (3,VNat 5), (4,VBool true)]
6
Some CWhile (EAnd (EEq (EPlus (ENum 2) (ENum 3)) (ENum 5)) (ENot EFalse)) (CIf (ELe (EMinus (ENum 2) (EMinus (EVar 3) (EVar 3))) (ENum 1)) (CAss 1 (EVar 4)) (CAss 2 (EVar 1)))
*** Failed after 7 tests and 0 shrinks
*)

(* Really motivates shrinking... 
QuickChecking well_typed_state_never_stuck_exec
[(1,TBool), (2,TBool), (3,TNat), (4,TBool)]
[(1,VBool false), (2,VBool true), (3,VNat 0), (4,VBool false)]
1
Some CSeq CSkip CSkip
*)

(* LEO: Fix in SF: it should be c ;; WHILE ... (double ;) *)
(** In a traditional functional programming language like OCaml or
    Haskell we could add the [WHILE] case as follows:

  Fixpoint ceval_fun (st : state) (c : com) : state :=
    match c with
      ...
      | WHILE b DO c END =>
          if (eval st b)
            then ceval_fun st (c; WHILE b DO c END)
            else st
    end.
*)
  
