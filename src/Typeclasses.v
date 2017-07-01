Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import Classes DependentClasses Checker Show.

Require Import GenLow GenHigh Sets.
Import GenLow GenHigh.

(* TODO: Derive these *)
Instance arbST_eq {A} (a : A) : GenSuchThat A (fun x => x = a) :=
  {| arbitraryST := returnGen (Some a) |}.
Instance arbST_Correct {A} (a : A) 
  : SuchThatCorrect (fun x => x = a) (genST (fun x => x = a)) :=
  {| STComplete := _ ;
     STSound    := _ |}.
Proof.
  - simpl; rewrite semReturn.
    unfold set_incl => ma Hma.
    inversion Hma as [a' [Eq HIn]].
    inversion HIn; subst; auto.
  - simpl; rewrite semReturn.
    unfold set_incl => ma Hma.
    inversion Hma; subst.
    left.
    firstorder.
Defined.

Instance arbST_eq' {A} (a : A) : GenSuchThat A (fun x => a = x) :=
  {| arbitraryST := returnGen (Some a) |}.
Instance arbST_Correct' {A} (a : A) 
  : SuchThatCorrect (fun x => a = x ) (genST (fun x => a = x)) :=
  {| STComplete := _ ;
     STSound    := _ |}.
Proof.
  - simpl; rewrite semReturn.
    unfold set_incl => ma Hma.
    inversion Hma as [a' [Eq HIn]].
    inversion HIn; subst; auto.
  - simpl; rewrite semReturn.
    unfold set_incl => ma Hma.
    inversion Hma; subst.
    left.
    firstorder.
Defined.


(* Typeclass foo *)
Global Instance testSuchThat {A : Type} {pre : A -> Prop} {prop : A -> Type}
       `{Show A} `{GenSuchThatCorrect A (fun x => pre x)}
       `{forall (x : A), Checkable (prop x)} :
  Checkable (forall x, pre x -> prop x) := 
  {| checker f := forAllProof (genST (fun x => pre x)) 
                              (fun mx H => 
                                 (* Leo: Is there a better way to do this? *)
                                 let mx' := mx in 
                                 let Heq := erefl mx' : mx' = mx in
                                 match mx as mx'' return (mx' = mx'' -> Checker) with 
                                 | Some x => fun _ => checker (f x _)
                                 | None => fun _ => checker tt
                                 end Heq) |}.
Proof.
  (* Annoying *)
  assert (Eq : mx = mx') by auto.
  rewrite -Eq in e.
  clear Heq Eq mx'.
  (* End annoying *)
  destruct H1.
  apply STSound in H; subst.
  inversion H as [Hyp | Contra].
  - inversion Hyp as [x' [Pre HIn]].
    inversion HIn; subst; auto.
  - inversion Contra.
Defined.     

Global Instance testSuchThat2_1 {A B : Type} {pre : A -> B -> Prop} {prop : A -> B -> Type}
       `{Show A} `{Show B} `{Arbitrary B}
       `{forall (b : B), GenSuchThat A (fun x => pre x b)}
       `{forall (b : B), SuchThatCorrect (fun x => pre x b) (genST (fun x => pre x b))}
       `{forall (a : A) (b : B), Checkable (prop a b)} :
  Checkable (forall a b , pre a b -> prop a b) :=
  {| checker f := 
       forAllShrink arbitrary shrink (fun b => 
         forAllProof (genST (fun x => pre x b)) 
                     (fun mx H => 
                        (* Leo: Is there a better way to do this? *)
                        let mx' := mx in 
                        let Heq := erefl mx' : mx' = mx in
                        match mx as mx'' return (mx' = mx'' -> Checker) with 
                        | Some x => fun _ => checker (f x b _)
                        | None => fun _ => checker tt
                        end Heq)
                                     ) |}.
Proof.
  (* Annoying *)
  assert (Eq : mx = mx') by auto.
  rewrite -Eq in e.
  clear Heq Eq mx'.
  (* End annoying *)
  destruct (H5 b).
  apply STSound in H; subst.
  inversion H as [Hyp | Contra].
  - inversion Hyp as [x' [Pre HIn]].
    inversion HIn; subst; auto.
  - inversion Contra.
Defined.     

Global Instance testSuchThat2_2 {A B : Type} {pre : A -> B -> Prop} {prop : A -> B -> Type}
       `{Show A} `{Show B} `{Arbitrary A}
       `{forall (a : A), GenSuchThat B (fun x => pre a x)}
       `{forall (a : A), SuchThatCorrect (fun x => pre a x) (genST (fun x => pre a x))}
       `{forall (a : A) (b : B), Checkable (prop a b)} :
  Checkable (forall a b , pre a b -> prop a b) :=
  {| checker f := 
       forAllShrink arbitrary shrink (fun a => 
         forAllProof (genST (fun x => pre a x)) 
                     (fun mx H =>  
                        (* Leo: Is there a better way to do this? *)
                        let mx' := mx in 
                        let Heq := erefl mx' : mx' = mx in
                        match mx as mx'' return (mx' = mx'' -> Checker) with 
                        | Datatypes.Some x => fun _ => checker (f a x _)
                        | Datatypes.None => fun _ => checker tt
                        end Heq)
                                     ) |}.
Proof.
  (* Annoying *)
  assert (Eq : mx = mx') by auto.
  rewrite -Eq in e.
  clear Heq Eq mx'.
  (* End annoying *)
  destruct (H5 a).
  apply STSound in H; subst.
  inversion H as [Hyp | Contra].
  - inversion Hyp as [x' [Pre HIn]].
    inversion HIn; subst; auto.
  - inversion Contra.
Defined.     

Global Instance testSuchThat_swap {A B C : Type} {pre : A -> B -> Prop} 
       {prop : A -> B -> C -> Type}
       `{Checkable (forall a b, pre a b -> forall c, prop a b c)} :
  Checkable (forall a b c, pre a b -> prop a b c) :=
  {| checker f := @checker (forall a b, pre a b -> forall c, prop a b c) _ _ |}. 
Proof. intros; eauto. Defined.

Global Instance GenSuchThatConj {A B : Type} (P : A -> Prop) (Q : B -> Prop)
       `{GenSuchThat A (fun x => P x)}
       `{GenSuchThat B (fun x => Q x)}
       : GenSuchThat (A * B) (fun xy => let (x,y) := xy in P x /\ Q y) :=
  {| arbitraryST := 
       bindGen (genST (fun x => P x)) (fun ma =>
       bindGen (genST (fun x => Q x)) (fun mb =>
       match ma, mb with 
       | Some a, Some b => returnGen (Some (a,b))
       | _, _ => returnGen None
       end)) |}.



(*
Global Instance GenSuchThatConjCorrect {A B : Type} (P : A -> Prop) (Q : B -> Prop)
       `{GA: GenSizedSuchThat A (fun x => P x)}
       `{GB: GenSizedSuchThat B (fun x => Q x)}
       `{SizedSuchThatCorrectSuchThatSizedCorrect A (fun x => P x) (@arbitraryST _ _ GA)}
       `{SuchThatSizeCorrect B (fun x => Q x) (@arbitraryST _ _ GB)} 
  : SuchThatCorrect (fun xy : A * B => let (x,y) := xy in P x /\ Q y) 
                    (@arbitraryST _ (fun xy => let (x,y) := xy : A * B in P x /\ Q y) 
                                  (@GenSuchThatConj A B P Q GA GB)) :=
  {| STComplete := _ ;
     STSound    := _ |}.
Proof.
- simpl. rewrite semBind
  *)


