Require Import AbstractGen.
Require Import List ssreflect ssrbool ssrnat seq.

(* The monad carrier *)
Definition Pred (A : Type) := A -> Prop.

(* Equivalence on sets of outcomes *) 
Definition peq {A} (m1 m2 : Pred A) := 
  forall A, m1 A <-> m2 A.

(* the set of outcomes m1 is a subset of m2 *) 
Definition pincl {A} (m1 m2 : Pred A) :=
  forall A, m1 A -> m2 A.
 
(* The set that is equal to A *) 
Definition all {A} : Pred A := fun _ => True. 
 
Definition bindP {A B} (m : Pred A) (f : A -> Pred B) : Pred B :=
  fun b => exists a, m a /\ f a b.

Definition returnP {A} (a : A) : Pred A :=
  eq a.

Definition fmapP {A B} (f : A -> B) (a : Pred A) : Pred B :=
 bindP a (fun a => 
 returnP (f a)).

(* Monad laws *)
Lemma left_identity : forall {A B} (f : A -> Pred B) (a : A),
  peq (bindP (returnP a) f) (f a).
Proof. compute. firstorder. subst. assumption. Qed.

Lemma right_identity : forall {A} (m: Pred A),  
  peq (bindP m returnP) m. 
Proof. intros. compute. firstorder. subst. assumption. Qed.
  
Lemma associativity : forall {A B C} (m : Pred A) (f : A -> Pred B) 
                             (g : B -> Pred C),
  peq (bindP (bindP m f) g) (bindP m (fun x => bindP (f x) g)).
Proof. intros. compute. firstorder. Qed. 

(* Functor laws *)
Lemma fmap_id: 
  forall A a, peq (fmapP (@id A) a) (@id (Pred A) a).
Proof.
  move => A pa. rewrite /fmapP /peq /bindP /returnP /id.
  move => a. split => [[a' [H1 H2]]| H] //=. by subst.
  by exists a; split.
Qed.
 
Lemma fmap_composition:
  forall A B C (a : Pred A) (f : A -> B) (g : B -> C), 
    peq (fmapP g (fmapP f a)) (fmapP (fun x => g (f x)) a).
Proof.  
  move=> A B C P f g. rewrite /fmapP /peq /bindP /returnP /id. move=> pc.
  split=> [[b [[a [Pa fa]]] Heq]| [a [Pa Heq]]]; subst. 
  + by exists a; split.  
  + exists (f a); split=> //=.
    by exists a; split.
Qed.

(* I don't think that this function will be a part if the common interface as
   Gen cannot implement it *)
Definition suchThat {A} (g : Pred A) (f : A -> bool) : Pred A :=  
  (fun x => g x /\ f x = true).
  (* bindP g (fun x =>  *)
  (* if f x then returnP x else (fun _ => False)). *)

Definition suchThatMaybePred {A} (g : Pred A) (f : A -> bool) 
: Pred (option A) :=  
  fun x => match x with
      | None => True
      | Some y => 
        f y = true /\ g y
    end.
 
Instance PredMonad : GenMonad Pred :=
  {
    bindGen := @bindP;
    returnGen := @returnP;
    fmapGen := @fmapP;
    choose A H p := 
      fun a => 
        (cmp (fst p) a <> Gt) /\
        (cmp (snd p) a <> Lt);
    sized A f := 
      fun a => exists n, f n a;
    suchThatMaybe := @suchThatMaybePred
  }.