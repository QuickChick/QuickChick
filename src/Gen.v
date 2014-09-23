Require Import ZArith List ssreflect ssrbool ssrnat.
Require Import Axioms RoseTrees Random AbstractGen.
Import ListNotations.

Set Implicit Arguments.

(* The monad carrier *)
Inductive Gen (A : Type) : Type :=
  | MkGen : (RandomGen -> nat -> A (** RandomGen*)) -> Gen A.

(*
-> extracted to
  | MkGen : (ref RandomGen -> nat -> A) -> Gen A.
*)

Definition fmapG {A B : Type} (f : A -> B) (g : Gen A) : Gen B :=
  match g with
    | MkGen h => MkGen (fun r n => f (h r n))
  end.

(* Functor laws *)

Lemma fmap_id:
  forall A a, (fmapG (@id A) a) = (@id (Gen A) a).
Proof.
  rewrite /fmapG. move => A a. case: a => a //=.
Qed.

Lemma fmap_composition:
  forall A B C (a : Gen A) (f : A -> B) (g : B -> C),
    (fmapG g (fmapG f a)) = (fmapG (fun x => g (f x)) a).
Proof.
  move=> A B C a f g. rewrite /fmapG.
  case: a => //=.
Qed.

Definition returnG {A : Type} (x : A) : Gen A :=
  MkGen (fun _ _ => x).

Definition bindG {A B : Type} (g : Gen A) (k : A -> Gen B) : Gen B :=
  match g with
    | MkGen m =>
      MkGen (fun r n =>
               let (r1,r2) := rndSplit r in
               let '(MkGen m') := k (m r1 n) in
               m' r2 n
            )
  end.

(* Monad laws *)
Lemma left_identity :
  forall {A B} (a : A) (f : A -> Gen B),
    bindG (returnG a) f = f a.
Proof.
  rewrite /bindG /returnG. move => A B a f.
  case: (f a) => a'.
  Abort.

Lemma right_identity :
  forall A (m : Gen A),
    bindG m returnG = m.
Proof.
  rewrite /bindG /returnG. move => A m.
  case: m => a.
  Abort.

Require Import FunctionalExtensionality.
Lemma associativity :
  forall {A B C} (m : Gen A) (f : A -> Gen B) (g : B -> Gen C),
    bindG (bindG m f) g =
    bindG m (fun x =>
    bindG (f x) g).
Proof.
  rewrite /bindG /returnG. move => A B C m f g /=.
  case: m => gen_a.
  Abort.

Definition sizedG {A : Type} (f : nat -> Gen A) : Gen A :=
  MkGen (fun r n => match f n with MkGen m => m r n end).

Definition promoteG {A : Type} (m : Rose (Gen A)) : Gen (Rose A) :=
  MkGen (fun r n => fmapRose (fun g => match g with MkGen m' => m' r n end) m).

Fixpoint rnds (rnd : RandomGen) (n' : nat) : list RandomGen :=
  match n' with
    | O => nil
    | S n'' =>
      let (rnd1, rnd2) := rndSplit rnd in
      cons rnd1 (rnds rnd2 n'')
  end.

Fixpoint createRange (n : nat) (acc : list nat) : list nat :=
  match n with
    | O => List.rev (cons O acc)
    | S n' => createRange n' (cons n acc)
  end.

Definition sample' (A : Type) (g : Gen A) : list A :=
  match g with
    | MkGen m =>
      let rnd := mkRandomGen 0 in
      let l := List.combine (rnds rnd 20) (createRange 20 nil) in
      List.map (fun (p : RandomGen * nat) => let (r,n) := p in m r n) l
  end.

Definition resize {A : Type} (n : nat) (g : Gen A) : Gen A :=
  match g with
    | MkGen m => MkGen (fun r _ => m r n)
  end.

Lemma resize_idempotent: 
  forall {A} (n m: nat) (g: Gen A), 
       resize m (resize n g) = resize n g.
Proof.
  move=> A n m g.
  destruct g. reflexivity. 
Qed. 

(* Does this have a bug or it is something I don't get?
   It seems that it won't do any loop because n will
   match against the first case at the first iteration *)

(* Definition suchThatMaybe {A : Type} (g : Gen A) (p : A -> bool) *)
(* : Gen (option A) := *)
(*   let t := (fix t (n : nat) (k : nat) : Gen (option A) :=  *)
(*               match n with *)
(*                 | O => returnG None *)
(*                 | S n' =>  *)
(*                   bindG (resize (2 * k + n) g)  *)
(*                           (fun x => if p x then returnG (Some x) *)
(*                                     else t n' (S k)) *)
(*               end) in *)
(*   sized (fun x => t 0 (max 1 x)). *)

Definition suchThatMaybeG {A : Type} (g : Gen A) (p : A -> bool)
: Gen (option A) :=
  let t := (fix t (k : nat) (n : nat) : Gen (option A) :=
              match n with
                | O => returnG None
                | S n' =>
                  bindG (resize (2 * k + n) g) (fun x =>
                  if p x then returnG (Some x)
                  else t (S k) n')
              end) in
  sizedG (fun x => t 0 (max 1 x)).

Definition chooseG {A : Type} `{Random A} (range : A * A) : Gen A := 
  MkGen (fun r _ => fst (randomR range r)).

Instance realGen : GenMonad Gen :=
  {
    bindGen := @bindG;
    returnGen := @returnG;
    fmapGen := @fmapG;
    choose := @chooseG;
    sized := @sizedG;
    suchThatMaybe := @suchThatMaybeG;
    promote := @promoteG
  }.
