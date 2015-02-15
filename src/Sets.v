Require Import ssreflect ssrfun ssrbool ssrnat.
Require Import Classes.RelationClasses Classes.Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* There are similar definitions in the Ensembles library (Included
   and Same_set); set_eq is not exactly the same as Same_set though
   (only logically equivalent). *)

Definition set T := T -> Prop.

Notation "x \in A" := (A x) (at level 70, only parsing) : set_scope.

Definition set_eq {A} (m1 m2 : set A) :=
  forall (a : A), m1 a <-> m2 a.

Global Instance : forall T, Equivalence (@set_eq T).
Proof.
move=> T; constructor=> // [A B eqAB | A B C eqAB eqBC] x.
  by split=> /eqAB.
by split=> [/eqAB/eqBC|/eqBC/eqAB].
Qed.

Infix "<-->" := set_eq (at level 70, no associativity) : set_scope.

Definition set_incl {A} (m1 m2 : set A) :=
  forall (a : A), m1 a -> m2 a.

Infix "\subset" := set_incl (at level 70, no associativity) : set_scope.

Open Scope set_scope.

Notation "[ 'set' x : T | P ]" := (fun x : T => P)
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]", only parsing) : set_scope.

Definition setT {T} := [set _ : T | True].

Notation "[ 'set' : T ]" := (@setT T)
  (at level 0, format "[ 'set' :  T ]") : set_scope.

Section setOpsDef.

Context {T U : Type}.
Implicit Types (a x : T) (A B : set T).

Definition set1 a := eq a.

Definition setU A B := [set x | x \in A \/ x \in B].

Definition setI A B := [set x | x \in A /\ x \in B].

Definition codom (f : T -> U) := [set y | exists x, f x = y].

Definition bigcup A (F : T -> set U) := [set x | exists i, i \in A /\ x \in F i].

End setOpsDef.

Definition imset {T U} (f : T -> U) A := bigcup A (fun x => set1 (f x)).

Definition setX T U (A : set T) (B : set U) := [set x | x.1 \in A /\ x.2 \in B].

Definition imset2 T U V (f : T -> U -> V) A1 A2 :=
  imset (prod_curry f) (setX A1 A2).

Definition codom2 T U V (f : T -> U -> V) := codom (prod_curry f).

Notation "[ 'set' a ]" := (set1 a)
  (at level 0, a at level 99, format "[ 'set'  a ]") : set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)]
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]") : set_scope.

Notation "A :|: B" := (setU A B) (at level 52, left associativity) : set_scope.
Notation "a |: A" := ([set a] :|: A) (at level 52, left associativity) : set_scope.

Notation "A :&: B" := (setI A B) (at level 48, left associativity) : set_scope.

Notation "f @: A" := (imset f A) (at level 24) : set_scope.

Notation "f @2: ( A , B )" := (imset2 f A B)
  (at level 24, format "f  @2:  ( A ,  B )") : set_scope.

Notation "\bigcup_ i F" := (bigcup setT (fun i => F))
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcup_ i '/  '  F ']'") : set_scope.
Notation "\bigcup_ ( i : t ) F" := (bigcup (@setT t) (fun i => F))
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i   :  t ) '/  '  F ']'", only parsing) : set_scope.
Notation "\bigcup_ ( i 'in' A ) F" := (bigcup A (fun i => F))
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  'in'  A ) '/  '  F ']'") : set_scope.

Lemma subset_eqP T (A B : set T) : (A <--> B) <-> (A \subset B /\ B \subset A).
Proof.
split; first by move=> eqAB; split=> a; rewrite (eqAB a).
by case=> subAB subBA a; split; [apply: subAB | apply:subBA].
Qed.

Lemma imsetT T U (f : T -> U) : f @: setT <--> codom f.
Proof.
move=> y; split; first by case=> x [_ fx]; exists x.
by case=> x fx; exists x.
Qed.

Lemma setXT T U : setX [set: T] [set: U] <--> [set: T * U].
Proof. by case. Qed.

Instance set_incl_Proper T U :
  Proper (@eq (T -> U) ==> set_incl ==> set_incl) imset.
Proof.
by move=> f ? <- A B subAB y [x [Ax fx]]; exists x; split=> //; apply: subAB.
Qed.

Instance set_eq_Proper T U : Proper (@eq (T -> U) ==> set_eq ==> set_eq) imset.
Proof.
by move=> f ? <- A B /subset_eqP[subAB subBA] y; split; apply: set_incl_Proper.
Qed.

Lemma bigcup_set1 T U (F : T -> set U) y :
  \bigcup_(x in [set y]) F x <--> F y.
Proof. by move=> t; split=> [[y' [<-]] | Fyt] //; exists y. Qed.

Lemma bigcup_const A B (P : set B) : inhabited A -> (\bigcup_(_ : A) P) <--> P.
Proof. by case=> a x; split=> [[?] []|Px] //; exists a. Qed.

Lemma bigcupC T U V A B (F : T -> U -> set V) :
  \bigcup_(i in A) \bigcup_(j in B) F i j <-->
  \bigcup_(j in B) \bigcup_(i in A) F i j.
Proof.
wlog suff: T U A B F / \bigcup_(i in A) \bigcup_(j in B) F i j \subset
   \bigcup_(j in B) \bigcup_(i in A) F i j.
  by move=> sub; apply/subset_eqP; split; apply: sub.
by move=> x [i [Ai [j [Bj ?]]]]; exists j; split=> //; exists i.
Qed.

Lemma incl_bigcupr T U A (F : T -> set U) G : (forall x, F x \subset G x) ->
  \bigcup_(x in A) F x \subset \bigcup_(x in A) G x.
Proof.
by move=> subFG t [x [Ax Fxt]]; exists x; split=> //; apply: subFG.
Qed.

Lemma eq_bigcupr T U A (F : T -> set U) G : (forall x, F x <--> G x) ->
  \bigcup_(x in A) F x <--> \bigcup_(x in A) G x.
Proof.
by move=> eq_FG t; split; apply: incl_bigcupr => {t} x t; rewrite (eq_FG x t).
Qed.

Lemma incl_bigcupl T U A B (F : T -> set U) : A \subset B ->
  \bigcup_(x in A) F x \subset \bigcup_(x in B) F x.
Proof.
by move=> subAB t [x [Ax Fxt]]; exists x; split=> //; apply: subAB.
Qed.

Global Instance eq_bigcupl T U : Proper (set_eq ==> @eq (T -> set U) ==> set_eq) bigcup.
Proof.
by move=> A B /subset_eqP[? ?] F G <- {G}; split; apply: incl_bigcupl.
Qed.

Lemma bigcup_flatten T U V A (F : T -> set U) (G : U -> set V) :
  \bigcup_(x in \bigcup_(y in A) F y) G x <-->
  \bigcup_(y in A) \bigcup_(x in F y) G x.
Proof.
move=> t; split=> [[x [[y [Ay Fyx]] Gxt]] | [y [Ay [x [Fyx Gxt]]]]].
  by exists y; split=> //; exists x.
by exists x; split=> //; exists y.
Qed.

Lemma codomE T U (f : T -> U) : codom f <--> \bigcup_x [set f x].
Proof. by move=> y; split=> [[x fx]|[x [_ fx]]]; exists x. Qed.

Lemma codom_id T : codom id <--> [set: T].
Proof. by move=> x; split=> // _; exists x. Qed.

Lemma codom_const A B (x : B) : inhabited A ->
  codom (fun _ : A => x) <--> [set x].
Proof. by move=> ?; rewrite codomE bigcup_const. Qed.

Lemma imset_comp T U V (f : U -> T) (g : V -> U) A :
  (f \o g) @: A <--> f @: (g @: A).
Proof.
by rewrite /imset bigcup_flatten; apply: eq_bigcupr => x; rewrite bigcup_set1.
Qed.

Lemma codom_comp T U V (f : U -> T) (g : V -> U) :
  codom (f \o g) <--> f @: (codom g).
Proof. by rewrite -imsetT imset_comp imsetT. Qed.

Lemma curry_imset2l T U V (f : T -> U -> V) A1 A2 :
  f @2: (A1, A2) <--> \bigcup_(x1 in A1) f x1 @: A2.
Proof.
move=> a; split.
  by case=> [[x1 x2] [[/= Ax1 Ax2] fx]]; exists x1; split=> //; exists x2.
by case=> [x1 [Ax1 [x2 [Ax2 fx]]]]; exists (x1,x2).
Qed.

Lemma curry_imset2r T U V (f : T -> U -> V) A1 A2 :
  f @2: (A1, A2) <--> \bigcup_(x2 in A2) f^~ x2 @: A1.
Proof. by rewrite curry_imset2l bigcupC. Qed.

Lemma curry_codom2l T U V (f : T -> U -> V) :
  codom (prod_curry f) <--> \bigcup_x1 codom (f x1).
Proof.
rewrite -imsetT -setXT -/(imset2 f _ _) curry_imset2l.
by apply: eq_bigcupr => x; rewrite imsetT.
Qed.

Lemma imset_bigcup T U V (f : U -> V) A (F : T -> set U) :
  (f @: \bigcup_(x in A) (F x)) <--> \bigcup_(x in A) f @: F x.
Proof. by rewrite /imset bigcup_flatten. Qed.

Lemma bigcup_imset T U V (f : T -> U) A (F : U -> set V) :
  \bigcup_(y in f @: A) (F y) <--> \bigcup_(x in A) F (f x).
Proof.
by rewrite bigcup_flatten; apply: eq_bigcupr => x; rewrite bigcup_set1.
Qed.

Lemma bigcup_codom T U V (f : T -> U) (F : U -> set V) :
  \bigcup_(y in codom f) (F y) <--> \bigcup_x F (f x).
Proof. by rewrite -imsetT bigcup_imset. Qed.

Lemma coverE T : \bigcup_x [set x] <--> [set: T].
Proof. by rewrite -codomE codom_id. Qed.