From Coq Require Import List Bool Arith.

From QuickChick Require Import QuickChick LazyList Enumerators.

Import ListNotations.

(* Port of the executable cases in examples/other/DependentTest.v.

   Assertions concern results, not the old engine's generated term shape. *)

Inductive Foo :=
| Foo1 : Foo 
| Foo2 : Foo -> Foo
| Foo3 : nat -> Foo -> Foo.

QuickChick Derive (Arbitrary, EnumSized, Show) for Foo.
#[local] Instance foo_dec (x y : Foo) : Dec (x = y).
Proof. dec_eq. Defined.

Inductive goodFoo : nat -> Foo -> Prop :=
| GoodFoo : forall n foo,  goodFoo n foo.

QuickChick Derive Checker for (goodFoo n foo).
QuickChick Derive Generator for (fun foo => goodFoo n foo).
QuickChick Derive Enumerator for (fun foo => goodFoo n foo).

Inductive goodFooUnif : nat -> Foo -> Prop := 
| GoodUnif : forall n, goodFooUnif n Foo1.

QuickChick Derive Checker for (goodFooUnif n foo).
QuickChick Derive Generator for (fun foo => goodFooUnif n foo).
QuickChick Derive Enumerator for (fun foo => goodFooUnif n foo).

Inductive goodFooCombo : nat -> Foo -> Prop :=
| GoodCombo : forall n foo, goodFooCombo n (Foo2 foo).

QuickChick Derive Checker for (goodFooCombo n foo).
QuickChick Derive Generator for (fun foo => goodFooCombo n foo).
QuickChick Derive Enumerator for (fun foo => goodFooCombo n foo).

Inductive goodFooMatch : nat -> Foo -> Prop := 
| GoodMatch : goodFooMatch 0 Foo1.

QuickChick Derive Checker for (goodFooMatch n foo).
QuickChick Derive Generator for (fun foo => goodFooMatch n foo).
QuickChick Derive Enumerator for (fun foo => goodFooMatch n foo).

Inductive goodFooRec : nat -> Foo -> Prop :=
| GoodRecBase : forall n, goodFooRec n Foo1
| GoodRec : forall n foo, goodFooRec 0 foo -> goodFooRec n (Foo2 foo).

QuickChick Derive Checker for (goodFooRec n foo).
QuickChick Derive Generator for (fun foo => goodFooRec n foo).
QuickChick Derive Enumerator for (fun foo => goodFooRec n foo).

Inductive goodFooPrec : nat -> Foo -> Prop :=
| GoodPrecBase : forall n, goodFooPrec n Foo1
| GoodPrec : forall n foo, goodFooPrec 0 Foo1 -> goodFooPrec n foo.

QuickChick Derive Checker for (goodFooPrec n foo).
QuickChick Derive Generator for (fun foo => goodFooPrec n foo).
QuickChick Derive Enumerator for (fun foo => goodFooPrec n foo).

Inductive goodFooNarrow : nat -> Foo -> Prop :=
| GoodNarrowBase : forall n, goodFooNarrow n Foo1
| GoodNarrow : forall n foo, goodFooNarrow 0 foo -> 
                        goodFooNarrow 1 foo -> 
                        goodFooNarrow n foo.

QuickChick Derive Checker for (goodFooNarrow n foo).
QuickChick Derive Generator for (fun foo => goodFooNarrow n foo).
QuickChick Derive Enumerator for (fun foo => goodFooNarrow n foo).

Inductive goodFooNL : nat -> Foo -> Foo -> Prop :=
| GoodNL : forall n foo, goodFooNL n (Foo2 foo) foo.

Definition addFoo2 (x : Foo) := Foo2 x.

QuickChick Derive Checker for (goodFooNL n m foo).
QuickChick Derive Generator for (fun foo => goodFooNL n m foo).
QuickChick Derive Enumerator for (fun foo => goodFooNL n m foo).

Inductive goodFun : Foo -> Prop :=
| GoodFun : forall (n : nat) (a : Foo), goodFooPrec n (addFoo2 a) ->
                                        goodFun a.

QuickChick Derive Checker for (goodFun a).
QuickChick Derive Generator for (fun a => goodFun a).
QuickChick Derive Enumerator for (fun a => goodFun a).

Inductive Foo_and : (bool * bool) -> bool -> Prop :=
  | Foo_andtt : Foo_and (true, true) true.

QuickChick Derive Generator for (fun p => Foo_and p b).
QuickChick Derive Enumerator for (fun p => Foo_and p b).

Inductive Foo_rel : nat -> bool -> Prop :=
  | R1 : forall n,
       Foo_rel n true
  | R2' : forall a1 l1 a2 l2 l,
       Foo_and (l1, l2) l ->
       Foo_rel a1 l1 ->
       Foo_rel a2 l2 ->
       Foo_rel a1 l.

QuickChick Derive Generator for (fun n => Foo_rel n b).
QuickChick Derive Enumerator for (fun n => Foo_rel n b).


(* Bound observations to twelve lazy results: this is a regression sample,
   not a completeness proof. Forcing whole recursive enumerations is costly. *)
Definition results {A} (P : A -> Prop) `{EnumSizedSuchThat A P} fuel :=
  LazyList_to_list (lazy_take 12 (Enumerators.run (enumSizeST (P := P) fuel) fuel)).
Definition successful {A} (xs : list (option A)) :=
  flat_map (fun x => match x with Some a => [a] | None => [] end) xs.
Definition isFoo1 f := match f with Foo1 => true | _ => false end.
Definition isFoo2 f := match f with Foo2 _ => true | _ => false end.
Example unification_output : successful (results (fun foo => goodFooUnif 7 foo) 2) = [Foo1].
Proof. lazy. reflexivity. Qed.
Example matching_input : successful (results (fun foo => goodFooMatch 0 foo) 2) = [Foo1].
Proof. lazy. reflexivity. Qed.
Example incompatible_input : successful (results (fun foo => goodFooMatch 1 foo) 2) = [].
Proof. lazy. reflexivity. Qed.
Example constructed_outputs :
  forallb isFoo2 (successful (results (fun foo => goodFooCombo 3 foo) 2)) = true /\
  existsb isFoo2 (successful (results (fun foo => goodFooCombo 3 foo) 2)) = true.
Proof. lazy. split; reflexivity. Qed.
Example recursive_outputs :
  existsb isFoo2 (successful (results (fun foo => goodFooRec 3 foo) 2)) = true.
Proof. lazy. reflexivity. Qed.
Example narrowing_outputs :
  forallb isFoo1 (successful (results (fun foo => goodFooNarrow 3 foo) 2)) = true /\
  existsb isFoo1 (successful (results (fun foo => goodFooNarrow 3 foo) 2)) = true.
Proof. lazy. split; reflexivity. Qed.
Example nonlinear_accepts : decOpt (P := goodFooNL 3 (Foo2 Foo1) Foo1) 3 = Some true.
Proof. lazy. reflexivity. Qed.
Example nonlinear_rejects : decOpt (P := goodFooNL 3 Foo1 Foo1) 3 = Some false.
Proof. lazy. reflexivity. Qed.
Example pair_output : successful (results (fun p => Foo_and p true) 2) = [(true,true)].
Proof. lazy. reflexivity. Qed.
Example pair_incompatible : successful (results (fun p => Foo_and p false) 2) = [].
Proof. lazy. reflexivity. Qed.

(* Added features: fixed/repeated inputs and reordered outputs. *)
Inductive successor : nat -> nat -> Prop := Next n : successor n (S n).
QuickChick Derive Checker for (successor 2 y).
QuickChick Derive Checker for (successor x x).
QuickChick Derive Generator for (fun '(y,x) => successor x y).
QuickChick Derive Enumerator for (fun p => let '(y,x) := p in successor x y).
Example fixed_accepts : decOpt (P := successor 2 3) 2 = Some true.
Proof. lazy. reflexivity. Qed.
Example repeated_rejects : decOpt (P := successor 2 2) 2 = Some false.
Proof. lazy. reflexivity. Qed.
Example reordered_results :
  forallb (fun p => Nat.eqb (fst p) (S (snd p)))
    (successful (results (fun '(y,x) => successor x y) 2)) = true /\
  existsb (fun p => Nat.eqb (fst p) (S (snd p)))
    (successful (results (fun '(y,x) => successor x y) 2)) = true.
Proof. lazy. split; reflexivity. Qed.

(* A parameterized family was commented out in the original suite. *)
Inductive Bar (A B : Type) :=
| Bar1 : A -> Bar A B
| Bar2 : Bar A B -> Bar A B
| Bar3 : A -> B -> Bar A B -> Bar A B -> Bar A B.
Arguments Bar1 {A B} _.
Arguments Bar2 {A B} _.
Arguments Bar3 {A B} _ _ _ _.
QuickChick Derive (GenSized, EnumSized) for Bar.
Inductive goodBar {A B : Type} (n : nat) : Bar A B -> Prop :=
| GoodBar1 : forall a, goodBar n (Bar1 a)
| GoodBar2 : forall bar, goodBar 0 bar -> goodBar n (Bar2 bar)
| GoodBar3 : forall a b bar, goodBar n bar -> goodBar n (Bar3 a b (Bar1 a) bar).
QuickChick Derive Generator for (fun bar => @goodBar A B n bar).
QuickChick Derive Enumerator for (fun bar => @goodBar A B n bar).
Definition polymorphic_bar {A B : Type} `{Gen A} `{Gen B} :
  GenSizedSuchThat (Bar A B) (fun bar => goodBar 2 bar) := _.
Example parameterized_has_results :
  existsb (fun _ => true)
    (successful (results (fun bar : Bar bool bool => goodBar 2 bar) 1)) = true.
Proof. lazy. reflexivity. Qed.

(* The former unused-variable soundness regression: a False premise must
   never be dropped. Supply an honest inconclusive checker, not an admitted
   generator of False. Every sampled finite result prefix must be empty. *)
Inductive impossible : Foo -> Prop := Impossible : False -> impossible Foo1.
#[local] Instance false_checker : DecOpt False := {| decOpt := fun _ => Some false |}.
QuickChick Derive Generator for (fun foo => impossible foo).
QuickChick Derive Enumerator for (fun foo => impossible foo).
Example impossible_has_no_results :
  successful (results (fun foo => impossible foo) 2) = [].
Proof. lazy. reflexivity. Qed.

(* Old reverse mode and function-valued premise inputs. *)
QuickChick Derive Generator for (fun n => goodFooPrec n x).
QuickChick Derive Enumerator for (fun n => goodFooPrec n x).
Example reverse_mode_has_results :
  existsb (fun _ => true) (successful (results (fun n => goodFooPrec n Foo1) 2)) = true.
Proof. lazy. reflexivity. Qed.
Example function_premise_accepts : decOpt (P := goodFun Foo1) 4 = Some true.
Proof. lazy. reflexivity. Qed.

(* Added feature: reject malformed output requests explicitly. *)
Fail QuickChick Derive Generator for (fun x => successor x x).
Fail QuickChick Derive Enumerator for (fun x => successor (S x) 3).

(* Exercise random generators as well as enumeration. Each test compares
   successful generated values to an independent structural specification.
   Enumerated witnesses above keep the corresponding checks nonvacuous. *)
Extract Constant defNumTests => "20".
QuickChick (forAll (@arbitrarySizeST _ (fun foo => goodFooCombo 3 foo) _ 2)
  (fun o => match o with Some f => isFoo2 f | None => true end)).
QuickChick (forAll (@arbitrarySizeST _ (fun '(y,x) => successor x y) _ 2)
  (fun o => match o with Some (y,x) => Nat.eqb y (S x) | None => true end)).

Example shrink_contains_child :
  existsb isFoo1 (shrink (Foo2 Foo1)) = true.
Proof. lazy. reflexivity. Qed.
Example unrestricted_has_results :
  existsb (fun _ => true) (successful (results (fun foo => goodFoo 3 foo) 0)) = true.
Proof. lazy. reflexivity. Qed.
Example premise_accepts : decOpt (P := goodFooPrec 3 (Foo2 Foo1)) 3 = Some true.
Proof. lazy. reflexivity. Qed.
Example recursive_rejects : decOpt (P := goodFooRec 3 (Foo3 0 Foo1)) 3 = Some false.
Proof. lazy. reflexivity. Qed.

(* Equality and shared-variable output: retain the original first case. *)
QuickChick Derive Generator for (fun x : bool => x = y).
QuickChick Derive Enumerator for (fun x : bool => x = y).
Example equality_output :
  successful (results (fun x : bool => x = true) 1) = [true].
Proof. lazy. reflexivity. Qed.
Example nonlinear_output :
  successful (results (fun foo => goodFooNL 3 (Foo2 Foo1) foo) 2) = [Foo1].
Proof. lazy. reflexivity. Qed.
Example compound_relation_has_results :
  existsb (fun _ => true) (successful (results (fun n => Foo_rel n true) 1)) = true.
Proof. lazy. reflexivity. Qed.
