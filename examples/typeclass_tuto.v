From Coq Require Import Init.Nat List.
Import ListNotations.

From QuickChick Require Import QuickChick.
Import QcNotation. Import QcDefaultNotation.

Require Import Coq.Strings.Ascii.

Open Scope qc_scope.
Open Scope nat_scope.


(** Regexp Matching *)

(* This example is taken from the Logical Foundations Volume of Software Foundations textbook *) 

Definition string := list ascii.

(* We start with an inductive definion of the regular expression data type *)
Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

(* We can then derive an enumerator for inhabitants of this data type *) 
Derive EnumSized for reg_exp.

(* Prints: EnumSizedreg_exp is defined *)

About EnumSizedreg_exp.

(* EnumSizedreg_exp : forall {T : Type}, Enum T -> EnumSized (reg_exp T) *) 

(* The [EnumSizedreg_exp] definition is a function that for each type
   T that can be enumerated (reflected in the typeclass constrain
   [Enum T]), returns an Instance of the typeclass [EnumSized]. *)

(* Let's look more closely at these two typeclasses.

   First, what is an enumerator?

   The enumerator monad
   --------------------

   Inductive EnumType (A : Type) : Type :=
    MkEnum : (nat -> LazyList A) -> EnumType A

   The type of enumerators is [EnumType] (or for short, just [E]).
   This type encapsulates a function of type [nat -> LazyList A].
   The [nat] parameter is an upper bound for the enumeration process. 
   The return type is a lazy list that contains all inhabitants of
   type A up to the given size.

   The Enum typeclass
   ------------------

   Class Enum (A : Type) : Type := { enum : E A }


   The [Enum] typeclass then is the class of all types that have an enumerator.  


   The EnumSized typeclass
   -----------------------
   The [EnumSized] typeclass is similar.

   Class EnumSized (A : Type) := { enumSized : nat -> E A }.

   The difference is that the enumerators of the EnumSized class have an
   additional [nat] parameter that is commonly used to bound the recursion
   depth. 
   
   From EnumSized to Enum
   ----------------------
   We can go from [EnumSized] to [Enum] using the [sized] combinator
   that internalizes the size parameter of [EnumSized]. Given an
   [EnumSized] instance, we can automatically derive an [Enum]
   instance with typeclass resolution.

*) 

(* After automatically generating the [EnumSized] instance, we can
   generate correctness proofs. To do this proof we first define a
   "set-of-outcomes" semantics for our enumerator.

   In particular, the combinator [semEnumSize], with signature:

   semEnumSize : forall {A : Type}, E A -> nat -> set A

   maps an enumerator of type A to set indexed by a size. This is the
   set of element that can be generated for each value of the internal
   size parameter. We will use this to state properties of enumerators.

   Before generating correctness we need some crucial monotonicity
   properties. 


   Monotonicity in the external size parameter
   --------------------------------------
   First, we prove that the enumerator is monotonic in the external size
   parameter. That is, 
   
   forall s s1 s2 : nat,
   s1 <= s2 -> semProdSize (enumSized s) s1 \subset (enumSized s) s2

   This property is captured by the [SizeMonotonic] typeclass. Again.
   we automatically instances of these typeclass.

*)


Instance EnumSizedreg_exp_SizedMonotonic T {_ : Enum T} :
  SizedMonotonic (@enumSized _ (@EnumSizedreg_exp T _)).
Proof. derive_enum_SizedMonotonic. Qed. 


(* Monotonicity in the internal size parameter
   --------------------------------------
   We also prove that the enumerator is monotonic in the internal size
   parameter. That is, 
   
   forall s s1 s2 : nat,
   s1 <= s2 -> semEnumSize (enumSized s1) s \subset semEnumSize (enumSized s2) s

   This property is captured by the [SizeMonotonic] typeclass. We automatically
   derive instances of this typeclass using our Ltac2 proofscript
   [derive_enum_SizedMonotonic]. 
*) 

Instance EnumSizedreg_exp_SizeMonotonic T `{EnumMonotonic T}:
  forall s, SizeMonotonic (@enumSized _ (@EnumSizedreg_exp T _) s).
Proof. derive_enum_SizeMonotonic. Qed.


(* Correctness
   -----------
   We use the two monotonicity properties to prove correctness.
   For simple enumerators like this one, correctness states:

   { x | exists s s', x \in semEnumSize (enumSized s) s' } <--> [set: A]

   That is, the set of elements that belongs to [semEnumSize (enumSized s) s']
   for some size parameters s (external) and s' (internal), is exactly the set
   of elements of type A (denoted [set: A]). The notation <--> denotes set
   equality.

 *)


Instance EnumSizedreg_expCorrect T `{EnumMonotonicCorrect T}:
  CorrectSized (@enumSized _ EnumSizedreg_exp).
Proof. derive_enum_Correct. Qed.

(* Now that we have seen how enumeration of simple data types works,
   we can move on to enumeration and checking of inductive relations.

   We focus on regular expression matching. 
 *)

Reserved Notation "s =~ re" (at level 80).

Definition app := @app.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(* The following inductive relation holds whenever a string of
   characters drawn from a set [T] matches a regular expression.
 *) 

Inductive exp_match {T: Type} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2 :
      s1 =~ re1 ->
      s2 =~ re2 ->
      s1 ++ s2 =~ (App re1 re2)
  | MUnionL s1 re1 re2 : 
      s1 =~ re1 ->
      s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2 : 
      s2 =~ re2 ->
      s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re : 
      s1 =~ re ->
      s2 =~ (Star re) ->
      s1 ++ s2 =~ (Star re)
  where "s =~ re" := (exp_match s re).

(** Checkers *) 

(* First, we can generate a checker for [exp_match]. *)

Derive DecOpt for (exp_match l e).
(* DecOptexp_match is defined *)

Derive EnumSizedSuchThat for (fun l => exp_match l e). 

About DecOptexp_match.
(* DecOptexp_match :
   forall {T : Type},
     Dec_Eq T ->
     Enum T ->
     forall (l : list T) (e : reg_exp T), DecOpt (l =~ e) *)

(* That is, for all types [T] that have decidable equality and are
   enumerable (this constraint is always present even though the
   checker does now always use it), for all inputs [l] and [e], we can
   decide weather the string [l] matches the regular expression [e].

   Checkers are described with the DecOpt typeclass. 

   The DecOpt typeclass
   --------------------

   Class DecOpt (P : Prop) := { decOpt : nat -> option bool }.

   This typeclass describes [Prop]'s  that have a semi-decision
   procedures of type [nat -> option bool]. The natural number
   is the fuel that bounds the recursion depth of the generated
   procedure. Conceptually, the procedure can decide the validity
   of [Prop]'s whose proof derivation have depth less or equal to
   this number.

 *)

(* We can now prove correctness of the derived checker.

   Monotonicity
   ------------

   As before, we need to show monotonicity. In particular, we show that
   if the validity of a proposition has been decided, then the decision
   will not change by providing more fuel. In particular:

   forall (s1 s2 : nat) (b : bool),
     s1 <= s2 -> decOpt s1 = Some b -> decOpt s2 = Some b


   This is capture by the [DecOptSizeMonotonic] typeclass. As before, an instance
   is derived automatically. 

 *)

Instance DecOptexp_match_monotonic {T} `{_ : Dec_Eq T} `{_ : EnumMonotonic T} (m : list T) n :
  DecOptSizeMonotonic (exp_match m n).
Proof. derive_mon. Qed.

(* Soundness and Completeness
   --------------------------

   Using monotonicity we can prove soundness and completeness.

   Soundness states:

   forall (P : Prop) (H : DecOpt P) (s : nat), decOpt s = Some true -> P

   That is, is [decOpt s] is [true] for some [s], then [P] holds.

   It is captured by the [DecOptSoundPos] typeclass.

   Completeness states:

   forall (P : Prop) (H : DecOpt P), P -> exists s : nat, decOpt s = Some true

   That is, if P holds then there exists some fuel [s] such that [decOpt s] is true.

   Again, we derive these instances automatically. *)


Instance DecOptexp_match_sound {T} `{_ : Dec_Eq T} `{_ : EnumMonotonicCorrect T} (m : list T) n :
  DecOptSoundPos (exp_match m n).
Proof. derive_sound. Qed.

Instance DecOptexp_match_complete {T} `{_ : Dec_Eq T} `{_ : EnumMonotonicCorrect T} (m : list T) n :
  DecOptCompletePos (exp_match m n).
Proof. derive_complete. Qed. 


(* Enumeration for the Eq predicate (TODO move) (required by [exp_match]) *)

Derive EnumSizedSuchThat for (fun n => eq x n).

Instance EnumSizedSuchThateq_SizedMonotonic X {_ : Enum X} {_ : Dec_Eq X} (n : X) :
  SizedMonotonicOptFP (@enumSizeST _ _ (EnumSizedSuchThateq n)).
Proof. derive_enumST_SizedMonotonicFP. Qed.

Instance EnumSizedSuchThateq_SizeMonotonic X `{_ : EnumMonotonic X} {_ : Dec_Eq X} (n : X) :
  forall s, SizeMonotonicOptFP (@enumSizeST _ _ (EnumSizedSuchThateq n) s).
Proof. derive_enumST_SizeMonotonicFP. Qed.

Instance EnumSizedSuchThateq_Correct X `{_ : EnumMonotonicCorrect X} `{_ : Dec_Eq X} (n : X) :
  CorrectSizedST (fun m => eq n m) (@enumSizeST _ _ (EnumSizedSuchThateq n)).
Proof. derive_enumST_Correct. Qed.


(* We can also derive an enumerator that given a regular expression, enumerates
   all strings that match the regular expression.

 *)

Derive EnumSizedSuchThat for (fun l => exp_match l e). 
(* EnumSizedSuchThatexp_match is defined. *)

About EnumSizedSuchThatexp_match.

(*
EnumSizedSuchThatexp_match :
  forall {T : Type},
    Dec_Eq T ->
    Enum T ->
    forall e : reg_exp T, EnumSizedSuchThat (list T) (fun l : list T => l =~ e)
*)

(* For all types [T] that have decidable equality and are enumerable, and for all
   input regular expressions [e], we derive an enumerator.

    The [EnumSizedSuchThat] typeclass
    ---------------------------------

    [EnumSizedSuchThat] is similar to [EnumSized] but it is also parameterized by
    a predicate that the enumerated elements must satisfy.

    Class EnumSizedSuchThat (A : Type) (P : A -> Prop) := { enumSizeST : nat -> E (option A) }

    The type of the enumerator is [nat -> E (option A)]. Again, it has a [nat] parameter
    that bounds the recursion depth. The type of the enumerator is [E (option A)].
    The semantics of [None] in the output of enumerator is that enumeration is not
    complete and there might be more elements that satisfy the predicate.

*)


(* As with the simple enumeration, before deriving correctness, we need to derive
   monotonicity. *)

Instance EnumSizedSuchThatexp_match_SizedMonotonic {T} `{_ : Dec_Eq T} `{_ : EnumMonotonic T} e:
  SizedMonotonicOptFP (@enumSizeST _ _ (EnumSizedSuchThatexp_match e)).
Proof. derive_enumST_SizedMonotonicFP. Qed.

Instance EnumSizedSuchThatexp_match_SizeMonotonic {T} `{_ : Dec_Eq T} `{_ : EnumMonotonic T} e :
  forall s, SizeMonotonicOptFP (@enumSizeST _ _ (EnumSizedSuchThatexp_match e) s).
Proof. derive_enumST_SizeMonotonicFP. Qed.

(* Correctness
   -----------

  Correctness of enumerators states that all elements that are
  generated satisfy the predicate (soundness) and that all elements
  that satisfy the predicate can be enumerated. Using the set of outcomes
  semantics, this can be states as:

   { x | exists s s',  Some x \in semEnumSize (enumSizeST s) s' } <--> { x | P x }

   This is captured by the [CorrectSizedST] typeclass. We derive this instance automatically.

*)

Instance EnumSizedSuchThatexp_match_Correct {T} `{_ : Dec_Eq T} `{_ : EnumMonotonicCorrect T} e :
  CorrectSizedST (fun l => exp_match l e)  (@enumSizeST _ _ (EnumSizedSuchThatexp_match e)).
Proof. derive_enumST_Correct. Qed.


(* Νote that we can also generate a enumerator for all the regular
   expressions that can match a string (i.e., the input is the string
   and the output is the regular expression)
 *)

Derive EnumSizedSuchThat for (fun e => exp_match l e). 
