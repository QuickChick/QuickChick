Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Omega.
Local Open Scope string.

(* ################################################################# *)
(** * Basics *)

(** ** First Example: The [Show] Typeclass *)

(* Motivation: Need to be able to test lots of different things for
   equality...

     - eqb : A -> A -> bool

   Similar examples:
     - show : A -> String
     - sort : list A -> list A
     - + : A -> A -> A
     - serialize : A -> BitString
     - hash : A -> Int
     - etc., etc.

   Coq adopts (and adapts) Haskell's notion of _typeclasses_ for this.

   Remark for newcomers: the name "typeclasses" may sound a bit like
   "classes" from OOP.  But this is misleading.  A better analogy is
   actually with _interfaces_ from languages like Java.  But best of
   all is to set aside OO preconceptions and try to approach the
   situation with an open mind. *)

(* Class declaration: *)
Class Eq A :=
  {
    eqb: A -> A -> bool;
  }.

Check Eq.  
(* 
==>
Eq
     : Type -> Type
*)

(* An instance declaration: *)
Instance eqBool : Eq bool :=
  {|
    eqb := fun (b c : bool) => if b then c else negb c
  |}.

(* Another: *)
Instance eqNat : Eq nat :=
  {|
    eqb := beq_nat
  |}.

(* Exercise: Write an eq instance for pairs of a nat and a bool. *)

(* We can define functions that use overloaded functions from 
   instances like this: *)
Definition oddManOut {X : Type} {Eq X} (a b c : X) : X :=
  if eqb a b then c
  else if eqb a c then b
  else a.                         

Compute (oddManOut 2 1 2).

(* Recommended exercise: What happens if we forget the class
   constraint?  Try deleting it and see what happens.  Do you
   understand why? *)

(* Another useful typeclass... *)
Class Show A : Type :=
  {
    show : A -> string
  }.

Instance showBool : Show bool :=
  {|
    show := fun b:bool => if b then "true" else "false"
  |}.

Definition natToDigit (n : nat) : string :=
  match n with
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
    | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end.

Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := (natToDigit (n mod 10)) ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string :=
  writeNatAux n n "".

Instance showNat : Show nat :=
  {|
    show := string_of_nat
  |}.

Compute (show 42).

Instance showString : Show string :=
  {|
    show := fun s:string => """" ++ s ++ """"
  |}.

Compute (show true).

(* ---------------------------------------------------------------- *)
(** Implicit Generalization *)

(* Here, [`{Eq A}] essentially means the same as [{_ : Eq A}].  The
   opening tick tells Coq to perform "implicit generalization."

   Here's what the Coq reference manual says:

      Implicit generalization is an automatic elaboration of a
      statement with free variables into a closed statement where
      these variables are quantified explicitly. Implicit
      generalization is done inside binders starting with a ` and
      terms delimited by `{ } and `( ), always introducing maximally
      inserted implicit arguments for the generalized
      variables. Inside implicit generalization delimiters, free
      variables in the current context are automatically quantified
      using a product or a lambda abstraction to generate a closed
      term. *)

(* For example: *)
Generalizable Variables x y.
(* (By default, ordinary variables don't behave this way, to avoid
   puzzling behavior in case of typos.) *)

Definition weird1 := `(x + y).
Print weird1.

Lemma weird2 : `(x + y = y + x).
Proof. intros. omega. Qed.

Print oddManOut.

Definition oddManOut' {X : Type} {_ : Eq X} (a b c : X) : X :=
  if eqb a b then c
  else if eqb a c then b
  else a.                         

(* TODO: Now explain this:

Definition oddManOut {X : Type} {Eq X} (a b c : X) : X :=
  if eqb a b then c
  else if eqb a c then b
  else a.                         

====>
    Error: Unable to satisfy the following constraints:
    UNDEFINED EVARS:
     ?X12==[X |- Type] (type of Eq) {?T}
     ?X15==[X0 Eq X a b c |- Eq X] (parameter Eq of @eqb) {?Eq}
     ?X17==[X0 Eq X a b c |- Eq X] (parameter Eq of @eqb) {?Eq0}
*)

(* This may seem like a lot of trouble just to avoid writing a _!  Why
   is it useful?

   Matthieu makes the point that binding super-classes is supported by
   implicit generalization using this example:

    Program Definition div2 ‘{Frac α} (a : α) := div a (1 + 1). ⇒
    Definition div2 {α} {N : Num α} {Frac α N} (a : α) := ...

    ___

    Also, substructures become subinstances: Class Monoid A := { monop
    : A → A → A ; ... } ClassGroupA:={grp mon: MonoidA;...} Instance
    grp mon ‘{Group A} : Monoid A. Definition foo ‘{Group A} (x : A) :
    A := monop x x.  Similar to the existing Structures based on
    coercive subtyping.

From the reference manual:

  However, the generalizing binders should be used instead as they
  have particular support for type classes:
      - They automatically set the maximally implicit status for type
        class arguments, making derived functions as easy to use as
        class methods. In the example above, A and eqa should be set
        maximally implicit.
      - They support implicit quantification on partially applied type
        classes (§2.7.19). Any argument not given as part of a type
        class binder will be automatically generalized.
      - They also support implicit quantification on
        superclasses (§20.5.1)
*)

(* ---------------------------------------------------------------- *)
(** Internals *)

(* Explain briefly what a typeclass actually translates
   into.  (Explain Coq records en passant.) *)

(* Explain the output!  Notice that it's basically just a record type. *)
Print Eq.
(* ===>
     Record Eq (A : Type) : Type := Build_Eq { eqb : A -> A -> bool }
*)

Check eqb.  
(* EXPLAIN:
==> 
eqb
     : ?A -> ?A -> bool
where
?A : [ |- Type] 
?Eq : [ |- Eq ?A] 
*)

(* Recommended exercise: Reminder of how Coq displays implicit parameters... *)
Definition foo {A : Type} (a : A) : A := a.
Check foo.
(* ===>
     foo
          : ?A -> ?A
     where
     ?A : [ |- Type] 
*)

Print eqBool.
(* ==> 
eqBool = {| eqb := fun b c : bool => if b then c else negb c |}
     : Eq bool
*)

Print eqb.
(* ==>
     eqb = 
     fun (A : Type) (Eq0 : Eq A) => let (eqb) := Eq0 in eqb
          : forall A : Type, Eq A -> A -> A -> bool

     Arguments A, Eq are implicit and maximally inserted
     Argument scopes are [type_scope _ _ _]
 *)

Check (@eqb).
(* ==>
    @eqb
       : forall A : Type, Eq A -> A -> A -> bool
*)

(* Instance inference... 

    fun (x y : bool) => eqb x y 
    ===>   { Implicit arguments }
    fun (x y : bool) => @eqb _ _ x y
    ===>   { Typing }
    fun (x y : bool) => @eqb (?A : Type) (?eq : Eq?A) x y 
    ===>   { Unification }
    fun (x y : bool) => @eqb bool (?eq : Eq bool) x y 
    ===>   { Proof search for Eq bool returns Eq bool }
    fun (x y : bool) => @eqb bool (eqBool : Eq bool) x y 
*)

(* For purposes of instance inference, it doesn't matter whether
   hypotheses are explicit or inferred.  So, for example, one could
   just as well write this: *)

Definition oddManOut'' {X : Type} (_ : Eq X) (a b c : X) : X :=
  if eqb a b then c
  else if eqb a c then b
  else a.                         

(* However, if we define it this way, then applying the function is
   going to be clunky: 

Check (oddManOut'' 1 2 1).
===>
   Error: The term "1" has type "nat" while it is expected to have type "Eq ?X".
*)

Check (oddManOut'' eqNat 1 2 1).

(*
Proof-search tactic with instances as lemmas: 

    A:Type, eqa: EqA |- ? : Eq (list A)

  Simple depth-first search with higher-order unification

– Returns the first solution only 
     - not always what you want!!
+ Extensible through Ltac
 *)

(* WRITE MORE: Show how to turn on debugging and explain what it
   prints.  Do some trickier examples.  (Maybe some of this needs to
   go below, after parameterized instances are introduced.) *)

(* Matthieu's slides have some stuff about "Instance Inference"
   that is probably useful but I'm not sure I follow it... *)

(* ---------------------------------------------------------------- *)
(** Parameterized Instances: New Typeclasses from Old *)

Instance eqPair {A B : Type} `{Eq A} `{Eq B} : Eq (A * B) :=
  {|
    eqb p1 p2 :=
      match p1,p2 with
      | (a1,b1),(a2,b2) => andb (eqb a1 a2) (eqb b1 b2)
      end
  |}.

(* Exercise: Write eq instances for options and lists *)

 *)
Class Show A : Type :=
  {
    show : A -> string
  }.

Instance showBool : Show bool :=
  {|
    show := fun b:bool => if b then "true" else "false"
  |}.

Definition natToDigit (n : nat) : string :=
  match n with
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
    | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end.

Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := (natToDigit (n mod 10)) ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string :=
  writeNatAux n n "".

Instance showNat : Show nat :=
  {|
    show := string_of_nat
  |}.

Compute (show 42).

Instance showString : Show string :=
  {|
    show := fun s:string => """" ++ s ++ """"
  |}.

Compute (show true).

(* ---------------------------------------------------------------- *)
(** Implicit Generalization *)

(* Here, [`{Eq A}] essentially means the same as [{_ : Eq A}].  The
   opening tick tells Coq to perform "implicit generalization."

   Here's what the Coq reference manual says:

      Implicit generalization is an automatic elaboration of a
      statement with free variables into a closed statement where
      these variables are quantified explicitly. Implicit
      generalization is done inside binders starting with a ` and
      terms delimited by `{ } and `( ), always introducing maximally
      inserted implicit arguments for the generalized
      variables. Inside implicit generalization delimiters, free
      variables in the current context are automatically quantified
      using a product or a lambda abstraction to generate a closed
      term. *)

(* For example: *)
Generalizable Variables x y.
(* (By default, ordinary variables don't behave this way, to avoid
   puzzling behavior in case of typos.) *)

Definition weird1 := `(x + y).
Print weird1.

Lemma weird2 : `(x + y = y + x).
Proof. intros. omega. Qed.

Print oddManOut.

Definition oddManOut' {X : Type} {_ : Eq X} (a b c : X) : X :=
  if eqb a b then c
  else if eqb a c then b
  else a.                         

(* TODO: Now explain this:

Definition oddManOut {X : Type} {Eq X} (a b c : X) : X :=
  if eqb a b then c
  else if eqb a c then b
  else a.                         

====>
    Error: Unable to satisfy the following constraints:
    UNDEFINED EVARS:
     ?X12==[X |- Type] (type of Eq) {?T}
     ?X15==[X0 Eq X a b c |- Eq X] (parameter Eq of @eqb) {?Eq}
     ?X17==[X0 Eq X a b c |- Eq X] (parameter Eq of @eqb) {?Eq0}
*)

(* This may seem like a lot of trouble just to avoid writing a _!  Why
   is it useful?

   Matthieu makes the point that binding super-classes is supported by
   implicit generalization using this example:

    Program Definition div2 ‘{Frac α} (a : α) := div a (1 + 1). ⇒
    Definition div2 {α} {N : Num α} {Frac α N} (a : α) := ...

    ___

    Also, substructures become subinstances: Class Monoid A := { monop
    : A → A → A ; ... } ClassGroupA:={grp mon: MonoidA;...} Instance
    grp mon ‘{Group A} : Monoid A. Definition foo ‘{Group A} (x : A) :
    A := monop x x.  Similar to the existing Structures based on
    coercive subtyping.

From the reference manual:

  However, the generalizing binders should be used instead as they
  have particular support for type classes:
      - They automatically set the maximally implicit status for type
        class arguments, making derived functions as easy to use as
        class methods. In the example above, A and eqa should be set
        maximally implicit.
      - They support implicit quantification on partially applied type
        classes (§2.7.19). Any argument not given as part of a type
        class binder will be automatically generalized.
      - They also support implicit quantification on
        superclasses (§20.5.1)
*)

(* Q: Does `(...) mean the same as `{...} ? *)

(* ---------------------------------------------------------------- *)
(** Internals *)

(* Explain briefly what a typeclass actually translates
   into.  (Explain Coq records en passant.) *)

(* Explain the output!  Notice that it's basically just a record type. *)
Print Eq.
(* ===>
     Record Eq (A : Type) : Type := Build_Eq { eqb : A -> A -> bool }
*)

Check eqb.  
(* EXPLAIN:
==> 
eqb
     : ?A -> ?A -> bool
where
?A : [ |- Type] 
?Eq : [ |- Eq ?A] 
*)

(* Recommended exercise: Reminder of how Coq displays implicit parameters... *)
Definition foo {A : Type} (a : A) : A := a.
Check foo.
(* ===>
     foo
          : ?A -> ?A
     where
     ?A : [ |- Type] 
*)

Print eqBool.
(* ==> 
eqBool = {| eqb := fun b c : bool => if b then c else negb c |}
     : Eq bool
*)

Print eqb.
(* ==>
     eqb = 
     fun (A : Type) (Eq0 : Eq A) => let (eqb) := Eq0 in eqb
          : forall A : Type, Eq A -> A -> A -> bool

     Arguments A, Eq are implicit and maximally inserted
     Argument scopes are [type_scope _ _ _]
 *)

Check (@eqb).
(* ==>
    @eqb
       : forall A : Type, Eq A -> A -> A -> bool
*)

(* Instance inference... 

    fun (x y : bool) => eqb x y 
    ===>   { Implicit arguments }
    fun (x y : bool) => @eqb _ _ x y
    ===>   { Typing }
    fun (x y : bool) => @eqb (?A : Type) (?eq : Eq?A) x y 
    ===>   { Unification }
    fun (x y : bool) => @eqb bool (?eq : Eq bool) x y 
    ===>   { Proof search for Eq bool returns Eq bool }
    fun (x y : bool) => @eqb bool (eqBool : Eq bool) x y 
*)

(* For purposes of instance inference, it doesn't matter whether hypotheses are explicit or inferred.  So, for example, one could just as well write *)

Definition oddManOut'' {X : Type} (_ : Eq X) (a b c : X) : X :=
  if eqb a b then c
  else if eqb a c then b
  else a.                         

(* However, if we define it this way, then applying the function is
   going to be more clunky: *)

(*
Check (oddManOut'' 1 2 1).
===>
   Error: The term "1" has type "nat" while it is expected to have type "Eq ?X".
*)

Check (oddManOut'' eqNat 1 2 1).

(*
Proof-search tactic with instances as lemmas: 

    A:Type, eqa: EqA |- ? : Eq (list A)

  Simple depth-first search with higher-order unification

– Returns the first solution only 
     - not always what you want!!
+ Extensible through Ltac
 *)

(* WRITE MORE: Show how to turn on debugging and explain what it
   prints.  Do some trickier examples.  (Maybe some of this needs to
   go below, after parameterized instances are introduced.) *)

(* Matthieu's slides have some stuff about "Instance Inference"
   that is probably useful but I'm not sure I follow it... *)

(* ---------------------------------------------------------------- *)
(** Parameterized Instances: New Typeclasses from Old *)

Instance eqPair {A B : Type} `{Eq A} `{Eq B} : Eq (A * B) :=
  {|
    eqb p1 p2 :=
      match p1,p2 with
      | (a1,b1),(a2,b2) => andb (eqb a1 a2) (eqb b1 b2)
      end
  |}.

(* Exercise: Write Eq and Show instances for options and lists *)

(* ---------------------------------------------------------------- *)
(** Classes with Superclasses *)

Generalizable Variables A.  (* Explain *)

Class Ord `{Eq A} :=
  {
    le : A -> A -> bool
  }.

(* This is kind of weird... -- choose a better example! *)
Definition le_eqb `{Ord A} (x y : A) := andb (le x y) (le y x).

(* From 20.5.1 of reference manual, but it doesn't seem to work:

Definition lt `{eqa : Eq A, ! Ord eqa} (x y : A) := 
        andb (le x y) (neqb x y).

(explain the ! notation...)
  
   "The ! modifier switches the way a binder is parsed back to the
   regular interpretation of Coq. In particular, it uses the implicit
   arguments mechanism if available, as shown in the example."
*)

(* Exercise: define Ord instances for nat, option, pair, and list *)


(* ---------------------------------------------------------------- *)
(** Typeclasses and Proofs *)

Class EqDec' (A : Type) := {
        eqb' : A -> A -> bool ;
        eqb_leibniz' : forall x y, eqb x y = true -> x = y }.
Print EqDec'.

Instance eq_bool : EqDec' bool := 
  {|
    eqb' x y := if x then y else negb y
  |}.

Class EqDec `{Eq A} : Type := 
  { 
    eqb_leibniz : forall x y, eqb x y = true -> x = y 
  }.
Print EqDec'.
Print EqDec.
Check (@eqb_leibniz).

(* NOT WORKING -- WHY?
Instance eq_bool : EqDec bool := 
  {|
    eqb x y := if x then y else negb y
  |}.
*)

(* If one does not give all the members in the Instance declaration, Coq
enters the proof-mode and the user is asked to build inhabitants of
the remaining fields, e.g.:

Instance eq_bool : EqDec bool := 
  {|
  |}.

etc.
*)

(* ---------------------------------------------------------------- *)
(** Dependent Typeclasses *)

(* Build the Dep typeclass and some instances.

   Probably also show Reflexive example from Matthieu.  Maybe also
   show Monoid and AbelianMonoid from his tutorial. (This motivates
   the real need for implicit generalization!) *)

(*
Substructures

Substructures are components of a class which are instances of a class themselves. They often arise when using classes for logical properties, e.g.:

Coq < Class Reflexive (A : Type) (R : relation A) :=
        reflexivity : forall x, R x x.

Coq < Class Transitive (A : Type) (R : relation A) :=
        transitivity : forall x y z, R x y -> R y z -> R x z.
This declares singleton classes for reflexive and transitive relations, (see 1 for an explanation). These may be used as part of other classes:

Coq < Class PreOrder (A : Type) (R : relation A) :=
      { PreOrder_Reflexive :> Reflexive A R ;
        PreOrder_Transitive :> Transitive A R }.

The syntax :> indicates that each PreOrder can be seen as a Reflexive relation. So each time a reflexive relation is needed, a preorder can be used instead. This is very similar to the coercion mechanism of Structure declarations. The implementation simply declares each projection as an instance.

One can also declare existing objects or structure projections using the Existing Instance command to achieve the same effect.
*)

(* ################################################################# *)
(** * Some Useful Typeclasses *)

(* MORE: Equality or equivalence?  *)

(* ----------------------------------------------------------------- *)
(** ** [Dep] *)

(* ----------------------------------------------------------------- *)
(** ** [Monad] *)

(* Mention ext-lib, but not sure whether it's a good idea to actually
   go into the details... Might be a good case study. *)

(* ----------------------------------------------------------------- *)
(** ** Others *)

(* Enumerate some of the interesting ones in the standard
   library... E.g., Functor (is there one??)?  Monoid?  See what else
   Matthieu likes... *)

(*
################################################################# *)
(** * Pragmatics *)

(* Advice about how to use typeclasses in Coq.  How to avoid various
   pitfalls and gotchas.  How to debug... *)

(* ------------------------------------------------------------- *)
(** ** Understanding error messages *)

(* One downside of using typeclasses is that error messages get more
   puzzling (sometimes substantially so).  Here is a common one. *)
Inductive bar :=
  Bar : nat -> bar.
(*
Definition eqBar :=
  eqb (Bar 42) (Bar 43).
===> 
      Error: Unable to satisfy the following constraints:
      ?Eq : "Eq bar"
*)
(* Here it's pretty easy to see what the problem is.  To fix it, we
   just have to define a new instance... 
*)

(* TODO: Cook up a more complicated example where it's harder to see... *)

(* ------------------------------------------------------------- *)
(** ** Debugging *)

(* TODO: Show how to use Set Printing Implicit *)

(* Getting even more information... *)

Set Typeclasses Debug.
(* Find an interesting enough example... *)
Definition pairThing := eqb (2,(3,true)) (2,(3,false)).
(* ==>
    Debug: 1: looking for (Eq X) without backtracking
    Debug: 1.1: exact e on (Eq X), 0 subgoal(s)
    Debug: 1: looking for (Eq X) without backtracking
    Debug: 1.1: exact e on (Eq X), 0 subgoal(s)
    Debug: 1: looking for (Eq A) without backtracking
    Debug: 1.1: exact H on (Eq A), 0 subgoal(s)
    Debug: 1: looking for (Eq B) without backtracking
    Debug: 1.1: exact H0 on (Eq B), 0 subgoal(s)
    Debug: 1: looking for (Eq (nat * (nat * bool))) without backtracking
    Debug: 1.1: simple apply @eqPair on (Eq (nat * (nat * bool))), 2 subgoal(s)
    Debug: 1.1.3 : (Eq nat)
    Debug: 1.1.3: looking for (Eq nat) without backtracking
    Debug: 1.1.3.1: exact eqNat on (Eq nat), 0 subgoal(s)
    Debug: 1.1.3 : (Eq (nat * bool))
    Debug: 1.1.3: looking for (Eq (nat * bool)) without backtracking
    Debug: 1.1.3.1: simple apply @eqPair on (Eq (nat * bool)), 2 subgoal(s)
    Debug: 1.1.3.1.3 : (Eq nat)
    Debug: 1.1.3.1.3: looking for (Eq nat) without backtracking
    Debug: 1.1.3.1.3.1: exact eqNat on (Eq nat), 0 subgoal(s)
    Debug: 1.1.3.1.3 : (Eq bool)
    Debug: 1.1.3.1.3: looking for (Eq bool) without backtracking
    Debug: 1.1.3.1.3.1: exact eqBool on (Eq bool), 0 subgoal(s)
    pairThing is defined
*)

(* Also... (default is 1) *)
Set Typeclasses Debug Verbosity 2.

(* ------------------------------------------------------------- *)
(** ** Nontermination *)

(* An example of a potential gotcha:
 
The problem appears to be when using the (universe-polymorphic) inject
function in conjunction with a typeclass method, when the necessary
instance doesn't exist.

Inductive Foo := MkFoo : Foo.
  Set Typeclasses Debug.

  Instance gen : Gen (list Foo) := {| arbitrary := liftGen inject
    arbitrary |}.

Leo: My goto debug method is to try to manually expand the
typeclasses. Before that, I needed to understand what “inject”
was. Since the result type was list of X, I assumed that inject is
similar to using “pure” or “return” in Haskell instead of (fun x =>
[x]). However, Coq is really bad usually at figuring out implicit
stuff – so I just replaced it by the explicit anonymous function.
 
After that it was just a “Gen (list X) instance does not exist”, so
deriving Arbitrary (or Gen) for X should work (and it did). Now, why
things work when moving back to “inject” after adding the instance I
have no idea 😊

Yao: I have discussed this with Leo. The problem is that I have
defined the following instance:

Polymorphic Instance Injection_trans {A B C : Type} {|P : Injection A
            B} {Q : Injection B C} : Injection A C := { inject e :=
            inject (inject e) |}.

This would cause the type checker to go to an infinite loop if it
recursively takes this branch before exploring other
possibilities. Removing this instance would fix the problem.

We don’t see other problems with this Injection type class for
now. Therefore, I suggest we keep this type class, but be careful not
to define something similar to what I did.

EXERCISE: Find a different way of making instance inference diverge.

Hint: If confused, you can look at the *coq* buffer. That's where
most debug messages appear if they don't appear in the *response*
buffer.  (What's a typical example of this?)
*)

(* ---------------------------------------------------------- *)
(** ** Controlling instantiation *)

(* Existing Instance *)

(* "Global Instance" redeclares Instance at end of Section. (Does it
   do anything else??) 

    "This commands adds an arbitrary constant whose type ends with an
    applied type class to the instance database with an optional
    priority. It can be used for redeclaring instances at the end of
    sections, or declaring structure projections as instances. This is
    almost equivalent to Hint Resolve ident : typeclass_instances." *)

(* Parametric Instance *)

(* Priorities *)

(* "An optional priority can be declared, 0 being the highest priority
   as for auto hints. If the priority is not specified, it defaults to
   n, the number of binders of the instance." *)

(* Defaulting *)

Check @eqb.
Check eqb.
(* ===>
     eqb
        : nat -> nat -> bool

(!)  Because typeclass inference does "defaulting."

This behavior can be puzzling.  
*)
Definition weird x y := eqb x y.
Check weird.

(* ---------------------------------------------------------- *)
(** ** Interactions with modules *)

(* ---------------------------------------------------------- *)
(* Problems with imports...

   I might try to explain this in more details later on, but this is a
   brief summary: The mystery lies in the order of
   imports/exports. There is another `get` function in Coq’s string
   library, and if that is imported after ExtLib’s MonadState library,
   Coq’s type checker will try to infer the types within a monadic
   function (which contains a MonadState.get) using the type of
   String.get. Somehow the definition of a monad transformer is too
   generic that it allows Coq to try to match the type with it again
   and again, instead of reporting an error.

   I do not fully understand this problem because it seems that Coq
   would still consider `get` as `String.get`, even if I export
   MonadState after String in Common.v. *)

(* ############################################################## *)
(** * Alternative Structuring Mechanisms *)

(* Choosing among typeclasses, modules, dependent records, canonical
   instances.  Pointers to where to read about all these. *)

(* Mattheiu's Penn slides have a discussion of sharing by fields vs by
   parameters that probably deserves to be incorporated here -- or at
   least summarized with a pointer to somewhere people can read about
   it... *)

(*
################################################################# *)
(** * Further Reading *)

(* Origins: In Haskell, Wadler & Blott, POPL’89.  In Isabelle, Nipkow
& Snelting, FPCA’91.  In Coq: Sozeau
*)

(* Acknowledge sources for this tutorial. *)

(* Typeclasses in Haskell:
     - https://en.wikibooks.org/wiki/Haskell/Classes_and_types
          - maybe a bit too low-level, not enough examples
     - http://learnyouahaskell.com/types-and-typeclasses and
       http://learnyouahaskell.com/making-our-own-types-and-typeclasses
     - Simon PJ, Classes, Jim, But Not as We Know Them — Type Classes
       in Haskell: What, Why, and Whither (video from OPLSS?)

  Typeclasses in Coq:
     - The original ideas: Matthieu Sozeau and Nicolas
       Oury. First-Class Type Classes. In TPHOLs’08, 2008.
     - Reference manual chapter:
           https://coq.inria.fr/refman/Reference-Manual023.html
     - "Gentle" Introduction:
           http://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf
     - StackOverflow:
           https://stackoverflow.com/questions/29872260/coq-typeclasses-vs-dependent-records
     - Sozeau slides:
           https://www.cis.upenn.edu/~bcpierce/courses/670Fall12/slides.pdf
*)

(* HIDE *)
(* ################################################################# *)
(* ################################################################# *)
(* ################################################################# *)
(* More Ideas for material that could be included...  *)

(* QUESTION: What does "Polymorphic Instance" mean? *)

(* _____________________________________________________________________ *)
    

