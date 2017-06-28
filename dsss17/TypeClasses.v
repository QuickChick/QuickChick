(** * Typeclasses *)

Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Omega.
Require Bool.
Local Open Scope string.

(* ################################################################# *)
(** * Basics: Classes and Instances *)

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

   Coq adopts (and significantly adapts) Haskell's notion of
   _typeclasses_ for this.

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
  {
    eqb := fun (b c : bool) => 
       match b, c with
         | true, true => true
         | true, false => false
         | false, true => false
         | false, false => true
       end
  }.

(* Another: *)
Instance eqNat : Eq nat :=
  {
    eqb := beq_nat
  }.

(* Exercise: Write an eq instance for pairs of a nat and a bool. *)

(* We can define functions that use overloaded functions from 
   instances like this: *)
Definition oddManOut {A : Type} `{Eq A} (a b c : A) : A :=
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
  {
    show := fun b:bool => if b then "true" else "false"
  }.

Compute (show true).

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
  {
    show := string_of_nat
  }.

Compute (show 42).

Instance showString : Show string :=
  {
    show := fun s:string => """" ++ s ++ """"
  }.


(* ---------------------------------------------------------------- *)
(** Parameterized Instances: New Typeclasses from Old *)

Instance eqPair {A B : Type} `{Eq A} `{Eq B} : Eq (A * B) :=
  {
    eqb p1 p2 :=
      match p1,p2 with
      | (a1,b1),(a2,b2) => andb (eqb a1 a2) (eqb b1 b2)
      end
  }.

(* Exercise: Write Eq and Show instances for options and lists *)

(* ---------------------------------------------------------------- *)
(** Classes with Superclasses *)

Class Ord {A : Type} `{Eq A} :=
  {
    le : A -> A -> bool
  }.

Definition max {A: Type} `{Eq A} `{Ord A} (x y : A) : A :=
  if le x y then y else x.

Check Ord.

(* Exercise: define Ord instances for nat, option, pair, and list *)

(* ---------------------------------------------------------------- *)
(** * Lifting the Lid  *)

(* Typeclasses in Coq are a powerful tool, but the expressiveness of
   the Coq logic makes it hard to implement sanity checks like
   Haskell's "overlapping instances" detector.  As a result, using
   Coq's typeclasses effectively -- and figuring out what is wrong
   when things don't work -- requires a clear understanding of the
   underlying mechanisms at work. *)

(* ---------------------------------------------------------------- *)
(** ** Implicit Generalization *)

Generalizable Variables A.  
(* (By default, ordinary variables don't behave this way, to avoid
   puzzling behavior in case of typos.) *)

Definition oddManOut' `{Eq A} (a b c : A) : A :=
  if eqb a b then c
  else if eqb a c then b
  else a.                         
(* The opening tick tells Coq to perform "implicit generalization." *)

Print oddManOut'.
(* ===>
    oddManOut' = 
      fun (A : Type) (H : Eq A) (a b c : A) =>
        if eqb a b then c else if eqb a c then b else a
             : forall A : Type, Eq A -> A -> A -> A -> A
*)

(* We can see that [`{Eq A}] essentially means the same as [{_ : Eq
   A}], except that the unbound [A] automatically gets bound at the
   front. *)

(* Where it gets fancy (and useful) is with subclasses: *)

Class Ord1 `{Eq A} :=
  {
    le1 : A -> A -> bool
  }.

Definition max1 `{Ord A} (x y : A) :=
  if le x y then y else x.

(* HIDE: Here's what the Coq reference manual says:

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

(* Implicit generalization can be used in other ways.  For example: *)
Generalizable Variables x y.

Lemma commutativity_property : `(x + y = y + x).
Proof. intros. omega. Qed.

Check commutativity_property.

(* This makes pretty good sense -- a lot of people like to write their
   theorems this way on paper, so why not the formal versions too?
   But it is also possible to use implicit generalization to get
   effects that are arguably not so natural. *)
Definition weird1 := `(x + y).
Print weird1.


(* ---------------------------------------------------------------- *)
(** Internals *)

(* Explain briefly what a typeclass actually translates
   into.  (Explain Coq records en passant.  Note that the syntax for
   record values is different from [Instance] declarations.) *)

(* (Notice that it's basically just a record type.) *)
Print Eq.
(* ===>
     Record Eq (A : Type) : Type := Build_Eq { eqb : A -> A -> bool }
*)

Check eqb.  
(* 
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

Definition oddManOut'' {A : Type} (_ : Eq A) (a b c : A) : A :=
  if eqb a b then c
  else if eqb a c then b
  else a.                         

(* However, if we define it this way, then applying the function is
   going to be more clunky: *)

(*
Check (oddManOut'' 1 2 1).
===>
   Error: The term "1" has type "nat" while it is expected to have type "Eq ?A".
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
(** Typeclasses and Proofs *)

Class EqDec (A : Type) {H : Eq A} := 
  { 
    eqb_eq : forall x y, eqb x y = true -> x = y 
  }.

Check (@EqDec).
Print EqDec.

Instance eqdecBool : EqDec bool := 
  {
    eqb_eq := Bool.eqb_prop
  }.

(* If the Instance declaration does not give values for all the class
   members, Coq enters proof-mode and the user is asked to build
   inhabitants of the remaining fields. *)
Instance eqdecBool' : EqDec bool := 
  {
  }.
Proof. apply Bool.eqb_prop. Defined.

Instance eqdecNat : EqDec nat := 
  {
    eqb_eq := EqNat.beq_nat_true
  }.

(* A quick (and somewhat contrived) example of a proof that works for
   arbitrary things from the EqDec class... *)

Lemma eqb_fact `{EqDec A} : forall (x y z : A),
  eqb x y = true -> eqb y z = true -> x = z.
Proof.
  intros x y z Exy Eyz. 
  apply eqb_eq in Exy.
  apply eqb_eq in Eyz.
  subst. reflexivity. Qed.

(* Exercise: When creating this example, I first wrote this:

     Lemma odd_man_out_fact : `{oddManOut a b c = a -> b = c}.

   Why didn't it work? *)
(* Answer: The types of a, b, and c got instantiated to nat. (But
   why??) *)

(* ---------------------------------------------------------------- *)
(** Dependent Typeclasses *)

(* Build the Dep typeclass and some instances.

   Probably also show Reflexive example from Matthieu.  Maybe also
   show Monoid and AbelianMonoid from his tutorial. *)

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

(* HIDE:

John: I most use Equivalence (and it's related type classes) and Proper.

Matthieu: Like John, I use mostly Equivalence and Proper, the
standard library does not define many more than those. Usually I have
a variant of EquivDec as well for decidable equality tests. *)


(* ----------------------------------------------------------------- *)
(** ** [Dep] *)

(* ----------------------------------------------------------------- *)
(** ** Coq's [EqDec] *)

(* (a bit different from the one we saw here) *)

(* HIDE:

Daniel Schepler:

More generally than EquivDec, I often end up adding a "Decision" typeclass:

Class Decision (P:Prop) : Type :=
decide : {P} + {~P}.
Arguments decide P [Decision].

And then it's very easy to add instances like:

Instance and_dec `{Decision P} `{Decision Q} : Decision (P /\ Q).
Instance nat_lt_dec (m n:nat) : Decision (m < n).
Instance Forall_dec `{!forall x:X, Decision (P x)} (l:list X) :
Decision (Forall P l).

etc.

(Although sometimes, I've found if I also define e.g. nat_le_dec,
nat_gt_dec, nat_ge_dec, it tends to resolve to nat_le_dec in every
case.  Probably not much of an issue, though, unless you want close
control over the extraction.)
*)

(* ----------------------------------------------------------------- *)
(** ** [Monad] *)

(* Mention ext-lib, but not sure whether it's a good idea to actually
   go into the details... Might be a good case study. *)

(* ----------------------------------------------------------------- *)
(** ** Others *)

(* Enumerate some of the interesting ones in the standard
   library... E.g., Functor (is there one??)?  Monoid?  See what else
   Matthieu likes... *)

(* ################################################################# *)
(** * Pragmatics *)

(* Advice about how to use typeclasses in Coq.  How to avoid various
   pitfalls and gotchas.  How to debug... *)

(* HIDE: Sozeau...

   The fact that typeclass resolution resorts to unrestricted proof
   search is a blessing and a curse for sure. Errors tell you only
   that proof search failed and the initial problem while in general
   you need to look at the trace of resolution steps to figure out
   what's missing or, in the worst case, making search diverge. If you
   are writing obviously recursive instances, not mixing computation
   with the search (e.g. Unfolding happening in the indices necessary
   for instances to match), and not creating dependent subgoals then
   you're basically writing Haskell 98-style instances and should get
   the same "simplicity". I think for more elaborate use cases (terms
   in indices, dependencies and computation), when encountering
   unexpected failure the debug output (Set Typeclasses Debug) is
   necessary. Testing the logic program, using Checks for example is a
   good way to explore the proof search results. One can also debug
   interactively by switching to the tactic mode and looking at the
   [typeclasses eauto] behavior. We're facing the same issues as logic
   programming and I don't know of a silver bullet to debug these
   programs. For common issues a newcomer is likely to get, there are
   missing instances which can be prevented/tested using some coverage
   tests, divergence which can be understood by looking at the
   trace (usually it's because of a dangerous instance like
   transitivity or symmetry which has to be restricted or removed, and
   sometimes because of a conversion which makes an instance always
   applicable), and ambiguity when the user does not get the instance
   he expected (due to overlapping mainly, priorities can help here).

   One advantage of modules is that everything is explicit but the
   abstraction cost a bit higher as you usually have to functorize
   whole modules instead of individual functions, and often write down
   signatures separate from the implementations. One rule of thumb is
   that if there are potentially multiple instances of the same
   interface for the same type/index then a module is preferable, but
   adding more indexes to distinguish the instances is also
   possible. *)

(* HIDE: Wiegley...

One thing that always gets me is that overlapping instances are easy to write
with no warning from Coq (unlike Haskell, which ensures that resolution always
pick a single instance). This requires me to often use:

   Typeclasses eauto := debug.

and switch to my *coq* buffer to see which lookup did not resolve to the
instance I was expecting. This is usually fixed by one of two things:

 1. Change the "priority" of the overlapping instance (something we cannot do
    in Haskell).

 2. Change the Instance to a Definition -- which I can still use it as an
    explicitly passed dictionary, but this removes it from resolution.


Another scenario that often bites me is when I define an instance for a type
class, and then intend to write a function using the type class and forget to
provide it as an argument. In Haskell this would be an error, but in Coq it
just resolves to whatever the last globally defined instance was.

For example, say I write a function that uses a functor, but forget to mention
the functor:

   Definition foo (C D : Category) (x y : C) (f : x ~> y) : fobj x ~> fobj y :=
     fmap f.

In Haskell this gives an error stating that no Functor is available. In Coq,
it type checks using the highest priority C --> D functor instance in scope. I
typically discover that this has happened when I try to use [foo] and find the
Functor to be too specific, or by turning on Printing All and looking at the
definition of `foo`. However, there are times when `foo` is deep down in an
expression, and then it's not obvious *at all* why it's failing.

The other way to solve this is to manually ensure there are no Instance
definitions that might overlap, such as a generic Instance for C --> D, but
only instances from specific categories to specific categories (though again,
I might define several functors of that same type). It would be nice if I
could make this situation into an error.


Finally, there is the dreaded "diamond problem", when referring to type
classes as record members rather than type indices:

   Class Foo := {
     method : Type -> Type
   }.

   Class Bar := {
     bar_is_foo :> Foo
   }.

   Class Baz := {
     baz_is_foo :> Foo
   }.

   Class Oops := {
     oops_is_bar :> Bar
     oops_is_baz :> Baz
   }.

Oops refers to two Foos, and I need explicit evidence to know when they are
the same Foo. I work around this using indices:

   Class Foo := {
     method : Type -> Type
   }.

   Class Bar (F : Foo) := {
   }.

   Class Baz (F : Foo) := {
   }.

   Class Oops (F : Foo) := {
     oops_is_bar :> Bar F
     oops_is_baz :> Baz F
   }.

Only those classes which might be multiply-inherited need to be lifted like
this. It forces me to use Sections to avoid repetition, but allows Coq to see
that base classes sharing is plainly evident.

The main gotcha here for the newcomer is that it is not obvious at all when
the diamond problem is what you're facing, since when it hits the parameters
are hidden indices, and you end up with goals like:

   A, B : Type
   F : Foo
   O : Oops
   H : @method (@bar_is_foo (@oops_is_bar O)) A = @method F B
   --------------------
   @method F A = @method F B

You can't apply here without simplying in H. However, what you see at first
is:

   A, B : Type
   F : Foo
   O : Oops
   H : method A = method B
   --------------------
   method A = method B

As a newcomer, knowing to turn on Printing All is just not obvious here, but
it quickly becomes something you learn to do whenever what looks obvious is
not.


Other than these things, I use type classes heavily in my own libraries, and
very much enjoy the facility they provide. I have a category-theory library
that is nearly all type classes, and I ran into every one of the problems
described above, before learning how to "work with Coq" to make things happy.
*)

(* HIDE: Soegtrop... What I had most problems with initially is that
   some type classes have implicit parameters. This works quite well
   when the nesting level of these parameters is small, but when the
   nesting of parameters gets deeper one can have the issue that
   unification takes long, that error messages are hard to understand
   and that later in a proof one might require certain relations
   between different parameters of a type class which are not explicit
   when the initial resolution was done and that an instance is chosen
   which is not compatible with these requirements, although there is
   one which would be compatible. The solution is typically to
   explicitly specify some of the implicit parameters, especially
   their relation to each other. Another advantage of stating certain
   things explicitly is that it is easier to understand what actually
   happens. Let me see if I can find a few examples. *)

(* HIDE: Anand...

Typeclasses are merely about inferring some implicit arguments using proof search. The underlying modularity mechanism, which is the ability to define "existential types" using induction, was ALWAYS there in Coq: typeclasses merely cuts down on verbosity because more arguments can now be implicit because they can be automatically inferred.
Relying on proof search often brings predictability concerns. So, guidance on taming proof search would be very useful: Chapter 13 of CPDT might be a good background for using typeclasses.
Also, it is good to keep in mind that if typeclass-resolution fails to instantiate an implicit argument, some/all of those arguments can be provided manually. Often, just providing one such implicit argument gives enough clues to the inference engine to infer all of them. I think it is important to emphasize that typeclass arguments are just implicit arguments.

Also, another design decision in typeclasses/records is whether to unbundle.
The following paper makes a great case for unbundling:
Spitters, Bas, and Eelis Van Der Weegen. “Type Classes for Mathematics in Type Theory.” MSCS 21, no. Special Issue 04 (2011): 795–825. doi:10.1017/S0960129511000119.
http://arxiv.org/pdf/1102.1323v1.pdf

I think the above paper is missing one argument for unbundling:
I've seen many libraries that begin by making an interface (say I) that bundles ALL the operations (and their correctness properties) they will EVER need and then ALL items in the library (say L) are parametrized by over I. 
A problem with this bundled approach is impossible to use ANY part of D if you are missing ANY operation (or proof of a logical property of the operation) in the interface I, even if parts of D don't actually need that operation: I've run into situations where it is impossible to cook up an operation that 90% of L doesn't use anyway.
When using the unbundled approach, one can use Coq's Section mechanism to ensure that definitions/proofs only depend on items of the interface they actually use, and not on a big bundle.
*)

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

   Here it's pretty easy to see what the problem is.  To fix it, we
   just have to define a new instance. *)

(* TODO: Cook up a more complicated example where it's harder to see... *)

(* ---------------------- *)

(* If you forget a `, you may see the following puzzling error message:

Definition oddManOut'' {A : Type} {Eq A} (a b c : A) : A :=
  if eqb a b then c
  else if eqb a c then b
  else a.                         

====>
    Error: Unable to satisfy the following constraints:
    UNDEFINED EVARS:
     ?X12==[A |- Type] (type of Eq) {?T}
     ?X15==[X0 Eq A a b c |- Eq A] (parameter Eq of @eqb) {?Eq}
     ?X17==[X0 Eq A a b c |- Eq A] (parameter Eq of @eqb) {?Eq0}
*)

(* ------------------------------------------------------------- *)
(** ** Debugging *)

(* TODO: Show how to use Set Printing Implicit *)

(* Getting even more information... *)

Set Typeclasses Debug.
(* Find an interesting enough example... *)
Definition pairThing := eqb (2,(3,true)) (2,(3,false)).
(* ==>
    Debug: 1: looking for (Eq A) without backtracking
    Debug: 1.1: exact e on (Eq A), 0 subgoal(s)
    Debug: 1: looking for (Eq A) without backtracking
    Debug: 1.1: exact e on (Eq A), 0 subgoal(s)
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

  Instance gen : Gen (list Foo) := { arbitrary := liftGen inject
    arbitrary }.

Leo: My goto debug method is to try to manually expand the
typeclasses. Before that, I needed to understand what “inject”
was. Since the result type was list of A, I assumed that inject is
similar to using “pure” or “return” in Haskell instead of (fun x =>
[x]). However, Coq is really bad usually at figuring out implicit
stuff – so I just replaced it by the explicit anonymous function.
 
After that it was just a “Gen (list X) instance does not exist”, so
deriving Arbitrary (or Gen) for X should work (and it did). Now, why
things work when moving back to “inject” after adding the instance I
have no idea 😊

Yao: I have discussed this with Leo. The problem is that I have
defined the following instance:

Polymorphic Instance Injection_trans {A B C : Type} {P : Injection A
            B} {Q : Injection B C} : Injection A C := { inject e :=
            inject (inject e) }.

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

(* ------------------------------------------------------------- *)
(** ** Syntax *)

(* If you read Coq libraries involving typeclasses, you may see
   [Instance] declarations written with [{|...|}] brackets instead of
   [{...}].  The two notations mean _almost_ the same thing, and both
   will work in most instances.  However, the Coq typechecker treats
   them a little differently, which can cause the instance inference
   process to fail sometimes for instances written with [{|...|}]
   brackets when the same declaration written with [{...}] will
   succeed. *)
(* HIDE: coq-club email 24 June 2017 from Matthieu Sozeau

   Indeed you're hitting a few confusing things. First the record notation:
   Instance has a special syntax [{ foo := bar }] for giving the fields of
   the class, while [{| foo := bar |}] was introduced after for introducing
   values in general record types (parsing issues prevented to reuse simple
   braces { }).

   There is a discrepancy in how these are typechecked currently: in the
   Instance : C args := { ... } case, the type information flows from the
   arguments of the class type constraint to the parameters of the
   constructor, hence you get a typing constraint for your method which
   readily mentions bool and eqBool and typechecking succeeds.

   In the case of {| |}, the record value is typechecked independently of
   the typing constraint first, and in your example this involves a
   unification problem

     forall (x y : ?A) (_ : @eq bool (@eqb ?A ?H x y) true), @eq ?A x y ~= 
     forall (a b : bool) (_ : @eq bool (Bool.eqb a b) true), @eq bool a b

   which fails at first. We try to launch typeclass resolution to fill the
   holes, finding ?A to be nat, ?H to be eqNat and then the unification
   fails again as we chose the wrong instance.

     Bidirectional typechecking making the typing constraint information
   flow to the parameters, avoiding this unexpected behavior, is not on by
   default (for compatibility reasons mainly), but activated in Program
   mode, so this works too:

   Program Instance eqdecBool : @EqDec bool eqBool := 
     {|
       eqb_eq := Bool.eqb_prop
     |}.       

   Sorry for the long explanation... it's definitely confusing.
   -- Matthieu
*)


(* ############################################################## *)
(** * Alternative Structuring Mechanisms *)

(* Choosing among typeclasses, modules, dependent records, canonical
   instances.  Pointers to where to read about all these. *)

(* Mattheiu's Penn slides have a discussion of sharing by fields vs by
   parameters that probably deserves to be incorporated here -- or at
   least summarized with a pointer to somewhere people can read about
   it... *)

(* HIDE:

   From Bas...

      Regarding the comparison between type classes and structures.

      LEAN seems to have some nice support for Type Classes/Structures; see
      https://leanprover.github.io/tutorial/

      Chapter Structures.

      They have a type class implementation, but provide some mechanisms for
      extending and renaming structures. It seems light weight, but the
      repackaging that is done behind the scenes looks really helpful and
      natural.

      It seems like it would be useful for Coq too, as it allows a nice
      combination of the conveniences of both the unbundled approach (as in
      math-classes) and package classes (as in ssreflect).

  And:

      Thanks for this. For bystanders, the corresponding library is here:
      http://math-classes.github.io/

*)

(* ################################################################# *)
(** * Further Reading *)

(* Origins: In Haskell, Wadler & Blott, POPL’89.  In Isabelle, Nipkow &
   Snelting, FPCA’91.  In Coq: Sozeau and xx. *)

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

(* /HIDE *)

    

