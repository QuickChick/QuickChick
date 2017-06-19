Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Local Open Scope string.

(* ################################################################# *)
(** * Basics *)

(** ** First Example: The [Show] Typeclass *)

(* Motivation: Need to be able to convert lots of things to strings... 
     - show : A -> String

   Similar examples:
     - sort : list A -> list A
     - eqb : A -> A -> bool      (is that the right name?)
     - + : A -> A -> A
     - serialize : A -> BitString
     - hash : A -> Int
     - etc., etc.

  Coq adopts (and adapts) Haskell's notion of _typeclasses_ for this.
*)

(* Class declaration: *)
Class Show (A : Type) : Type :=
{
  show : A -> string
}.

Check Show.  (* explain the output! *)
Check show.  (* explain the output! *)

(* Instance declaration: *)
Instance showBool : Show bool :=
  {|
    show := fun b:bool => if b then "true" else "false"
  |}.

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
  {|
    show := string_of_nat
  |}.

Compute (show 42).

Instance showString : Show string :=
  {|
    show := fun s:string => """" ++ s ++ """"
  |}.

Compute (show true).

(* Exercise: Write show instance for pairs of a nat and a bool. *)

(* One downside of using typeclasses is that error messages get more
   puzzling (sometimes substantially so).  Here is a common one. *)
(*
Inductive foo :=
  Foo : nat -> foo.

Definition showMyList :=
  show (Foo 43).

===> 
      Error: Unable to satisfy the following constraints:
      ?Show : "Show foo"

To fix it, we just have to define a new instance... (do it, or ask them to)
*)

(* What if we *)

Definition showFancy {A : Type} `{Show A} (a : A): string :=
  "((((((((((( " ++ show a ++ " )))))))))))".

Compute (showFancy true).


(* Explain: What does the ` syntax mean?  Note that we can name the
   parameter if we want -- i.e., `{Show A} is just the same as `{_ :
   Show A}. Explain when you'd need to do this, or better yet explain
   it below and put a pointer here. *)

(* Recommended exercise: What happens if we forget the class
   constraint?  Try deleting it and see what happens.  Do you
   understand why? *)

(* MAYBE: Show one more simple typeclass, perhaps equality *)

(* Remark for newcomers: the name "typeclasses" may sound a bit like
   "classes" from OOP.  But this is misleading.  A better analogy is
   actually with _interfaces_ from languages like Java.  But best of
   all is to set aside OO preconceptions and try to approach the
   situation with an open mind. *)

(* ---------------------------------------------------------------- *)
(** Internals *)

(* Explain briefly what a typeclass actually translates into. *)

(* ---------------------------------------------------------------- *)
(** Parameterized Instances: New Typeclasses from Old *)

Instance showPair {A B : Type} `{Show A} `{Show B} : Show (A * B) :=
  {|
    show p :=
      match p with (a,b) =>
      | ("(" ++ show a ++ "," ++ show b ++ ")")
      end
  |}.

(* Exercise: Write show instances for options and lists *)

(* Exercise?: Define a Ord typeclass, with instances for nat, bool,
   pairs, and lists. *)

(** Typeclasses and Proofs *)

(* E.g. maybe Matthieu's EqDec example.  (And then we could replace
   Show above by Eq.) *)

(*
################################################################# *)
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
   pitfalls and gotchas.  How to debug. *)

(* Alternatives.  Choosing among typeclasses, modules, dependent
   records, canonical instances.  Pointers to where to read about all
   these. *)

(*
################################################################# *)
(** * Further Reading *)

(* Origins: In Haskell, Wadler & Blott, POPL’89.  In Isabelle, Nipkow
& Snelting, FPCA’91.  In Coq: Sozeau
*)

(* Typeclasses in Haskell:
     - https://en.wikibooks.org/wiki/Haskell/Classes_and_types
          - maybe a bit too low-level, not enough examples
     - http://learnyouahaskell.com/types-and-typeclasses and
       http://learnyouahaskell.com/making-our-own-types-and-typeclasses
     - Simon PJ, Classes, Jim, But Not as We Know Them — Type Classes
       in Haskell: What, Why, and Whither (video from OPLSS?)

  Typeclasses in Coq:
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
(*
################################################################# *)
(*
################################################################# *)
(*
################################################################# *)
(* More Ideas...  *)

(* What does "Polymorphic Instance" mean? *)

(** Pragmatics *)

(* A potential gotcha:
 
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

 *)

(* Hint: If confused, you can look at the *coq* buffer. That's where
most debug messages appear if they don't appear in the *response*
buffer.  (What's a typical example of this? *)
*)

(* /HIDE *)