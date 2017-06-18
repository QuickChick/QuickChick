(* see Learn You A Haskell, or Simon PJ, Classes, Jim, But Not as We
  Know Them — Type Classes in Haskell: What, Why, and Whither (video
  from OPLSS?)

  good background http://learnyouahaskell.com/types-and-typeclasses
    and Simon PJ, Classes, Jim, But Not as We Know Them — Type Classes
    in Haskell: What, Why, and Whither (video from OPLSS?)

  By "tutorial on basic Haskell type classes" I am assuming that you
  mean something which explains what a type class is, how to create
  and use them, and so on? (As opposed to, say, something which
  introduces some of the particular type classes in the standard
  library?)  I suppose you might be able to use my lecture notes as a
  starting point:
  http://www.seas.upenn.edu/~cis194/spring13/lectures/05-type-classes.html
  .  I don't know if it's good but it's certainly short.  The Haskell
  wikibook is also usually pretty good:
  https://en.wikibooks.org/wiki/Haskell/Classes_and_types , though on
  skimming it now I think it probably spends too much time on
  incidental details with not enough examples.  All the other basic
  type class tutorials that I know of are in textbooks that I haven't
  read so I can't vouch for them.

Reference manual chapter:
  https://coq.inria.fr/refman/Reference-Manual023.html "Gentle"
  Introduction:
  http://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf
  StackOverflow:
  https://stackoverflow.com/questions/29872260/coq-typeclasses-vs-dependent-records
  Sozeau slides:
  https://www.cis.upenn.edu/~bcpierce/courses/670Fall12/slides.pdf

  an example or two of how what are compiled into (dictionary passing)

  advice about advantages and disadvantages (and alternatives?)
 *)

Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Local Open Scope string.

Class Show (A : Type) : Type :=
{
  show : A -> string
}.

Check Show.  (* explain the output! *)
Check show.  (* explain the output! *)

Instance showBool : Show bool :=
{|
  show := fun b:bool => if b then "true" else "false"
|}.

Instance showString : Show string :=
{|
  show := fun s:string => """" ++ s ++ """"
|}.

Definition natToDigit (n : nat) : string :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
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

(* Can eliminate _, right? *)
Instance showPair {A B : Type} `{_ : Show A} `{_ : Show B} : Show (A * B) :=
{|
  show p := match p with (a,b) => ("(" ++ show a ++ "," ++  show b ++ ")") end
|}.

(* Explain: What does the ` syntax mean? *)

(* Do we want to show them that leaving out some fields causes Coq to
   go into "Proof mode" for the others?  I guess not unless we need
   this. *)

(* now show a parameterized type class (what's the simplest example?) *)

(* now show the definition of Dep *)



(* ----------------------------------------------------------------- *)
(* More stuff... *)

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
buffer.
*)