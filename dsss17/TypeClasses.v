(*
  see Learn You A Haskell, or 
  Simon PJ, Classes, Jim, But Not as We Know Them — Type Classes in Haskell:
    What, Why, and Whither (video from OPLSS?)

  good background
    http://learnyouahaskell.com/types-and-typeclasses
  and 
    Simon PJ, Classes, Jim, But Not as We Know Them — Type Classes in Haskell:
      What, Why, and Whither (video from OPLSS?)

Reference manual chapter:
  https://coq.inria.fr/refman/Reference-Manual023.html
"Gentle" Introduction:
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