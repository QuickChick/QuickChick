Require Import String.
Require Import ZArith.
Require Import List.

Axiom show_nat  : nat -> string.
Extract Constant show_nat => "Prelude.show".
Axiom show_bool : bool -> string.
Extract Constant show_bool => "Prelude.show".
Axiom show_int  : Z -> string.
Extract Constant show_int => "Prelude.show".

Local Open Scope string.
Class Show (A : Type) : Type :=
{
  show : A -> string
}.

Instance showNat : Show nat :=
{|
  show := show_nat
|}.

Instance showBool : Show bool :=
{|
  show := show_bool
|}.

Instance showInt : Show Z :=
{|
  show := show_int
|}.

Fixpoint contents {A : Type} (s : A -> string) (l : list A) : string :=
  match l with 
    | nil => ""%string
    | cons h nil => s h
    | cons h t => append (append (s h) ", ") (contents s t)
  end.

Instance showList {A : Type} `{_ : Show A} : Show (list A) :=
{|
  show l := append "[ " (append (contents show l) " ]")
|}.

Instance showPair {A B : Type} `{_ : Show A} `{_ : Show B} : Show (A * B) :=
{|
  show p := match p with (a,b) => ("(" ++ show a ++ "," ++  show b ++ ")")%string end
|}.

Instance showOpt {A : Type} `{_ : Show A} : Show (option A) :=
{|
  show x := match x with
              | Some x => "Some " ++ (show x)
              | None => "None"
            end
|}.

Instance showStr : Show string :=
{| show x := x |}.

Require Import Ascii.
Definition nl : string := String (ascii_of_nat 10) EmptyString.