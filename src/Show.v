Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import ZArith.
Require Import List.

Definition newline := String "010" ""%string.

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

(* Following Coq's weird conventions -- not certain that's a good idea *)
Definition quotechar := ascii_of_nat 34.
Fixpoint show_quoted_string (s:string) : string :=
  match s with
  | EmptyString => """"
  | String c s' =>
    if nat_of_ascii c =? nat_of_ascii quotechar then
        String quotechar (String quotechar (show_quoted_string s'))
    else String c (show_quoted_string s')  
  end.

Instance showString : Show string :=
{|
  show s := String quotechar (show_quoted_string s)
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

Instance showType : Show Type :=
{|
  show x := "nat :)"
|}.

Instance showEx {A} `{_ : Show A} P : Show ({x : A | P x}) :=
  {|
    show ex := let '(exist _ x _) := ex in show x 
  |}.


Require Import Ascii.
Definition nl : string := String (ascii_of_nat 10) EmptyString.

Definition smart_paren (s : string) : string :=
  let fix aux s (b : bool) := 
      match s with 
        | EmptyString => (if b then ")" else "", b)
        | String a s => 
          let (s', b) := aux s (orb b (nat_of_ascii a =? 32)) in
          (String a s, b)
      end in
  let (s', b) := aux s false in
  if b then "(" ++ s' else s'.

Module ShowFunctions.

Import ListNotations.

Class ReprSubset (A : Type) :=
  { representatives : list A }.

Instance repr_bool : ReprSubset bool :=
  {| representatives := [ true; false ] |}.

Instance repr_nat : ReprSubset nat :=
  {| representatives := [ 0 ; 1 ; 2 ; 17 ; 42 ] |}.

Instance repr_option {A} `{_ : ReprSubset A} : ReprSubset (option A) :=
  {| representatives := None :: map Some representatives |}.

Instance repr_list {A} `{_ : ReprSubset A} : ReprSubset (list A) :=
  {| representatives := 
       [] :: map (fun x => [x]) representatives 
          ++ flat_map (fun x : A =>
                         map (fun y : A => [x;y]) representatives
                      ) representatives
  |}%list.

Instance repr_prod {A B} `{_ : ReprSubset A} `{_ : ReprSubset B} :
  ReprSubset (A * B) :=
  {| representatives :=
       flat_map (fun x : A => 
                   map (fun y : B => (x,y)) representatives
                ) representatives 
  |}.

Fixpoint prepend {A : Type} (a : A) (l : list A) :=
  match l with 
    | [] => []
    | h::t => a :: h :: prepend a t
  end.

Definition intersperse {A : Type} (a : A) (l : list A) :=
  match l with 
    | [] => []
    | h::t => h :: prepend a t
  end.

Definition string_concat (l : list string) : string :=
  fold_left (fun a b => a ++ b) l "".

Instance show_fun {A B} `{_ : Show A} `{_ : ReprSubset A}
         `{_ : Show B} : Show (A -> B) :=
  {| show f := 
       "{ " ++ string_concat (intersperse " , " 
                            (map (fun x => show x ++ " |-> " ++ show (f x))
                                 (@representatives A _)))
           ++ " }"
  |}.            

End ShowFunctions.