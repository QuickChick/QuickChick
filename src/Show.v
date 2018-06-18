Require Import List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import ZArith.

Definition newline := String "010" ""%string.

Require Extraction.
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

Fixpoint from_list (s : list ascii) : string :=
  match s with
  | [] => EmptyString
  | c :: s' => String c (from_list s')
  end.

Definition unit_digit (n : nat) : ascii :=
  ascii_of_nat ((n mod 10) + 48 (* 0 *)).

Definition three_digit (n : nat) : string :=
  let n0 := unit_digit n in
  let n1 := unit_digit (n / 10) in
  let n2 := unit_digit (n / 100) in
  from_list [n2; n1; n0].

Definition digit_of_ascii (c : ascii) : option nat :=
  let n := nat_of_ascii c in
  if ((48 <=? n)%nat && (n <=? 57)%nat)%bool then
    Some (n - 48)
  else
    None.

Definition unthree_digit (c2 c1 c0 : ascii) : option ascii :=
  let doa := digit_of_ascii in
  match doa c2, doa c1, doa c0 with
  | Some n2, Some n1, Some n0 =>
    Some (ascii_of_nat (n2 * 100 + n1 * 10 + n0))
  | _, _, _ => None
  end.

Fixpoint show_quoted_string (s:string) : string :=
  match s with
  | EmptyString => """"
  | String c s' =>
    let quoted_s' := show_quoted_string s' in
    let n := nat_of_ascii c in
    if ascii_dec c "009" (* TAB *) then
      "\t" ++ quoted_s'
    else if ascii_dec c "010" (* NEWLINE *) then
      "\n" ++ quoted_s'
    else if ascii_dec c "013" (* CARRIAGE RETURN *) then
      "\r" ++ quoted_s'
    else if ascii_dec c """" (* DOUBLEQUOTE *) then
      "\""" ++ quoted_s'
    else if ascii_dec c "\" (* BACKSLASH *) then
      "\\" ++ quoted_s'
    else if ((n <? 32)%nat (* SPACE *)
         || (126 <? n)%nat (* ~ *))%bool then
      "\" ++ three_digit n ++ quoted_s'
    else
      String c quoted_s'
  end.

Instance showString : Show string :=
{|
  show s := String """" (show_quoted_string s)
|}.

(* Example:

Compute (show (from_list
  [ascii_of_nat 10;
   ascii_of_nat 14;
   "a"%char;
   ascii_of_nat 127])).

> """\n\014a\127"""

*)

Fixpoint read_quoted_string (s : string) : option string :=
  match s with
  | String c s' =>
    if ascii_dec c """" then
      match s' with
      | EmptyString => Some EmptyString
      | _ => None
      end
    else if ascii_dec c "\" then
      match s' with
      | String c2 s'' =>
        if ascii_dec c2 "n" then
          option_map (String "010") (read_quoted_string s'')
        else if ascii_dec c2 "r" then
          option_map (String "013") (read_quoted_string s'')
        else if ascii_dec c2 "t" then
          option_map (String "009") (read_quoted_string s'')
        else if ascii_dec c2 "\" then
          option_map (String "\") (read_quoted_string s'')
        else if ascii_dec c2 """" then
          option_map (String """") (read_quoted_string s'')
        else
          match s'' with
          | String c1 (String c0 s''') =>
            match unthree_digit c2 c1 c0 with
            | Some c' => option_map (String c')
                                    (read_quoted_string s''')
            | None => None
            end
          | _ => None
          end
      | _ => None
      end
    else
      option_map (String c) (read_quoted_string s')
  | _ => None
  end.

Definition read_string (s : string) : option string :=
  match s with
  | EmptyString => None
  | String c s' => read_quoted_string s'
  end.

Fixpoint contents {A : Type} (s : A -> string) (l : list A) : string :=
  match l with
    | nil => ""%string
    | cons h nil => s h
    | cons h t => append (append (s h) "; ") (contents s t)
  end.

Instance showList {A : Type} `{_ : Show A} : Show (list A) :=
{|
  show l := append "[" (append (contents show l) "]")
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
  show x := "nat :-)"
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
          (String a s', b)
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
