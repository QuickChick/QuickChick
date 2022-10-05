From Coq Require Import
     Ascii
     Basics
     Decimal
     List
     String
     ZArith.

Import ListNotations.
Local Open Scope program_scope.
Local Open Scope string_scope.

Export Coq.Strings.String.StringSyntax.

(* This makes just the [%string] key available to [Derive ShowS]. *)
Delimit Scope string_scope with string.

Require Import QuickChick.Show.

Class ShowS (A : Type) : Type :=
{
  shows : A -> string -> string
}.

Definition showString (s : string) : string -> string :=
  fun s' => s ++ s'.

Definition fromShow {A} `{Show A} (a : A) : string -> string :=
  showString (show a).

#[global]
Instance showS_unit : ShowS unit := {|
  shows := fromShow  
|}.

#[global]
Instance showS_uint : ShowS uint := {|
  shows := fromShow
|}.

#[global]
Instance showS_bool : ShowS bool := {|
  shows := fromShow
|}.

#[global]
Instance showS_nat : ShowS nat := {|
  shows := fromShow
|}.

#[global]
Instance showS_int : ShowS int := {|
  shows := fromShow
|}.
