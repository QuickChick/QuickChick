From Coq Require Import Extraction.

From QuickChick Require Export
  QuickChick_Plugin
  Show
  Random
  Sets
  Nat_util
  GenLow
  GenHigh
  State
  Checker
  SemChecker
  Test
  ExtractionQC
  Decidability
  Classes
  Instances
  DependentClasses
  Typeclasses
  Mutation.

Export GenLow GenHigh.

Axiom _W : nat -> Prop.
Axiom _Size : Prop.

Global Unset Asymmetric Patterns.
Global Set Bullet Behavior "Strict Subproofs".

(* TODO: Figure out better place for these *)
(* String and Ascii Instances *)

Require Export Ascii String.

(* Derive (Arbitrary, Show) for ascii. *)

(* Derive (Arbitrary, Show) for string. *)
