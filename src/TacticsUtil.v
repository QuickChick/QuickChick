Require Import String.
Require Import List.

Require Import RoseTrees.
Require Import Show.
Require Import State.
Require Import Producer Generators.
Require Import Classes.
Require Import DependentClasses.
Require Import Tactics.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.
From Ltac2 Require Import Constr.

Ltac2 ltac1_congruence () := Ltac1.run (Ltac1.ref [ident:(Coq); ident:(Init); ident:(Prelude); ident:(congruence)]).
Ltac2 Notation "congruence" := ltac1_congruence ().

(* From https://github.com/tchajed/coq-ltac2-experiments/blob/master/src/Ltac2Lib.v *)
Local Ltac2 inv_tac (h: ident) := Std.inversion Std.FullInversion (Std.ElimOnIdent h) None None; subst; Std.clear [h].
Ltac2 Notation "inv" h(ident) := inv_tac h.

Local Ltac2 exfalso_tac () := ltac1:(exfalso).
Ltac2 Notation "exfalso" := exfalso_tac ().

Local Ltac2 lia_ltac1 () := ltac1:(micromega.Lia.lia).
Ltac2 Notation "lia" := lia_ltac1 ().

Ltac2 inv := fun (h : ident) =>  inversion h; subst.

Ltac2 eassumption_ltac2 () := ltac1:(eassumption).
Ltac2 Notation "eassumption" := eassumption_ltac2 ().

Ltac2 tci_ltac (_ : unit) := now eauto 20 with typeclass_instances.
Ltac2 Notation "tci" := tci_ltac ().

Ltac2 print_string (s : string) := Message.print (Message.of_string s).

Ltac2 print_kind (p : constr) :=
  match Constr.Unsafe.kind p with
  | Constr.Unsafe.Rel _ => print_string "Rel"
  | Constr.Unsafe.Var _ => print_string "Var"
  | Constr.Unsafe.Meta _ => print_string "Meta"
  | Constr.Unsafe.Evar _ _ => print_string "Evar"
  | Constr.Unsafe.Sort _ => print_string "Sort"
  | Constr.Unsafe.Cast _ _ _ => print_string "Case"
  | Constr.Unsafe.Prod _ _ => print_string "Prod"
  | Constr.Unsafe.Lambda _ _ => print_string "Lambda"
  | Constr.Unsafe.LetIn _ _ _ => print_string "Letin"
  | Constr.Unsafe.App _ _ => print_string "App"
  | Constr.Unsafe.Constant _ _ => print_string "Constant"
  | Constr.Unsafe.Ind _ _ => print_string "Ind"
  | Constr.Unsafe.Constructor _ _ => print_string "Constructor"
  | Constr.Unsafe.Case _ _ _ _ _ => print_string "Case"
  | Constr.Unsafe.Fix _ _ _ _ => print_string "fix"
  | Constr.Unsafe.CoFix _ _ _ => print_string "Cofix"
  | Constr.Unsafe.Proj _ _ => print_string "Proj"
  | Constr.Unsafe.Uint63 _ => print_string "Uint63"
  | Constr.Unsafe.Float _ => print_string "Float"
  | Constr.Unsafe.Array _ _ _ _ =>print_string "Array" 
  end.


Ltac2 constr_to_ident (a : Init.constr) :=
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.Var i => i
  | _ => Control.throw (Tactic_failure (Some (Message.of_string ("constr is not a var"))))
  end.

Ltac2 constrs_to_idents (a : Init.constr list) := List.map constr_to_ident a.

Ltac simplstar := simpl in *.


Ltac2 id_of_string (s : string) :=
  match Ident.of_string s with
  | Some i => i
  | None => Control.throw (Tactic_failure (Some (Message.of_string ("Not a valid string for identifier"))))
  end.

Ltac2 print_constr (c : constr) := Message.print (Message.of_constr c). 
Ltac2 print_str (c : string) := Message.print (Message.of_string c). 

Local Ltac2 ssromega_tac () := ltac1:(ssromega).
Ltac2 Notation "ssromega" := ssromega_tac ().


Ltac2 clear_dependent (x : ident) :=
  let x := Control.hyp x in
  ltac1:(x |- clear dependent x) (Ltac1.of_constr x).
