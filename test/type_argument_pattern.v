From QuickChick Require Import QuickChick.
Require Import List. Import ListNotations.

(* A type argument of a constructor in a conclusion is erased when matching
   inputs, also when the type is a definition such as [Event]. *)
Definition Event := (nat * bool)%type.
Inductive Has : list Event -> Prop := has (e : Event) (l : list Event) : Has (e :: l).
QuickChick Derive Checker for (Has l).

Example has_checks : (decOpt (P := Has [(1, true)]) 5, decOpt (P := Has []) 5) = (Some true, Some false).
Proof. vm_compute. reflexivity. Qed.

(* Constructors still discriminate: from a module, ... *)
Module M. Inductive T := A | B. End M.
Inductive P : M.T -> Prop := p : P M.A.
QuickChick Derive Checker for (P t).

Example module_checks : (decOpt (P := P M.A) 5, decOpt (P := P M.B) 5) = (Some true, Some false).
Proof. vm_compute. reflexivity. Qed.

(* ... and when a constructor shares its name with a type elsewhere. *)
Module X. Inductive Foo := mk. End X.
Inductive Bar := Foo (n : nat) | Baz.
Inductive PF : Bar -> Prop := pf : PF (Foo 0).
QuickChick Derive Checker for (PF b).

Example shared_name_checks :
  (decOpt (P := PF (Foo 0)) 5, decOpt (P := PF (Foo 1)) 5, decOpt (P := PF Baz) 5)
  = (Some true, Some false, Some false).
Proof. vm_compute. reflexivity. Qed.
