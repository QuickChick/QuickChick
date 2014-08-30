Require Import ZArith.
Require Import List.
Require Import EquivDec.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype finset.

Require Import Utils Labels Memory Machine.
(*Require Import Common.*)

Module IndistM (Lattice : FINLAT).

Module GenericMachine := MachineM Lattice.

Import LabelEqType.

(* CH: things fail in very strange ways if this is just Import *)
Export GenericMachine.

Open Scope bool.

(* Indistinguishability type class *)
Class Indist (A : Type) : Type :=
  indist : Label -> A -> A -> bool.

Instance oindist {T : Type} `{Indist T} : Indist (option T) :=
  fun obs x1 x2 => match x1, x2 with
  | None, None => true
  | Some x1, Some x2 => indist obs x1 x2
  | _, _ => false
  end.

Instance indistList {A : Type} `{Indist A} : Indist (list A) :=
{|
  indist lab := forallb2 (indist lab)
|}.

(* Indistinguishability of Values.
   - Ignores the label (called only on unlabeled things)
   - Just syntactic equality thanks to the per-stamp-level allocator!
*)
Instance indistValue : Indist Value :=
{|
  indist _lab v1 v2 := val_eq v1 v2
|}.

(* Indistinguishability of Atoms.
   - The labels have to be equal (observable labels)
   - If the labels are equal then:
     * If they are both less than the observability level then
       the values must be indistinguishable
     * Else if they are not lower, the label equality suffices
*)
Instance indistAtom : Indist Atom :=
{|
  indist lab a1 a2 :=
    let '(Atm v1 l1) := a1 in
    let '(Atm v2 l2) := a2 in
    (l1 == l2)
    && (isHigh l1 lab || indist lab v1 v2)
|}.

Instance indistFrame : Indist frame :=
{|
  indist lab f1 f2 :=
    let '(Fr stamp1 l1 vs1) := f1 in
    let '(Fr stamp2 l2 vs2) := f2 in
    (stamp1 == stamp2) &&
    if isLow stamp1 lab && isLow stamp2 lab then
      (* CH: this part is basically the same as indistinguishability of values;
             try to remove this duplication at some point *)
      (l1 == l2) && (isHigh l1 lab || indist lab vs1 vs2)
    else true
|}.

(* Indistinguishability of memories
   - Get all corresponding memory frames
   - Make sure they are indistinguishable
   - Get all pairs that have been allocated in low contexts.
     They have to be allocated in the same order so no need for fancy stuff
*)

Definition blocks_stamped_below (lab : Label) (m : memory) : list frame :=
  list_of_option (map (Mem.get_frame m) (Mem.get_blocks (allThingsBelow lab) m)).

Instance indistMem : Indist memory :=
{|
  indist lab m1 m2 :=
    indist lab (blocks_stamped_below lab m1) (blocks_stamped_below lab m2)
|}.

(* Indistinguishability of stack frame (pointwise)
     * The returning pc's must be equal
     * The saved registers must be indistinguishable
     * The returning register must be the same
     * The returning labels must be equal
*)
Instance indistStackFrame : Indist StackFrame :=
{|
  indist lab sf1 sf2 :=
    match sf1, sf2 with
      | SF p1 regs1 r1 l1, SF p2 regs2 r2 l2 =>
           pc_eq p1 p2
        && indist lab regs1 regs2
        && Z_eq r1 r2
        && (l1 == l2)
    end
|}.

Definition stackFrameBelow (lab : Label) (sf : StackFrame) : bool :=
  let 'SF ret_addr  _ _ _ := sf in
  let 'PAtm _ l_ret_addr := ret_addr in
  flows l_ret_addr lab.

Definition filterStack (lab : Label) (s : Stack) : list StackFrame :=
  (List.filter (stackFrameBelow lab) (unStack s)).

Instance indistStack : Indist Stack :=
{|
  indist lab s1 s2 :=
    indist lab (filterStack lab s1) (filterStack lab s2)
|}.

Instance indistImems : Indist imem :=
{|
  indist _lab imem1 imem2 :=
    if list_eq_dec instr_eq_dec imem1 imem2 then true else false
|}.

Instance indistState : Indist State :=
{|
  indist lab st1 st2 :=
    let '(St imem1 m1 s1 regs1 pc1) := st1 in
    let '(St imem2 m2 s2 regs2 pc2) := st2 in
    [&& indist lab imem1 imem2,
    indist lab m1 m2,
    indist lab s1 s2 &
    (isLow ∂pc1 lab || isLow ∂pc2 lab) ==>
      (pc_eq pc1 pc2 &&
      indist lab regs1 regs2)]
|}.

End IndistM.
