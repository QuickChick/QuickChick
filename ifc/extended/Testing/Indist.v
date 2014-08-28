Require Import ZArith.
Require Import List.

Require Import Utils.
Require Import Common.

Open Scope bool.

(* Indistinguishability type class *)
Class Indist (A : Type) : Type :=
{
  indist : Label -> A -> A -> bool
}.

(* Indistinguishability of Values.
   - Ignores the label (called only on unlabeled things)
   - For pointers, it is syntactic equality thanks to the per-stamp-level allocator!
*)
Instance indistValue : Indist Value :=
{|
  indist _lab v1 v2 :=
    match v1, v2 with
      | Vint  i1, Vint i2  => Z_eq i1 i2
      | Vlab  l1, Vlab l2  => label_eq l1 l2
      | Vptr (Ptr mf1 i1), Vptr (Ptr mf2 i2) =>
        mframe_eq mf1 mf2 && Z_eq i1 i2
      | _, _ => false
    end
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
    label_eq l1 l2
    && (isHigh l1 lab || indist lab v1 v2)
|}.

(* Indistinguishability of Frames
   - If their stamps are low, then
     * Their labels are equal
     ** if these labels are low
        then their data must be equal as well
   - If their stamps are high, no condition
     CH: what about the case when one stamp is low and the other is not,
         currently that's treated as indistinguishable, but I don't know
         if it really should
   ** Note: may need to revisit this to make sure it is okay
*)
Instance indistFrame : Indist frame :=
{|
  indist lab f1 f2 :=
    let '(Fr stamp1 l1 ds1) := f1 in
    let '(Fr stamp2 l2 ds2) := f2 in
    if isLow stamp1 lab && isLow stamp2 lab then
      (label_eq l1 l2) && (label_eq stamp1 stamp2) &&
      (if isLow l1 lab then forallb2 (indist lab) ds1 ds2
       else true)
    else (label_eq stamp1 stamp2)
|}.

(* CH: should think of a reachability-based variant of this;
       the root set is the registers and the saved registers on stack *)
(* Helper function for indistinguishability of memories
   - Receives a list of corresponding mframes
   - Recurses down the list making sure that all the frames
     are pairwise indistinguishable.
*)
Definition indistMemHelper (framePairs : list (frame * frame))
         (lab : Label)
         (m1 m2 : memory) :=
  forallb (fun (x : frame * frame) =>
    let (f1, f2) := x in indist lab f1 f2) framePairs.

(* Indistinguishability of memories
   - Get all corresponding memory frames
   - Make sure they are indistinguishable
   - Get all pairs that have been allocated in low contexts.
     They have to be allocated in the same order so no need for fancy stuff
*)

Instance indistMem : Indist memory :=
{|
  indist lab m1 m2 :=
  let get_all_frames (m : memory) : list frame :=
      list_of_option (map (Mem.get_frame m)
                          (Mem.get_blocks (allThingsBelow lab) m)) in
  let frames1 := get_all_frames m1 in
  let frames2 := get_all_frames m2 in
  (* CH: Why is the following not written with forallb2? *)
  beq_nat (length frames1) (length frames2) &&
  indistMemHelper (combine frames1 frames2) lab m1 m2
|}.

(* Indistinguishability of registers
   - Make sure all corresponding registers are indistinguishable
   INV: called only in low contexts
*)
Instance indistReg : Indist regSet :=
{|
  indist lab r1 r2 := forallb2 (indist lab) r1 r2
|}.

(* Indistinguishability of *low* stacks
   - Pointwise indistinguishability
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
        && label_eq l1 l2
    end
|}.

Definition stackFrameBelow (lab : Label) (sf : StackFrame) : bool :=
  let 'SF ret_addr  _ _ _ := sf in
  let 'PAtm _ l_ret_addr := ret_addr in
  flows l_ret_addr lab. 

Definition filterStack (lab : Label) (s : Stack) : list StackFrame :=
  (List.filter (stackFrameBelow lab) (unStack s)).

Instance indistList {A : Type} `{Indist A} : Indist (list A) :=
{|
  indist := fix i lab xs1 xs2 :=
    match xs1, xs2 with
    | nil, nil => true
    | x1 :: xs1', x2 ::xs2' => indist lab x1 x2 && i lab xs1' xs2'
    | _, _ => false
    end
|}.

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
    indist lab imem1 imem2 &&
    indist lab m1 m2 &&
    indist lab s1 s2 &&
    (if isLow ∂pc1 lab && isLow ∂pc2 lab then
      pc_eq pc1 pc2 &&
      indist lab regs1 regs2
    else true)
|}.
