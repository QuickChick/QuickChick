Require Import Machine.
Require Import Common.

Require Import ZArith.
Require Import List.

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
      | Vcptr c1, Vcptr c2 => Z_eq c1 c2
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

(* Indistinguishability of pcs 
   - If both pc's are lower than the observability level,
     then we need to make sure all their components are pairwise 
     indistinguishable (ie. equal)
   - Else, if both are high, there is no need for their labels to
     be equal, since they are protected by the pc themselves.
*)
Instance indistPtrAtm : Indist Ptr_atom :=
{|
  indist lab p1 p2 := 
    let '(PAtm i1 l1) := p1 in
    let '(PAtm i2 l2) := p2 in
    if isLow l1 lab && isLow l2 lab then
      label_eq l1 l2 && Z_eq i1 i2
    else isHigh l1 lab && isHigh l2 lab
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
      (label_eq l1 l2) &&
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
      list_of_option (map (Mem.get_frame m) (Mem.get_all_blocks lab m)) in
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

(* LL: Per discussion with Catalin, doing away with this constraint to see what happens *)
(* Constraint for well formed stacks
   - The returning pc labels must decrease as we go down the stack.
*)
Require Import String.
Fixpoint well_formed_stack (prev : Label) (s : Stack) : bool :=
  match s with
    | Mty => true
    | RetCons (pc, _, _ ,r) s' =>
      if isLow ∂pc prev then well_formed_stack ∂pc s'
      else false
  end.

(* CropTop helper for stacks. 
   - Takes a stack and keeps its low part.
   INV: Stacks should be wellFormed
*)
Fixpoint cropTop (lab : Label) (s : Stack) :=
  match s with
    | Mty => Mty 
    | RetCons (pc, _, _, _) s' =>
      if isLow ∂pc lab then s else cropTop lab s'
  end.

(* Indistinguishability of *low* stacks 
   - Pointwise indistinguishability
     * The returning labels must be equal
     * The returning pc's must be equal
     * The saved registers must be indistinguishable
     * The returning register must be the same
     * The rest of the stack must be also indistinguishable
   INV: Called only on stacks after cropTop, which means all pc's are low
*)
Fixpoint indistStackHelper (lab : Label) 
         (s1 s2 : Stack) :=
  match s1, s2 with
    | Mty, Mty => true
    | RetCons (p1,l1,regs1,r1) s1, RetCons (p2,l2,regs2,r2) s2 =>
      label_eq l1 l2 
      && indist lab p1 p2
      && Z_eq r1 r2
      && indist lab regs1 regs2 
      && indistStackHelper lab s1 s2
    | _, _ => false
  end.

(* Indistinguishability of stacks 
   - Both must be well formed 
   - Their cropTop parts must be equivalent
*)
Instance indistStack : Indist Stack :=
{|
  indist lab s1 s2 :=
(*    wellFormed s1 && wellFormed s2
    && indistStackHelper lab (cropTop lab s1) (cropTop lab s2)*)
    indistStackHelper lab (cropTop lab s1) (cropTop lab s2) 
|}.

    
(* Indistinguishability of states 
   - If both pc's are high then :
     -- Memories and Stacks must be indistinguishable (Fix with reachability)
   - Else if at least one pc is low then :
     -- Both pc's must be low and equal
     -- Registers should be indistinguishable
     -- The high constraints also apply
*)
Instance indistState : Indist State :=
{| 
  indist lab st1 st2 := 
    let '(St imem1 m1 _ s1 regs1 pc1) := st1 in
    let '(St imem2 m2 _ s2 regs2 pc2) := st2 in
    if list_eq_dec instr_eq_dec imem1 imem2 then 
      if isHigh ∂pc1 lab && isHigh ∂pc2 lab then
        if indist lab m1 m2 then
          if indist lab s1 s2 then true
          else Property.trace "Stack" false
        else Property.trace "Memory" false
      else 
        (* next check implies isLow pc1 ... && isLow pc2 ... *)
        if indist lab pc1 pc2 then
          if indist lab regs1 regs2 then
            if indist lab m1 m2 then
              if indist lab s1 s2 then true
                   (* CH: This still relies on Leo's stack pc invariant;
                          otherwise should be running indistStackHelper *)
              else Property.trace "Stack" false
            else Property.trace "Memory" false
          else Property.trace "Registers" false
        else Property.trace "PC" false
    else Property.trace "not equal instructions" false
|}.
