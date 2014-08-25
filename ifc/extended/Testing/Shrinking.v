Require Import ZArith.
(*Require Import String.*)
Require Import List. Import ListNotations.
Require Import NPeano.

Require Import QuickChick.

Require Import Common. Import Mem.
Require Import Indist.
Require Import Generation.

Local Open Scope nat.

(* CH: old stuff about sets of prins
Powerset returns the set as its first element, so ignore that
Definition shrinkLabel l :=
    match powerset (Zset.elements l) with
      | [[]] => nil
      | _::t => map lab_of_list t
      | _    => nil
    end.
*)
Definition shrinkLabel l :=
  match l with
  | L       => []
  | M1 | M2 => [L]
  | H       => [L;M1;M2]
  end.

Definition shrinkBinop (b : BinOpT) : list BinOpT := nil.
Definition shrinkInstr (i : @Instr Label) : list (@Instr Label) :=
  match i with
    | Nop => nil
    | PutLab l r =>
      List.map (fun l' => PutLab l' r) (shrinkLabel l) ++ [Nop]
    | _ => [Nop]
  end.

Definition shrinkPointer (p : Pointer) : list Pointer :=
  let '(Ptr mf i) := p in
  List.map (Ptr mf) (shrink i).

Definition shrinkValue (v : Value) : list Value :=
  match v with
    | Vint i => List.map Vint (shrink i)
    | Vptr p => Vint Z0 :: List.map Vptr (shrinkPointer p)
    | Vlab l => Vint Z0 :: List.map Vlab (shrinkLabel l)
  end.

Definition shrinkAtom (a : Atom) : list Atom :=
  let '(Atm val lab) := a in
  List.map (flip Atm lab) (shrinkValue val)
  ++  List.map (Atm val) (shrinkLabel lab).

Fixpoint noopShrink (n : nat) (l : Label) (l1 l2 : list (@Instr Label))
: list (@Variation (list (@Instr Label))) :=
  match n with
    | S n' =>
      match List.nth n' l1 Nop, List.nth n' l2 Nop with
        | Nop, Nop =>
          noopShrink n' l l1 l2
        | _, _ =>
          match upd l1 (Z.of_nat n') Nop, upd l2 (Z.of_nat n') Nop with
            | Some l1', Some l2' => cons (Var l l1' l2')
                                         (noopShrink n' l l1 l2)
            | _, _ => noopShrink n' l l1 l2
          end
      end
    | _ => nil
  end.

Fixpoint noopRemove (l : Label) (l1 l2 : list (@Instr Label))
         (acc1 acc2 : list (@Instr Label)) :=
  match l1, l2 with
    | Nop :: t1, Nop :: t2 =>
      (Var l (rev_append acc1 t1)) (rev_append acc2 t2)
      :: (noopRemove l t1 t2 (Nop :: acc1) (Nop :: acc2))
    | h1 :: t1, h2 :: t2 =>
      noopRemove l t1 t2 (h1 :: acc1) (h2 :: acc2)
    | _, _ => nil
  end.

Instance shrVVal : ShrinkV Value :=
{|
  shrinkV vv :=
    match vv with
      | Var lab (Vint i) (Vint _) =>
        List.map (fun i => Var lab (Vint i) (Vint i)) (shrink i)
      | Var lab (Vptr p) (Vptr _) =>
        List.map (fun p => Var lab (Vptr p) (Vptr p)) (shrinkPointer p)
      | Var lab (Vlab l) (Vlab _) =>
        List.map (fun l => Var lab (Vlab l) (Vlab l)) (shrinkLabel l)
      | _ => nil
    end
|}.

Definition shrinkVLabeled {A B : Type} (c : B -> Label -> A) (b b' : B)
           (l lab : Label) : list (@Variation A) :=
  flat_map (fun ls =>
    if flows ls lab then
      [Var lab (c b ls) (c b ls);
       Var lab (c b' ls) (c b' ls)]
    else
      [Var lab (c b ls) (c b' ls)]
  ) (shrinkLabel l).

Instance shrVAtom : ShrinkV Atom :=
{|
  shrinkV va :=
    let '(Var lab (Atm v l) (Atm v' l')) := va in
    if flows l lab then
      List.map (fun v => let '(Var _ v1 v2) := v in
                    Var lab (Atm v1 l) (Atm v2 l')) (shrinkV (Var lab v v'))
    else
      let a1s := List.map (fun v1 => Atm v1 l) (shrinkValue v)  in
      let a2s := List.map (fun v2 => Atm v2 l) (shrinkValue v') in
      List.map (fun a => Var lab a (Atm v' l')) a1s ++
      List.map (fun a' => Var lab (Atm v l) a') a2s ++
      concat (List.map (fun a => List.map (fun a' => Var lab a a') a2s) a1s)
    ++ shrinkVLabeled Atm v v' l lab
|}.

Fixpoint shrink_datas (lab : Label) (ds ds' : list Atom) :=
  match ds, ds' with
    | h1 :: t1, h2 :: t2 =>
      Var lab t1 t2 ::
      List.map (fun x => let '(Var _ h1' h2') := x in
                    Var lab (h1':: t1) (h2'::t2)) (shrinkV (Var lab h1 h2))
      ++ List.map (fun x => let '(Var _ t1' t2') := x in
                       Var lab (h1::t1') (h2::t2')) (shrink_datas lab t1 t2)
    | _, _ => nil
  end.

Definition shrinkListAtom := shrinkList shrinkAtom.

(* Probably need to revisit this *)
Instance shrVFrame : ShrinkV frame :=
{|
  shrinkV vf :=
    let '(Var obs (Fr stmp lab data1) (Fr stmp2 lab2 data2)) := vf in
    if isLow lab obs then
      List.map (fun x => let '(Var _ ds1 ds2) := x in
                    Var lab (Fr stmp lab ds1) (Fr stmp2 lab2 ds2))
          (shrink_datas obs data1 data2)
    else
      List.map (fun data1' => Var lab (Fr stmp lab data1') (Fr stmp2 lab2 data2))
          (shrinkListAtom data1) ++
      List.map (fun data2' => Var lab (Fr stmp lab data1) (Fr stmp2 lab2 data2'))
          (shrinkListAtom data2)
|}.

(*
Fixpoint liftFrameMem (mf : mframe) (l : Label) (m1 m2 : mem)
         (lf : list (@Variation Frame)) :=
  match lf with
    | [] => []
    | (Var lab f1' f2') :: t =>
      match update_frame m1 mf f1', update_frame m2 mf f2' with
        | Some m1', Some m2' => (Var lab m1' m2')
                                  :: (liftFrameMem mf l m1 m2 t)
        | _, _ => liftFrameMem mf l m1 m2 t
      end
  end.

Fixpoint shr_v_mem (lim : nat) (mf : mframe) (l : Label) (m1 m2 : mem) :=
  match lim with
    | O => nil
    | S lim' =>
      match load_frame m1 mf, load_frame m2 mf with
        | Some f1, Some f2 =>
          app (liftFrameMem mf l m1 m2 (shrinkV (Var l f1 f2)))
                 (shr_v_mem lim' (Zsucc mf) l m1 m2)
        | _, _ => nil
      end
  end.

Instance shrVMem : ShrinkV mem :=
{|
  shrinkV vm :=
    match vm with
      | Var lab m1 m2 =>
        app (shr_v_mem 42 Z0 lab m1 m2)
            nil
    end
|}.
*)
Fixpoint stackLength (s : Stack) :=
  match s with
    | Mty => 0
    | RetCons _ s' => 1 + stackLength s'
  end.

Function shrink_stacks (lab : Label) (sp : Stack * Stack )
         {measure (fun sp => stackLength (fst sp) + stackLength (snd sp)) sp}:=
  (* TODO: Think about shrinking individual stack info *)
  let (s1, s2) := sp in
  match s1, s2 with
    | RetCons h1 t1, RetCons h2 t2 =>
      let '(pc1, _ , _ , _ ) := h1 in
      let '(pc2, _ , _ , _ ) := h2 in
      if flows (pc_lab pc1) lab && flows (pc_lab pc2) lab then
        (* Both are low *)
        flat_map (fun vt => let '(Var lab t1' t2') := vt in
                            [ Var lab (RetCons h1 t1') (RetCons h2 t2') ;
                              Var lab t1' t2' ])
                 (shrink_stacks lab (t1, t2))
      else if flows (pc_lab pc1) lab then
        (* Mach 2 is high *)
        shrink_stacks lab (s1, t2)
      else
        (* Mach 1 is high *)
        shrink_stacks lab (t1, s2)
    | _, _ => nil
  end.
Proof.
intros; unfold fst; unfold snd; unfold stackLength; simpl; omega.
intros; unfold fst; unfold snd; unfold stackLength; simpl; omega.
intros; unfold fst; unfold snd; unfold stackLength; simpl; omega.
Defined.

Instance shrVStack : ShrinkV Stack :=
{|
  shrinkV vs :=
    let '(Var lab s1 s2) := vs in
    shrink_stacks lab (s1, s2)
|}.

(*
Fixpoint liftMemState (st1 st2 : State) (lm : list (@Variation mem)) :=
  match st1, st2 with
    | St _ p1 s1 regs1 pc1, St _ p2 s2 regs2 pc2 =>
      match lm with
        | nil => nil
        | cons (Var lab m1' m2') t =>
          cons (Var lab (St m1' p1 s1 regs1 pc1) (St m2' p2 s2 regs2 pc2))
               (liftMemState st1 st2 t)
      end
  end.
*)

Fixpoint liftStackState (st1 st2 : State) (ls : list (@Variation Stack)) :=
  match st1, st2 with
    | St im1 m1 _ regs1 pc1, St im2 m2 _ regs2 pc2 =>
      match ls with
        | nil => nil
        | cons (Var lab s1' s2') t =>
          cons (Var lab (St im1 m1 s1' regs1 pc1) (St im2 m2 s2' regs2 pc2))
               (liftStackState st1 st2 t)
      end
  end.

(*
Definition shrinkStateMemory (v : @Variation State) :=
  let '(Var lab st1 st2) := v   in
  let '(St _ m  p  s  regs1 pc ) := st1 in
  let '(St _ m' p' s' regs2 pc') := st2 in
  liftMemState st1 st2 (shrinkV (Var lab m m')).
*)

Definition shrinkStateStack (v : @Variation State) :=
  let '(Var lab st1 st2) := v in
  let '(St _ _ s  _ _) := st1 in
  let '(St _ _ s' _ _) := st2 in
  liftStackState st1 st2 (shrinkV (Var lab s s')).

Definition shrinkState x :=
  (* shrinkStateMemory x ++ *) shrinkStateStack x.

Definition cDecr (lim r : regId) :=
  if (lim <=? r)%Z then (r - 1)%Z else r.

Definition decrRegInstr (r : regId) (i : @Instr Label) :=
  match i with
  | Lab r1 r2 => Lab (cDecr r r1) (cDecr r r2)
  | MLab r1 r2 => MLab (cDecr r r1) (cDecr r r2)
  | PcLab r1 => PcLab (cDecr r r1)
  | BCall r1 r2 r3 => BCall (cDecr r r1) (cDecr r r2) (cDecr r r3)
  | BRet => BRet
  | PutLab l r1 => PutLab l (cDecr r r1)
  | Nop => Nop
  | Put n r1 => Put n (cDecr r r1)
  | BinOp o r1 r2 r3 => BinOp o (cDecr r r1) (cDecr r r2) (cDecr r r3)
  | Jump r1 => Jump (cDecr r r1)
  | BNZ n r1 => BNZ n (cDecr r r1)
  | Load r1 r2 => Load (cDecr r r1) (cDecr r r2)
  | Store r1 r2 => Store (cDecr r r1) (cDecr r r2)
  | Write r1 r2 => Write (cDecr r r1) (cDecr r r2)
  | Alloc r1 r2 r3 => Alloc (cDecr r r1) (cDecr r r2) (cDecr r r3)
  | PSetOff r1 r2 r3 => PSetOff (cDecr r r1) (cDecr r r2) (cDecr r r3)
  | Halt => Halt
  | MSize r1 r2 => MSize (cDecr r r1) (cDecr r r2)
  | PGetOff r1 r2 => PGetOff (cDecr r r1) (cDecr r r2)
  | Mov r1 r2 => Mov (cDecr r r1) (cDecr r r2)
  end.

(* TODO
Fixpoint decrRegInFrames (m : mem) (fs : list mframe) (r : regId) :=
  match fs with
    | []   => m
    | h::t =>
      match load_frame m h with
        | Some (CFR is) =>
          match update_frame m h (CFR (map (decrRegInstr r) is)) with
            | Some m' =>
              decrRegInFrames m' t r
            | _ => decrRegInFrames m t r
          end
        | _ => decrRegInFrames m t r
      end
end.

Definition removeReg (st : State) (r : regId) :=
  let '(St m p s rs pc) := st in
  let rn := Z.to_nat r in
  let rsHd := firstn rn rs in
  let rsTl := skipn (S rn) rs in
  St (decrRegInFrames m (allocated m) r) p s (rsHd ++ rsTl) pc.
*)
Fixpoint shrinkVRegContents (l : Label) (prev prev' rest rest' : regSet)
: list (@Variation regSet) :=
  match rest, rest' with
    | h1 :: t1, h2 :: t2 =>
      let shrunk := shrinkV (Var l h1 h2) in
      List.map (fun v' =>
        let '(Var _ h1' h2') := v' in
        Var l (rev_append prev  (h1'::t1))
              (rev_append prev' (h2'::t2))
      ) shrunk ++ shrinkVRegContents l (h1 :: prev) (h2 :: prev') t1 t2

    | _, _ => nil
  end.

Fixpoint liftRegsState (st1 st2 : State) (ls : list (@Variation regSet)) :=
  match st1, st2 with
    | St im1 m1 s1 _ pc1, St im2 m2 s2 _ pc2 =>
      match ls with
        | nil => nil
        | cons (Var lab regs1' regs2') t =>
          cons (Var lab (St im1 m1 s1 regs1' pc1) (St im2 m2 s2 regs2' pc2))
               (liftRegsState st1 st2 t)
      end
  end.

Definition shrinkVRegs (v : @Variation State) :=
    let '(Var l st st') := v in
    let '(St _ _ _ regs _) := st in
    let '(St _ _ _ regs' _) := st' in
(*    let regsNo := List.length regs - 1 in
    let allRegs := map Z.of_nat (seq 0 regsNo) in
    let sts  := map (removeReg st ) allRegs in
    let sts' := map (removeReg st') allRegs in
    map (fun x : (State * State) =>
           let (st1,st2) := x in Var l st1 st2) (combine sts sts') ++*)
    (liftRegsState st st' (shrinkVRegContents l nil nil regs regs')).

Definition shrinkVState (x : @Variation State) :=
  shrinkState x
(*  ++ concat (map shrinkStateMemory (shrinkStateMemory x))
  ++ concat (map shrinkStateMemory (shrinkStateStack x))
  ++ concat (map shrinkStateStack  (shrinkStateMemory x))*)
  ++ shrinkVRegs x.
(*
Definition shrinkObsVar v :=
    let '(V lab st st' mf fm1 fm2) := v in
    let x := obsVarToVar v in
    map (varToObsVar mf fm1 fm2) (shrinkVState x).
*)
