Require Import String.
Require Import List. Import ListNotations.
Require Import MSetPositive.
Require Import ZArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Require Import QuickChick.

Require Import Common.
Require Import Indist.

(* High-level note:
   Deal with printing variations of stuff, then instantiate the
   single show instances with a variation of the same thing.
   Hacky, slightly less efficient - but allows for code reuse.
   Otherwise, the single instances ``belong'' before the indist file.
*)

Local Open Scope string.

Axiom show_pos : positive -> string.
Instance showPos : Show positive :=
{|
  show := show_pos
|}.

Instance show_label : Show Lab4 :=
{|
  show lab := match lab with
                | L  => "L"
                | M1 => "M1"
                | M2 => "M2"
                | H  => "H"
              end
|}.

Instance show_bin_op : Show BinOpT :=
{|
  show x := "Binop " ++ (
            match x with
              | BAdd => "+"
              | BMult => "*"
              | BFlowsTo => "<:"
              | BJoin => "\/"
              | BEq => "="
            end)
|}.

Instance show_instr : Show (@Instr Label) :=
{|
  show i :=
    match i with
    | Lab r1 r2 => "Lab " ++ show r1 ++ " " ++ show r2
    | MLab r1 r2 => "MLab " ++ show r1 ++ " " ++ show r2
    | PcLab r1 => "PcLab " ++ show r1
    | BCall r1 r2 r3 => "BCall " ++ show r1 ++ " " ++ show r2 ++ " " ++ show r3
    | BRet => "BRet"
    | PutLab l r => "PutLab " ++ show l ++ " " ++ show r
    | Nop => "Nop"
    | Put n r1 => "Push " ++ show n ++ " " ++ show r1
    | BinOp o r1 r2 r3 => show o ++ " " ++ show r1 ++ " "
                               ++ show r2 ++ " " ++ show r3
    | Jump r1 => "Jump " ++ show r1
    | BNZ n r1 => "BNZ " ++ show n ++ " " ++ show r1
    | Load r1 r2 => "Load " ++ show r1 ++ " " ++ show r2
    | Store r1 r2 => "Store " ++ show r1 ++ " " ++ show r2
    | Write r1 r2 => "Write " ++ show r1 ++ " " ++ show r2
    | Alloc r1 r2 r3 =>
      "Alloc " ++ show r1 ++ " " ++ show r2 ++ " " ++ show r3
    | PSetOff r1 r2 r3 =>
      "PSetOff " ++ show r1 ++ " " ++ show r2 ++ " " ++ show r3
    | Halt => "Halt"
    | MSize r1 r2 => "MSize " ++ show r1 ++ " " ++ show r2
    | PGetOff r1 r2 => "PGetOff " ++ show r1 ++ " " ++ show r2
    | Mov r1 r2 => "Mov " ++ show r1 ++ show r2
    end
|}.

Instance show_op_code : Show OpCode :=
{|
  show op :=
    match op with
    | OpLab => "OpLab"
    | OpMLab => "OpMLab"
    | OpPcLab => "OpPcLab"
    | OpBCall => "OpBCall"
    | OpBRet => "OpBRet"
    | OpPutLab => "OpPutBot"
    | OpNop => "OpNop"
    | OpPut => "OpPut"
    | OpBinOp => "OpBinOp"
    | OpJump => "OpJump"
    | OpBNZ => "OpBNZ"
    | OpLoad => "OpLoad"
    | OpStore => "OpStore"
    | OpWrite => "OpStore"
    | OpAlloc => "OpAlloc"
    | OpPSetOff => "OpPSetOff"
    | OpPGetOff => "OpPGetOff"
    | OpMSize => "OpMSize"
    | OpMov => "OpMov"
    end
|}.

Instance show_pointer : Show Pointer :=
{|
  show ptr :=
    let '(Ptr x y) := ptr in
    "(f=" ++ show x ++ ";i=" ++ show y ++ ")"
|}.

Instance show_val : Show Value :=
{|
  show val :=
    match val with
      | Vint  v => "Vint  " ++ show v
      | Vptr  v => "Vptr  " ++ show v
      | Vlab  v => "Vlab  " ++ show v
    end
|}.

(* Takes a list and shows it in numbered different lines *)
Fixpoint numed_contents {A : Type} (s : A -> string) (l : list A) (n : nat)
: string :=
  match l with
    | nil => ""%string
    | cons h t => show n ++ " : " ++ s h ++ nl ++ (numed_contents s t (S n))
  end.

Definition par (s : string) := "( " ++ s ++ " )".

Instance show_atom : Show Atom :=
{|
  show a :=
    let '(v @ l) := a in
    show v ++ " @ " ++ show l
|}.

Instance show_Ptr_atom : Show Ptr_atom :=
{|
  show p :=
    let '(PAtm i l) := p in show i ++ " @ " ++ show l
|}.

Instance show_list {A : Type} `{_ : Show A} : Show (list A) :=
{|
  show l := numed_contents show l 0
|}.

Instance show_frame : Show frame :=
{|
  show f :=
    let '(Fr stmp lab data) := f in
    "Stamp: " ++ show stmp ++ " Label: " ++ show lab ++ nl ++
    show data
|}.

Definition show_variation (s1 s2 : string) :=
  "{ " ++ s1 ++ " / " ++ s2 ++ " }".

Class ShowPair (A : Type) : Type :=
{
  show_pair : Lab4 -> A -> A -> string
}.

Instance show_value_pair : ShowPair Value :=
{|
  show_pair lab v1 v2 :=
    if indist lab v1 v2 then show v1
    else show_variation (show v1) (show v2)
|}.

Instance show_label_pair : ShowPair Lab4 :=
{|
  show_pair lab l1 l2 :=
    if label_eq l1 l2 then show l1
    else show_variation (show l1) (show l2)
|}.

Instance show_atom_pair : ShowPair Atom :=
{|
  show_pair lab a1 a2 :=
    let '(v1 @ l1) := a1 in
    let '(v2 @ l2) := a2 in
    show_pair lab v1 v1 ++ " @ "
    ++ show_pair lab l1 l2
|}.

Instance show_ptr_atom_pair : ShowPair Ptr_atom :=
{|
  show_pair lab p1 p2 :=
    if indist lab p1 p2 then
      show p1
    else
      show_variation (show p1) (show p2)
|}.

Fixpoint show_pair_list {A : Type} `{_ : Show A} `{_ : ShowPair A}
         (n : nat) (lab : Lab4)
         (l1 l2 : list A) :=
  match n with
    | O => match l1, l2 with
           | nil, nil => ""
           | _, _ => "[ " end
    | _ => ""
  end ++
  match l1, l2 with
    | [h1], [h2] =>
      show n ++ " : " ++ show_pair lab h1 h2 ++ " ]"
    | h1 :: t1, h2 :: t2 =>
      show n ++ " : " ++ show_pair lab h1 h2 ++ " , " ++
      show_pair_list (S n) lab t1 t2
    | h1 :: t1, [] =>
      "Cont1 : " ++ numed_contents show (h1::t1) (S n) ++ " ]"
    | [], h2 :: t2 =>
      "Cont2 : " ++ numed_contents show (h2 :: t2) (S n)++ " ]"
    | _, _ => "]"
  end.

(* INV: framePairs must be a list of corresponding memory pairs *)
Fixpoint show_mem_pair_helper (frame_pairs : list (mframe * mframe))
         lab (m1 m2 : memory) :=
  match frame_pairs with
    | [] => ""
    | (f1, f2) :: t =>
      (* Show mframes *)
      (if Mem.EqDec_block f1 f2 then show f1
      else show_variation (show f1) (show f2)) ++ (
      (* Show actual corresponding frames *)
      match Mem.get_frame m1 f1, Mem.get_frame m2 f2 with
        | Some (Fr stmp1 l1 data1), Some (Fr stmp2 l2 data2) =>
          (if label_eq stmp1 stmp2 then
            (* same stamps *)
            "Stamp: " ++ show stmp1
          else "Stamp: " ++ show_variation (show stmp1) (show stmp2)) ++
          (if label_eq l1 l2 then
            "DFR @ " ++ show l1 ++ " : [ "
                     ++ show_pair_list 0 lab data1 data2 ++ nl
                     ++ show_mem_pair_helper t lab m1 m2 ++ " ]"
          else
            "DFR @ " ++ (show_variation (show l1) (show l2)) ++ " : [ "
                     ++ (show_pair_list 0 lab data1 data2) ++ nl
                     ++ show_mem_pair_helper t lab m1 m2) ++ " ]"
        | Some (Fr stmp1 l1 data1), None =>
          "Frame " ++ show f1 ++ " corresponds to " ++ nl
                   ++ show stmp1 ++ ", " ++ show l1 ++ " : [ "
                   ++ show data1 ++ nl
        | None, Some (Fr stmp2 l2 data2) =>
          "Frame " ++ show f2 ++ " corresponds to " ++ nl
                   ++ show stmp2 ++ ", " ++ show l2 ++ " : [ "
                   ++ show data2 ++ nl
        | _, _ => "Bad frames: " ++ show f1 ++ " vs "++ show f2
      end)
  end.

Definition show_high_frames m (mfs : list mframe) :=
  let fix aux (mfs : list mframe) :=
      match mfs with
        | [] => ""
        | h :: t =>
          match Mem.get_frame m h with
            | Some f => par (show h) ++ " : " ++ show f ++ nl ++ aux t
            | _ => "ERROR SHOWING EXTRA FRAMES"
          end
      end in
  match mfs with
    | [] => ""
    | _ => aux mfs
  end.

Definition show_pair_mem (obs : Label) (m1 m2 : memory)
: string :=
  let frames1 := Mem.get_blocks elems m1 in
  let high1 := filter (fun mf => isHigh (Mem.stamp mf) obs) frames1 in
  let low1  := filter (fun mf => isLow  (Mem.stamp mf) obs) frames1 in
  let frames2 := Mem.get_blocks elems m2 in
  let high2 := filter (fun mf => isHigh (Mem.stamp mf) obs) frames2 in
  let low2  := filter (fun mf => isLow  (Mem.stamp mf) obs) frames2 in
  "DEBUG: " ++ nl ++
  "fst: " ++ show frames1 ++ nl ++
  "snd: " ++ show frames2 ++ nl ++
  show_mem_pair_helper (combine frames1 frames2) obs m1 m2 ++ nl ++
  show_high_frames m1 high1 ++ nl ++
  show_high_frames m2 high2 ++ nl.

(* Keep top separates the high prefix of the stack
   INV : Assumes well formed! (fix?) CH: yes!
*)
Fixpoint keep_top (lab : Lab4) (s : Stack) :=
  match s with
    | Mty => (Mty, Mty)
    | RetCons (pc, a,b,c) s' =>
      if flows (pc_lab pc) lab then (Mty, s)
      else let (h,l) := keep_top lab s' in (RetCons (pc,a,b,c) h, l)
  end.

Fixpoint show_single_stack s :=
  match s with
    | Mty => ""
    | RetCons (pc, l, rs, r) s' =>
      "RetPC: " ++ show pc ++ nl ++
      "RetLAB: " ++ show l ++ nl ++
      "RetRegs: " ++ show rs ++ nl ++
      "RetReg : " ++ show r ++ nl ++
      show_single_stack s'
  end.

(* Could be a new instance with a "newtype"? *)
Fixpoint show_low_stack_pair lab s1 s2 :=
  match s1, s2 with
    | Mty, Mty => " ] "
    | RetCons (p1, l1, r1, t1) s1', RetCons (p2, l2, r2, t2) s2' =>
      "RetPC: "   ++ show_pair lab p1 p1 ++ nl ++
      "RetLab: "  ++ show_pair lab l1 l2 ++ nl ++
      "RetRegs: " ++ show_pair_list 0 lab r1 r2 ++ nl ++
      "RetReg: "  ++ (if Z.eq_dec t1 t2 then show t1 else
                        show_variation (show t1) (show t2)) ++
      show_low_stack_pair lab s1' s2'
    | Mty, s => "Unequal stack 2: " ++ nl ++ show_single_stack s
    | s, Mty => "Unequal stack 1: " ++ nl ++ show_single_stack s
  end.

Instance show_stack_pair : ShowPair Stack :=
{|
  show_pair lab s1 s2 :=
    let (h1,l1) := keep_top lab s1 in
    let (h2,l2) := keep_top lab s2 in
    (match h1 with
       | Mty => ""
       | _ => "High part of stack 1: [ " ++ show_single_stack h1 ++ "]" ++ nl
     end
    ) ++
    (match h2 with
       | Mty => ""
       | _ => "High part of stack 2: [ " ++ show_single_stack h2 ++ "]" ++ nl
     end
    ) ++
    "Low-comparable stack parts: [ " ++
    show_low_stack_pair lab l1 l2 ++ "]" ++ nl
|}.

Instance show_state_pair : ShowPair State :=
{|
  show_pair lab st1 st2 :=
    let '(St im1 m1 s1 r1 pc1) := st1 in
    let '(St im2 m2 s2 r2 pc2) := st2 in
    "Instructions: " ++ show im1 ++ nl ++
    "PC: "  ++ show_pair lab pc1 pc2 ++ nl ++
    "Mem: " ++ nl ++
       show_pair_mem lab m1 m2 ++ nl ++
    "Regs: " ++ nl ++
       show_pair_list 0 lab r1 r2 ++ nl ++
    "Stacks: " ++ nl ++
       show_pair lab s1 s2
|}.

Instance show_variation_instance : Show Variation :=
{|
  show v := let '(Var lab st1 st2) := v in
            "Obs level:" ++ show lab ++ nl ++ show_pair lab st1 st2
|}.

Fixpoint show_execution (lab : Lab4)
         (sts1 sts2 : list State) :=
  match sts1, sts2 with
    | h1::t1, h2::t2 =>
      "-=Step=-" ++ nl ++
      show_pair lab h1 h2 ++ nl ++
      show_execution lab t1 t2
    | [], [] => ""
    | [], _ => "Mach 2 continues: FIXME"
    | _, [] => "Mach 1 continues: FIXME"
  end.
