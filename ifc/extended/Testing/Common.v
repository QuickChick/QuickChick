Require Import List. Import ListNotations.
Require Import ZArith.
Require Import String.
Require Import NPeano.

Require Import QuickChick Gen.

Require Import Machine.
Require Import Lab4.

Section GenUtils.
  Context {Gen : Type -> Type}
          `{GenMonad Gen}.

Definition pure {A : Type} (x : A) : Gen A := returnGen x.

Fixpoint foldGen {A B : Type} (f : A -> B -> Gen A) (l : list B) (a : A)
: Gen A :=
  match l with
    | [] => returnGen a
    | (x :: xs) => bindGen (f a x) (foldGen f xs)
  end.

End GenUtils.

(* Variation stuff - should be deleted -- CH: ha? it seems used *)
Inductive Variation {A : Type} :=
| Var : Lab4 -> A -> A -> Variation.

Class ShrinkV (A : Type) := { shrinkV : @Variation A -> list (@Variation A) }.
(* End of to be deleted *)

(* Short for a label l to be low/high compared to an observability label obs *)
Definition isLow  (l obs : Lab4) := flows l obs.
Definition isHigh (l obs : Lab4) := negb (isLow l obs).

Definition validJump (st : @State Lab4) (addr : Z) :=
  let '(St imem _ _ _ _) := st in
  (Z.to_nat addr) <? (List.length imem).

Fixpoint containsRet (stk : @Stack Lab4) :=
  match stk with
    | Mty => false
    | RetCons _ _ => true
  end.

Definition incr_ptr (p : @Pointer Lab4) :=
  let (fp, i) := p in (Ptr fp (Zsucc i)).

(* Simple equalities *)
Definition Z_eq (i1 i2 : Z) : bool :=
  if Z.eq_dec i1 i2 then true else false.

Definition reg_eq_dec : forall r1 r2 : regPtr,
  {r1 = r2} + {r1 <> r2}.
Proof. apply Z_eq_dec. Defined.

Hint Resolve reg_eq_dec.

Definition bin_op_eq_dec : forall b1 b2 : BinOpT,
  {b1 = b2} + {b1 <> b2}.
Proof. decide equality. Defined.

Hint Resolve bin_op_eq_dec.

Definition instr_eq_dec : forall i1 i2 : Instruction,
  {i1 = i2} + {i1 <> i2}.
Proof. decide equality. Defined.

Definition instr_eq i1 i2 := if instr_eq_dec i1 i2 then true else false.

Definition label_eq (l1 l2 : Lab4) := flows l1 l2 && flows l2 l1.

Definition mframe_eq (m1 m2 : @mframe Lab4) : bool :=
  if Mem.EqDec_block m1 m2 then true else false.
