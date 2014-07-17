Require Import QuickChick Gen.

Require Import Machine.

Require Import List.
Require Import ZArith.
Require Import String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

(* List notations - isn't there a way to import these?! *)
Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.

(* Helper functions *) 
Definition flip {A B C : Type} (f : A -> B -> C) (x : B) (y : A) : C := f y x.
Definition compose {A B C : Type} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).
Notation " f << g " := (compose f g) (at level 42). (* F# style, because . *)

Section GenUtils.
  Context {Gen : Type -> Type}
          `{GenMonad Gen}.

Definition pure {A : Type} (x : A) : Gen A := returnGen x.

(* This is provided by the interface *)
(* Definition sequenceGen {A : Type} (ms : list (Gen A)) : Gen (list A) := *)
(*   fold_right (fun m m' => bindGen m  (fun x =>  *)
(*                           bindGen m' (fun xs => *)
(*                           returnGen (x :: xs)))) (pure []) ms. *)

Fixpoint foldGen {A B : Type} (f : A -> B -> Gen A) (l : list B) (a : A) 
: Gen A :=
  match l with
    | [] => returnGen a
    | (x :: xs) => bindGen (f a x) (foldGen f xs)
  end.

End GenUtils.

(* Variation stuff - should be deleted *)
Inductive Variation {A : Type} :=
| Var : Label -> A -> A -> Variation.

Class ShrinkV (A : Type) := { shrinkV : @Variation A -> list (@Variation A) }.
(* End of to be deleted *)

(* List helpers *)
Fixpoint concat {A : Type} (l : list (list A)) : (list A) :=
  match l with
    | [] => []
    | (h :: t) => h ++ concat t
  end.

Fixpoint powerset {A : Type} (l : list A) : (list (list A)) :=
  match l with
    | [] => [[]]
    | h::t => 
      let p := powerset t in
      map (cons h) p ++ p
  end.

Fixpoint forallb2 {A : Type} (f : A -> A -> bool) (l1 l2 :list A) : bool :=
  match l1, l2 with
    | nil, nil => true
    | h1::t1, h2::t2 => f h1 h2 && forallb2 f t1 t2
    | _, _ => false
  end.

(* Label helpers *)
Definition lab_of_list (l : list Z) : Label :=
  fold_left (fun a b => Zset.add b a) l Zset.empty.

(* Short for a label l to be low/high compared to an observability label obs *)
Definition isLow  (l obs : Label) := flows l obs.
Definition isHigh (l obs : Label) := negb (isLow l obs).

Fixpoint list_of_option {A : Type} (l : list (option A)) : list A :=
  match l with
    | nil => nil
    | Some h :: t => h :: list_of_option t
    | None :: t => list_of_option t
  end.

Fixpoint optOfList {A : Type} (l : list (option A)) (acc : list A)
: option (list A) :=
  match l with
    | nil  => Some acc
    | None::_ => None
    | Some h :: t => optOfList t (h :: acc)
  end.

Definition option_bind {X Y} (f : X -> option Y) (o : option X) :=
  match o with
  | Some x => f x
  | None => None
  end.

Definition validJump (st : State) (addr : Z) :=
  let '(St imem _ _ _ _ _) := st in
  (Z.to_nat addr) <? (List.length imem).

Fixpoint containsRet (stk : Stack) :=
  match stk with
    | Mty => false
    | RetCons _ _ => true
  end.

Definition incr_ptr (p : Pointer) :=
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

Definition label_eq l1 l2 := flows l1 l2 && flows l2 l1.

Definition indistLabel (l1 l2 : Label) := label_eq l1 l2.

Definition mframe_eq (m1 m2 : mframe) : bool := 
  if Mem.EqDec_block m1 m2 then true else false.

Instance allBelow : AllThingsBelow Label :=
{|
  allThingsBelow l := map label_of_list (powerset (Zset.elements l))
|}.
