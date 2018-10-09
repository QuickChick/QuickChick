From QuickChick Require Import QuickChick.

Require Import ZArith.
Require Import NPeano.
Require Import List.
Import ListNotations.
From QuickChick.ifcbasic Require Import Machine.

(* Overriding default instance to generate "in-bounds" things *)
Definition mem_length : Z := 10.

Definition gen_Z := choose (0,mem_length).

Definition gen_label := elems_ L [L; H].

Definition gen_atom := liftGen2 Atm gen_Z gen_label.

Definition gen_memory := vectorOf 10 gen_atom.

Definition is_atom_low (a : Atom) :=
  match a with
    | _ @ L => true
    | _     => false
  end.

Local Open Scope nat.

Definition ainstr (st : State) (fuel : nat) : G Instruction :=
  let '(St im m stk pc ) := st in
  let fix stack_length s :=
      match s with
        | _ :: s' => 1 + stack_length s'
        | _ => 0
      end in
  let sl := stack_length stk in
  let fix containsRet s :=
      match s with
        | _ ::: _ => true
        | _ :: s' => containsRet s'
        | _ => false
      end in
  
  freq_ (returnGen Nop) [
          (1, returnGen Nop);
          (if is_atom_low pc then (20 - fuel) * (20 - fuel) else 0, returnGen Halt);
          (40, liftGen Push gen_Z);
          (if sl < 1 ? then 0 else 40,
           liftGen BCall (if beq_nat sl 0 then returnGen 0
                          else choose (0, Z.of_nat sl))%Z);
          (if containsRet stk then 40 else 0, returnGen BRet);
          (if sl < 2 ? then 0 else 40, returnGen Add);
          (if sl < 1 ? then 0 else 40, returnGen Load);
          (if sl < 2 ? then 0 else 60, returnGen Store)].

Fixpoint gen_stack (n : nat) (onlyLow : bool) : G Stack :=
  match n with
    | O => returnGen Mty
    | S n' =>
      freq_ (returnGen Mty) [
                  (10, liftGen2 Cons gen_atom (gen_stack n' onlyLow));
                  (2, bindGen gen_atom (fun pc =>
                       liftGen (RetCons pc) (gen_stack n' (is_atom_low pc))))]
  end.

Fixpoint gen_by_exec (t : table) (fuel : nat) (st : State) :=
  let '(St im m stk (Atm addr pcl)) := st in
  match fuel with
  | O => returnGen st
  | S fuel' =>
    match nth im addr with
    | Some Nop =>
      (* If it is a noop, generate *)
      bindGen (ainstr st fuel') (fun i =>
      match upd im addr i with
      | Some im' =>
        let st' := St im' m stk (Atm addr pcl) in
        gen_by_exec t fuel' st'
      | None => returnGen st
      end)
    | Some i =>
      (* Existing instruction, execute *)
      match exec t st with
      | Some st' =>
        gen_by_exec t fuel' st'
      | None => returnGen st
      end
    | None =>
      (* Out of bounds, terminate *)
      returnGen st
    end
  end.

Require Import ExtLib.Structures.Monads.
Import MonadNotation.
Open Scope monad_scope.

Fixpoint replace_some_nops imem :=
  match imem with
  | [] => ret []
  | cons Nop imem' =>
    bindGen (@arbitrary bool _) (fun (b : bool) =>
    if b then       
      n <- gen_Z ;;
      liftGen (cons (Push n)) (replace_some_nops imem')
    else
      liftGen (cons Nop) (replace_some_nops imem'))
  | cons i imem' =>
    liftGen (cons i) (replace_some_nops imem')
  end.

Definition gen_state' : G State :=
  let imem0 := replicate 10 Nop in
  pc <- gen_atom ;;
  mem <- gen_memory ;;
  stk <- gen_stack 10 (is_atom_low pc) ;;
  st' <- gen_by_exec default_table 20 (St imem0 mem stk pc) ;;
  let '(St i m s p) := st' in
  (*  i' <- replace_some_nops i ;; *)
  let i' := i in
  ret (St i' m s p).

From QuickChick.ifcbasic Require Generation.

Definition gen_variation_state' : G (@Generation.Variation State) :=
  bindGen gen_state' (fun st =>
  bindGen (Generation.vary st) (fun st' =>
  returnGen (Generation.V st st'))).

