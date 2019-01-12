Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From QuickChick Require Import QuickChick.
Require Import Arith List. Import ListNotations.

Require Import Stack.Exp.

(* Instructions for our stack machine *)
Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(* Execution *)
Fixpoint execute (stack : list nat) (prog : list sinstr) : list nat :=
  match (prog, stack) with
  | (nil,             _           ) => stack
  | (SPush n::prog',  _           ) => execute (n::stack) prog'
  | (SPlus::prog',    m::n::stack') => execute ((m+n)::stack') prog'
  | (SMinus::prog',   m::n::stack') => execute ((m-n)::stack') prog'
  | (SMult::prog',    m::n::stack') => execute ((m*n)::stack') prog'
  | (_::prog',        _           ) => execute stack prog'
  end.

(* Compilation... *)
Fixpoint compile (e : exp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
(*! *)
  | APlus  e1 e2 => compile e2 ++ compile e1 ++ [SPlus]
  | AMinus e1 e2 => compile e2 ++ compile e1 ++ [SMinus]
  | AMult  e1 e2 => compile e2 ++ compile e1 ++ [SMult]
(*!! Wrong associativity *)
(*!
  | APlus  e1 e2 => compile e1 ++ compile e2 ++ [SPlus]
  | AMinus e1 e2 => compile e1 ++ compile e2 ++ [SMinus]
  | AMult  e1 e2 => compile e1 ++ compile e2 ++ [SMult]
*)
  end.

Definition compiles_correctly (e : exp) := (execute [] (compile e)) = [eval e]?.
(*! QuickChick compiles_correctly. *)