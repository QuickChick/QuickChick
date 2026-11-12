From QuickChick Require Import QuickChick.

(* A typing relation whose context is a function: a rule may apply it, as in
   [ctx n], and extend it with [fun k => match k with ...]. The application
   becomes an equality premise, and the extended context is computed and
   passed to the recursive check. *)
Inductive ty := TNat | TBool.
#[local] Instance dec_ty (a b : ty) : Dec (a = b). Proof. dec_eq. Defined.

Inductive tm := Var (n : nat) | Lit (n : nat) | Let (a b : tm).

Inductive typed : (nat -> ty) -> tm -> ty -> Prop :=
| TVar ctx n : typed ctx (Var n) (ctx n)
| TLit ctx n : typed ctx (Lit n) TNat
| TLet ctx a b t1 t2 : typed ctx a t1 ->
    typed (fun k => match k with 0 => t1 | S k => ctx k end) b t2 ->
    typed ctx (Let a b) t2.

QuickChick Derive Checker for (typed ctx e t).

Definition ctx0 (n : nat) := match n with 0 => TBool | _ => TNat end.

Example checks :
  (decOpt (P := typed ctx0 (Var 0) TBool) 5, decOpt (P := typed ctx0 (Var 0) TNat) 5,
   decOpt (P := typed ctx0 (Let (Lit 1) (Var 0)) TNat) 5,
   decOpt (P := typed ctx0 (Let (Lit 1) (Var 1)) TBool) 5,
   decOpt (P := typed ctx0 (Let (Lit 1) (Var 1)) TNat) 5)
  = (Some true, Some false, Some true, Some true, Some false).
Proof. vm_compute. reflexivity. Qed.
