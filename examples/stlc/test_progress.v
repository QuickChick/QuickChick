Require Import QuickChick.
Require Import ssreflect ssrbool.
Require Import String. (* ?? *)
Require Import monad lambda.


(* Note : In general we would need a type checking/inferring function for this.
          Since our generator only generates well-typed terms this is not needed
          for this example. However, it would be nice to have one for other examples.*) 

Definition is_some {A} (o : option A) : bool :=
  match o with 
    | Some _ => true
    | None => false
  end.

Definition has_progress (t : term) := is_value t || (is_some (step t)).

QuickCheck (forAll gen_type (fun tau => 
                               forAll (gen_term tau) has_progress)).

Fixpoint step_bug (t : term) : option term :=
  match t with
    | Const _ | Id _ => None | Abs x => None
    | App t1 t2 =>
      if is_value t1 then 
        match t1 with 
          | Abs t => 
            if is_value t2 then ret (subst 0 t1 t)
            else None
          | _ => None
        end
      else
        t1' <- step t1;;
        ret (App t1' t2)
  end.

Definition has_progress_bug (t : term) := is_value t || (is_some (step_bug t)).

QuickCheck (forAll gen_type (fun tau => 
                               forAll (gen_term tau) has_progress_bug)).