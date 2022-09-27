From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Open Scope string_scope.

Class ShowS (A: Set): Type := {
  shows: A -> string -> string
}.

Module Test1.

Inductive T := | A : T | B : T -> T.
Derive (Show, Arbitrary, Sized) for T.

(* Print ShowT. *)

Instance ShowST: ShowS T := {
  shows :=
    fun x =>
      let fix aux (x': T) (str: string): string :=
            match x' with 
            | A => "A"%string ++ str
            | B t => 
              (* smart parens *)
              match t with
              | A => "B A"%string ++ str
              | B _ => "B"%string ++ " "%string ++ "(" ++ aux t str ++ ")"
              end
            end
      in aux x
}.

(* Eval cbv in (shows (B A) ""). *)
Locate "genST".
Check @arbitraryST.

Inductive Trivial : T -> Prop :=
| trivial : forall t, Trivial t. 

Derive ArbitrarySizedSuchThat for (fun t => Trivial t).

Definition ShowST_correct_prop :=
  forAllMaybe (genST (fun (t: T) => Trivial t)) (fun (t: T) =>
  (show t = shows t "")?
  ).

(* QuickChick ShowST_correct_prop. *)

(* SOLVED
Definition bad1: T := B A.
Eval cbv in (shows bad1 ""). *)

(* SOLVED 
Definition bad1: T := B (B (B A)).
Eval cbv in (show bad1).
Eval cbv in (shows bad1 ""). *)

End Test1.

(* Section Test2. *)

Inductive T : Set := 
| A : T
| B : T -> T -> T.

Derive Show for T.

Definition compose {A B C} (g : B -> C) (f : A -> B) (x: A): C := g (f x).

Instance ShowST: ShowS T := {
  shows := 
    fun x =>
    let 
      fix aux (x': T): string -> string :=
      match x' return string -> string with 
      | A => append "A"%string 
      | B x1 x2 =>
        compose
          (append ("B"%string ++ " ("%string))
          (compose 
            (aux x1)
            (compose
              (append ") ("%string)
              (compose
                (aux x2)
                (append ")")
              )
            )
          )
      end
    in aux x 
}.

Eval cbv in (shows (B (B A A) (B A A)) "").

End Test2.