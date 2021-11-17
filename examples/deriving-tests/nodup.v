From QuickChick Require Import QuickChick. 

Inductive In' (A:Type) : A -> list A -> Prop :=
| In_hd :
    forall x l, In' A x (cons x l)
| In_tl :
    forall x y l, In' A x l -> In' A x (cons y l).

Derive DecOpt for (In' a l).
Derive ArbitrarySizedSuchThat for (fun x => In' x l).
Derive EnumSizedSuchThat for (fun x => In' x l).
Derive EnumSizedSuchThat for (fun l => In' x l).

Inductive NoDup {A:Type} : list A -> Prop :=
  | NoDup_nil : NoDup nil
  | NoDup_cons :
      forall a l,
        ~ In' A a l ->
        NoDup l ->
        NoDup (a :: l).


(* XXX LEO Error: Anomaly "Uncaught exception Failure("Simultaneous Some/None")." *)
(* Error: Anomaly "Uncaught exception Failure("Incompatible modes/1")." *)
Derive DecOpt for (NoDup l). 
Derive EnumSizedSuchThat for (fun l => NoDup l). 
Derive ArbitrarySizedSuchThat for (fun l => NoDup l).

Inductive repeats {X:Type} : list X -> Prop :=
  | rep_here : forall a l, In' X a l -> repeats (a::l)
  | rep_later : forall a l, repeats l -> repeats (a::l).

Derive DecOpt for (repeats l). 
Derive ArbitrarySizedSuchThat for (fun l => repeats l). 
Derive EnumSizedSuchThat for (fun l => repeats l).

