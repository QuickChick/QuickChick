From QuickChick Require Import QuickChick.

Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  | merge_empty :
      merge nil nil nil
  | merge_left : forall l1 l2 l3 x,

      merge l1 l2 l3 ->
      merge (x::l1) l2 (x::l3)
  | merge_right : forall l1 l2 l3 x,
      merge l1 l2 l3 ->
      merge l1 (x::l2) (x::l3).

Derive Instance DecOpt for (merge l1 l2 l3).
Derive Instance ArbitrarySizedSuchThat for (fun l3 => merge l1 l2 l3).
Derive Instance EnumSizedSuchThat for (fun l3 => merge l1 l2 l3).

Inductive In' {A:Type} : A -> list A -> Prop :=
| In_hd :
    forall x l, In' x (cons x l)
| In_tl :
    forall x y l, In' x l -> In' x (cons y l).

Derive Instance EnumSizedSuchThat for (fun x => In' x l).
Derive Instance DecOpt for (In' x l).
