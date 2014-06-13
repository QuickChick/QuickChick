Require Import ZArith List ssreflect ssrbool ssrnat.
Require Import Axioms AbstractGen.
Import ListNotations.

Set Implicit Arguments.

Record Lazy (T : Type) := lazy { force : T }.

Inductive Gen (A : Type) : Type :=
| MkGen : (RandomGen -> nat -> A) -> Gen A.

(* Consider making this a part of the common interface *)
Definition fmapGen {A B : Type} (f : A -> B) (g : Gen A) : Gen B :=
  match g with
    | MkGen h => MkGen (fun r n => f (h r n))
  end.

Program Instance realGen : GenMonad Gen :=
  { 
    bindGen A B g k :=
      match g with
        | MkGen m =>
          MkGen (fun r n =>
               let (r1,r2)  := rndSplit r in
               let '(MkGen m') := k (m r1 n) in
               m' r2 n
            )
      end;
    returnGen A x :=
      MkGen (fun _ _ => x);
    choose A R range := 
      MkGen (fun r _ => fst (randomR range r));
    sized A f := 
      MkGen (fun r n => match f n with MkGen m => m r n end)
  }.


(*
Require Import Monad.

Instance functorGen : Functor Gen :=
{|
  fmap := fun _ _ f g =>
    match g with 
      | MkGen h => 
        MkGen (fun r n => f (h r n))
    end
|}.

Instance monadGen : Monad Gen :=
{|
  return_ := fun _ x => MkGen (fun _ _ => x);
  bind    := fun _ _ g k =>
               match g with
                 | MkGen m =>
                   MkGen (fun r n =>
                            let (r1,r2)  := rndSplit r in
                            match k (m r1 n) with
                              | MkGen m' => m' r2 n
                            end
                         )
               end
|}.
*)             


(* This could be added at the typeclass too *)
Definition promote {M : Type -> Type} {A : Type}
           (liftFun : (Gen A -> A) -> M (Gen A) -> M A) 
           (m : M (Gen A)) : Gen (M A) :=
  MkGen (fun r n => liftFun (fun g => match g with MkGen m' => m' r n end) m).

Fixpoint rnds (rnd : RandomGen) (n' : nat) : list RandomGen :=
  match n' with
    | O => nil
    | S n'' => 
      let (rnd1, rnd2) := rndSplit rnd in
      cons rnd1 (rnds rnd2 n'')
  end.

Fixpoint createRange (n : nat) (acc : list nat) : list nat :=
  match n with 
    | O => List.rev (cons O acc)
    | S n' => createRange n' (cons n acc)
  end.

Definition sample' (A : Type) (g : Gen A) : list A :=
  match g with
    | MkGen m => 
      let rnd := mkRandomGen 0 in
      let l := List.combine (rnds rnd 20) (createRange 20 nil) in
      List.map (fun (p : RandomGen * nat) => let (r,n) := p in m r n) l
  end.

Definition resize {A : Type} (n : nat) (g : Gen A) : Gen A :=
  match g with
    | MkGen m => MkGen (fun r _ => m r n)
  end.

