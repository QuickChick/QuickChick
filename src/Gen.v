Require Import ZArith.
Require Import List.

Set Implicit Arguments.

Axiom RandomGen   : Type.
Axiom rndNext     : RandomGen   -> Z * RandomGen.
Axiom rndGenRange : RandomGen   -> Z * Z.
Axiom rndSplit    : RandomGen   -> RandomGen * RandomGen.
Axiom mkRandomGen : Z           -> RandomGen.
Axiom randomRBool : bool * bool -> RandomGen -> bool * RandomGen.
Axiom randomRNat  : nat  * nat  -> RandomGen -> nat  * RandomGen.
Axiom randomRInt  : Z    * Z    -> RandomGen -> Z    * RandomGen.
Axiom newStdGen   : RandomGen.

Inductive Gen (A : Type) : Type :=
| MkGen : (RandomGen -> nat -> A) -> Gen A.

Definition fmapGen {A B : Type} (f : A -> B) (g : Gen A) : Gen B :=
  match g with
    | MkGen h => MkGen (fun r n => f (h r n))
  end.

Definition returnGen (A : Type) (x : A) : Gen A := 
  MkGen (fun _ _ => x).

Definition bindGen (A B : Type) (g : Gen A) (k : A -> Gen B) : Gen B :=
  match g with
    | MkGen m =>
      MkGen (fun r n =>
               let (r1,r2)  := rndSplit r in
               let '(MkGen m') := k (m r1 n) in
               m' r2 n
            )
  end.

Definition liftGen {A B : Type} (C : A -> B) (m : Gen A) : Gen B:=
  bindGen m (fun x => returnGen (C x)).

Definition liftGen2 {A1 A2 R : Type} (C : A1 -> A2 -> R) 
           (m1 : Gen A1) (m2 : Gen A2) 
: Gen R :=
  bindGen m1 (fun x1 => bindGen m2 (fun x2 => returnGen (C x1 x2))).

Definition liftGen3 {A1 A2 A3 R : Type} (F : A1 -> A2 -> A3 -> R)
           (m1 : Gen A1) (m2 : Gen A2) (m3 : Gen A3) 
: Gen R :=
  bindGen m1 (fun x1 =>
  bindGen m2 (fun x2 =>
  bindGen m3 (fun x3 =>
  returnGen (F x1 x2 x3)))).

Definition liftGen4 {A1 A2 A3 A4 R : Type} (F : A1 -> A2 -> A3 -> A4 -> R)
           (m1 : Gen A1) (m2 : Gen A2) (m3 : Gen A3) (m4: Gen A4)
: Gen R :=
  bindGen m1 (fun x1 =>
  bindGen m2 (fun x2 =>
  bindGen m3 (fun x3 =>
  bindGen m4 (fun x4 =>
  returnGen (F x1 x2 x3 x4))))).

Definition liftGen5 {A1 A2 A3 A4 A5 R : Type} (F : A1 -> A2 -> A3 -> A4 -> A5 -> R)
           (m1 : Gen A1) (m2 : Gen A2) (m3 : Gen A3) (m4: Gen A4) (m5 : Gen A5)
: Gen R :=
  bindGen m1 (fun x1 =>
  bindGen m2 (fun x2 =>
  bindGen m3 (fun x3 =>
  bindGen m4 (fun x4 =>
  bindGen m5 (fun x5 =>
  returnGen (F x1 x2 x3 x4 x5)))))).

Definition sequenceGen {A : Type} (ms : list (Gen A)) : Gen (list A) :=
  fold_right (fun m m' => bindGen m  (fun x => 
                          bindGen m' (fun xs =>
                          returnGen (x :: xs)))) (pure []) ms.

Fixpoint foldGen {A B : Type} (f : A -> B -> Gen A) (l : list B) (a : A) 
: Gen A :=
  match l with
    | [] => returnGen a
    | (x :: xs) => bindGen (f a x) (foldGen f xs)
  end.

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

(* This will be ugly, unless I can figure out a way of adding 
haskell typeclass constraints *)
Definition chooseBool (rng : bool * bool) : Gen bool :=
  MkGen (fun r _ => fst (randomRBool rng r)).

Definition chooseNat (rng : nat * nat) : Gen nat :=
  MkGen (fun r _ => fst (randomRNat rng r)).

Definition chooseZ (rng : Z * Z) : Gen Z :=
  MkGen (fun r _ => fst (randomRInt rng r)).

Definition promote {M : Type -> Type} {A : Type}
           (liftFun : (Gen A -> A) -> M (Gen A) -> M A) 
           (m : M (Gen A)) : Gen (M A) :=
  MkGen (fun r n => liftFun (fun g => match g with MkGen m' => m' r n end) m).

Fixpoint rnds (rnd : RandomGen) (n' : nat) :=
  match n' with
    | O => nil
    | S n'' => 
      let (rnd1, rnd2) := rndSplit rnd in
      cons rnd1 (rnds rnd2 n'')
  end.

Fixpoint createRange n acc :=
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

Definition sized (A : Type) (f : nat -> Gen A) : Gen A :=
  MkGen (fun r n => match f n with MkGen m => m r n end).

Definition suchThatMaybe {A : Type} (g : Gen A) (p : A -> bool) :=
  let t := (fix t (n : nat) (k : nat) : Gen (option A) := 
              match n with
                | O => returnGen None
                | S n' => 
                  bindGen (resize (2 * k + n) g) 
                          (fun x => if p x then returnGen (Some x)
                                    else t n' (S k))
              end) in
  sized (fun x => t 0 (max 1 x)).

Definition oneof {A : Type} (def: Gen A) (gs : list (Gen A)) : Gen A :=
  bindGen (chooseNat (0, length gs - 1))
          (fun n => List.nth n gs def).

Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
  match n with
    | O    => nil
    | S n' => cons x (replicate n' x)
  end.

Fixpoint freqRep {A : Type} (gs : list (nat * Gen A)) : list (Gen A) :=
  match gs with
    | nil => nil
    | cons (n, g) t =>
      (replicate n g) ++ freqRep t
  end.

Definition frequency {A : Type} (def : Gen A) (gs : list (nat * Gen A)) :=
  oneof def (freqRep gs).

Definition vectorOf {A : Type} (k : nat) (g : Gen A) : Gen (list A) :=  
  fold_right (fun m m' =>
                bindGen m (fun x => bindGen m' (fun xs => returnGen (cons x xs)))
             ) (returnGen nil) (replicate k g).

Definition listOf {A : Type} (g : Gen A) : Gen (list A) :=
  sized (fun n => bindGen (chooseNat (0, n)) (fun k => vectorOf k g)).

Fixpoint elements {A : Type} (def : A) (l : list A) :=
  let n := length l in
  bindGen (chooseNat (0, n - 1)) (fun n' => returnGen (nth n' l def)).
 
