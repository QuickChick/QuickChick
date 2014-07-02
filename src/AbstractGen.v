Require Import ZArith Axioms.
Require Import List ssreflect ssrbool ssrnat seq.
Import ListNotations.

Class Random (A : Type) :=
  { 
    randomR : A * A -> RandomGen -> A * RandomGen; 
    
    (* I need this to convert randomR to set of 
       outcomes, taking range into account *)
    cmp : A -> A -> comparison 
  }.


Instance Randombool : Random bool :=
  {
    randomR := randomRBool;
    cmp b1 b2 :=
      match b1, b2 with 
        | false, true => Lt
        | true, false => Gt
        | _, _ => Eq
      end
  }.

Instance Randomnat : Random nat :=
  {
    randomR := randomRNat;
    cmp := nat_compare
  }.


Instance RandomZ : Random Z :=
  {
    randomR := randomRInt;
    cmp := Z.compare
  }.

Class GenMonad M := 
  {
    bindGen : forall {A B : Type},  M A -> (A -> M B) -> M B;
    returnGen : forall {A : Type}, A -> M A;
    fmapGen : forall {A B: Type}, (A -> B) -> (M A) -> M B; 
    choose : forall {A} {H: Random A}, A * A -> M A;
    sized : forall {A}, (nat -> M A) -> M A;
    suchThatMaybe : forall {A}, M A -> (A -> bool) -> M (option A)
  }.
  
Section Utilities.
  Context {Gen : Type -> Type}
          {H : GenMonad Gen}. 
  
  Definition liftGen {A B} (f: A -> B) (a : Gen A) 
  : Gen B := nosimpl 
               (bindGen a (fun x =>
                returnGen (f x))).

  Definition liftGen2 {A1 A2 B}
             (C : A1 -> A2 -> B) (m1 : Gen A1) (m2  : Gen A2)
  : Gen B:=
    nosimpl (bindGen m1 (fun x1 => bindGen m2 (fun x2 => returnGen (C x1 x2)))).

  Definition liftGen3 {A1 A2 A3 R} (F : A1 -> A2 -> A3 -> R)
           (m1 : Gen A1) (m2 : Gen A2) (m3 : Gen A3) 

  : Gen R := nosimpl(
    bindGen m1 (fun x1 =>
    bindGen m2 (fun x2 =>
    bindGen m3 (fun x3 =>
    returnGen (F x1 x2 x3))))).

  Definition liftGen4 {A1 A2 A3 A4 R}
             (F : A1 -> A2 -> A3 -> A4 -> R)
             (m1 : Gen A1) (m2 : Gen A2) (m3 : Gen A3) (m4: Gen A4)
  : Gen R := nosimpl(
    bindGen m1 (fun x1 =>
    bindGen m2 (fun x2 =>
    bindGen m3 (fun x3 =>
    bindGen m4 (fun x4 =>
    returnGen (F x1 x2 x3 x4)))))).

  Definition liftGen5 {A1 A2 A3 A4 A5 R} 
             (F : A1 -> A2 -> A3 -> A4 -> A5 -> R)
             (m1 : Gen A1) (m2 : Gen A2) (m3 : Gen A3) (m4: Gen A4) (m5 : Gen A5)
  : Gen R := nosimpl(
    bindGen m1 (fun x1 =>
    bindGen m2 (fun x2 =>
    bindGen m3 (fun x3 =>
    bindGen m4 (fun x4 =>
    bindGen m5 (fun x5 =>
    returnGen (F x1 x2 x3 x4 x5))))))).

  Definition sequenceGen {A : Type} (ms : list (Gen A)) : Gen (list A) := nosimpl(
    fold_right (fun m m' => bindGen m  (fun x => 
                            bindGen m' (fun xs =>
                            returnGen (x :: xs)))) (returnGen []) ms).

  Fixpoint foldGen {A B : Type} (f : A -> B -> Gen A) (l : list B) (a : A) 
  : Gen A := nosimpl(
    match l with
      | [] => returnGen a
      | (x :: xs) => bindGen (f a x) (foldGen f xs)
    end).

  Definition oneof {A : Type} (def: Gen A) (gs : list (Gen A)) : Gen A := nosimpl(
    bindGen (choose (0, length gs - 1))
            (fun n => nth def gs n)).

  Fixpoint replicate {A : Type} (n : nat) (x : A) : list A := nosimpl(
    match n with
      | O    => nil
      | S n' => cons x (replicate n' x)
    end).

  Fixpoint freqRep {A : Type} (gs : list (nat * Gen A)) : list (Gen A) := nosimpl(
    match gs with
      | nil => nil
      | cons (n, g) t =>
        (nseq n g) ++ freqRep t
    end).

  Definition frequency {A : Type} (def : Gen A) (gs : list (nat * Gen A)) := nosimpl(
    oneof def (freqRep gs)).
 
  (* This is the implementation of frequency a la QuickCheck and seems more 
     memory and time efficient. Is there a reason the should stick to the 
     first one? A corner case is when all the keys are set to zero and thus 
     the range of choose is (1, 0), which, according to Haskell's interface, 
     is an undefined behavior. *)
 
    Fixpoint pick {A : Type} (def : Gen A) (n : nat) (xs : list (nat * Gen A)) 
    : nat * Gen A := nosimpl(
      match xs with 
        | nil => (0, def)
        | (k, x) :: xs =>  
          if (n < k) then (k, x) 
          else pick def (n - k) xs
      end).

  Definition frequency'  {A : Type} (def : Gen A) (gs : list (nat * Gen A)) 
  : Gen A := nosimpl(
    let tot := (sumn (map (@fst _ _) gs)) in
    bindGen (choose (0, tot-1)) (fun n =>
    @snd _ _ (pick def n gs))).

  Definition vectorOf {A : Type} (k : nat) (g : Gen A) : Gen (list A) := nosimpl(
    fold_right (fun m m' =>
                  bindGen m (fun x => 
                  bindGen m' (fun xs => returnGen (cons x xs)))
               ) (returnGen nil) (nseq k g)).

  Definition listOf {A : Type} (g : Gen A) : Gen (list A) := nosimpl
    (sized (fun n => bindGen (choose (0, n)) (fun k => vectorOf k g))).

  Definition elements {A : Type} (def : A) (l : list A) := nosimpl(
    let n := length l in
    bindGen (choose (0, n - 1)) (fun n' => 
    returnGen (List.nth n' l def))).

End Utilities.