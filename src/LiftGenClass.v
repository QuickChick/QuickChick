Require Import QuickChick.


Class liftable (A : Type) (B : Type) :=
  {
    lift_m : A -> B 
  }.

Instance lift0 {A} : liftable (G A) (G A) :=
  { 
    lift_m := id 
  }.


Instance liftN {A B R} `(liftable (G B) R) : liftable (G (A -> B)) (G A -> R):=
   { 
     lift_m f ga := 
       lift_m (liftGen2 id f ga) 
   }.

Notation liftM := (fun f g => lift_m (fmap f g)). (* Definition does not work *)

Check (liftM (fun x => x + 3) (returnGen 0) : G nat). 
Check (liftM (fun x y => x + y) (returnGen 0) (returnGen 1) : G nat).
Check (liftM (fun x y => x + y + y) (returnGen 0) (returnGen 1) (returnGen 2) : G nat).