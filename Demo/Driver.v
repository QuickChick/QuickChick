Require Import QuickChick.

Require Import Machine.
Require Import Printing.
Require Import Generation.
Require Import Indist.

Definition SSNI (t : table) (v : @Variation State) : Property :=
  let '(V st1 st2) := v in
  let '(St _ _ _ (_@l1)) := st1 in
  let '(St _ _ _ (_@l2)) := st2 in
  if indist st1 st2 then 
    match l1, l2 with
      | L,L  => 
        match exec t st1, exec t st2 with
          | Some st1', Some st2' => property (indist st1' st2')
          | _, _ => property rejected 
        end
      | H,_ => 
        match exec t st1 with
          | Some st1' => property (indist st1 st1')
          | _ => property rejected
        end
      | _,H => 
        match exec t st2 with
          | Some st2' => property (indist st2 st2')
          | _ => property rejected
        end
    end
  else property rejected.

Definition prop_SSNI := 
  forAllShrink show gen_variation_state (fun _ => nil) (SSNI default_table).

Definition main := 
  showResult (quickCheck prop_SSNI).

QuickCheck main.


  
  
  
