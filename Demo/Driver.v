Require Import QuickChick.

Require Import Machine.
Require Import Printing.
Require Import Generation.
Require Import Indist.

Require Import String.
Local Open Scope string.
Definition SSNI (t : table) (v : @Variation State) : Property :=
  let '(V st1 st2) := v in
  let '(St _ _ _ (_@l1)) := st1 in
  let '(St _ _ _ (_@l2)) := st2 in
  if indist st1 st2 then 
    match l1, l2 with
      | L,L  => 
        match exec t st1, exec t st2 with
          | Some st1', Some st2' => property (indist st1' st2')
          | _, _ => collect "L,L,FAIL" true (* property rejected *)
        end
      | H, H => 
        match exec t st1, exec t st2 with
          | Some st1', Some st2' =>
            if is_atom_low (st_pc st1') && is_atom_low (st_pc st2') then
              whenFail ("Initial states: " ++ nl ++ show_pair st1 st2 ++ nl 
                        ++ "Final states: " ++ nl ++ show_pair st1' st2' ++nl)
                       (indist st1' st2') 
            else if is_atom_low (st_pc st1') then
              property (indist st2 st2') 
            else 
              property (indist st1 st1')
          | _, _ => property rejected
        end
      | H,_ => 
        match exec t st1 with
          | Some st1' => property (indist st1 st1')
          | _ => collect "H,_,FAIL" true (* property rejected*)
        end
      | _,H => 
        match exec t st2 with
          | Some st2' => property (indist st2 st2')
          | _ => collect "L,H,FAIL" true (* property rejected *)
        end
    end
  else collect "Not indist!" true (* property rejected *) .

Definition prop_SSNI := 
  forAllShrink show gen_variation_state (fun _ => nil) (SSNI default_table).

Definition prop_gen_indist := 
  forAllShrink show gen_variation_state (fun _ => nil) 
               (fun v => let '(V st1 st2) := v in indist st1 st2).

Definition main := 
  showResult (quickCheck prop_SSNI).

QuickCheck main.


  
  
  
