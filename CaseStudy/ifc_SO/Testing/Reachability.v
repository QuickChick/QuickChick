Require Import Machine.

Require Import Common.

Require Import List.
Require Import ZArith.

Definition is_low_pointer (obs : Label) (st : State) (a : Atom) : bool :=
  match a with
    | Vptr p @ L => isLow L obs
    | _ => false
  end.

Definition extract_mframe (a : Atom) : option mframe :=
  match a with
    | Vptr (Ptr fp _) @ _ => Some fp
    | _ => None
  end.

Definition elem {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (x : A) (l : list A) : bool :=
  existsb (fun y => if eq_dec x y then true else false) l.

(* This unions to sets while removing duplicates *)
Fixpoint nub_by_aux {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y})
         (l acc : list A) : list A :=
  match l with
    | [] => acc
    | h::t => 
      if elem eq_dec h acc 
      then nub_by_aux eq_dec t acc
      else nub_by_aux eq_dec t (h::acc)
  end.

(* This removes duplicates from a list *)
Definition nub_by {A : Type} eq_dec (l : list A) := nub_by_aux eq_dec l [].

Definition get_mframes_from_atoms (obs : Label) (st : State) (atoms : list Atom) 
  : list mframe :=
  nub_by Mem.EqDec_block 
        (list_of_option (map extract_mframe
                        (filter (is_low_pointer obs st) atoms))).

Fixpoint get_root_set_stack (obs : Label) (st : State) 
         (acc : list mframe) (s : Stack) : list mframe :=
  match s with
    | Mty => acc
    | RetCons (pc, _, rs, _) s' =>
      let new_mframes := 
          if isLow ∂pc obs then get_mframes_from_atoms obs st rs
          else [] in
      let acc' := nub_by_aux Mem.EqDec_block new_mframes acc in
      get_root_set_stack obs st acc' s'
  end.

Definition get_root_set (obs : Label) (st : State) : list mframe :=
  let '(St _ _ _ s r pc) := st in
  let init_root_set := 
      if isLow ∂pc obs then get_mframes_from_atoms obs st r
      else [] in
  get_root_set_stack obs st init_root_set s.

Function reachable_from_root_set (obs : Label) (st : State)
         (visited worklist : list mframe)
  {measure (fun w => 0) worklist} (* TODO: prove termination?
     CH: Yes, but this measure is completely bogus; a good measure would be the
         length (all frames / (visited / workist)), or something like that *)
  : list mframe :=
  match worklist with
    | [] => visited
    | h::t => 
      if elem Mem.EqDec_block h visited then
        reachable_from_root_set obs st visited t
      else 
        match Mem.get_frame (st_mem st) h with
          | Some (Fr _ L atoms) =>
            let newCands := 
                if isLow L obs then 
                  get_mframes_from_atoms obs st atoms 
                else [] in
            let worklist' := nub_by_aux Mem.EqDec_block newCands t in
            reachable_from_root_set obs st (h :: visited) worklist'
          | _ => reachable_from_root_set obs st (h :: visited) t
        end
  end.
Proof. 
admit. admit. admit. 
Defined.

Definition reachable (obs : Label) (st : State) : list mframe :=
  let root_set := get_root_set obs st in
  reachable_from_root_set obs st [] root_set.

Definition well_formed_label (st : State) (l : Label) : bool :=
  let observable := reachable l st in 
  forallb (fun mf => let s := Mem.stamp mf in isLow s l) observable.

(* Given a state and a stamp configuration, make sure everything is ok *)
(* LL: This also suggests a way of generating stamps! Namely, get 
   the meet of all the labels where a frame is reachable *)
Definition well_formed (st : State) : bool :=
  let '(St _ _ prins _ _ _) := st in
  let all_labels := map lab_of_list (powerset (Zset.elements prins)) in
  forallb (well_formed_label st) all_labels.

(* Computes the meet of a list of labels. Must be provided with top as the
   initial accumulator *)
Definition list_meet (acc : Label) (ls : list Label) :=
  fold_left meet ls acc.

(* Attempt to reverse the above predicate to get a stamp generator *)
(* CH: currently unused *)
Definition generate_stamp (st : State) (mf : mframe) : mframe :=
  let '(St _ m p _ _ _) := st in 
  let all_labels := map lab_of_list (powerset (Zset.elements p)) in
  let cands := filter (fun l => elem Mem.EqDec_block mf (reachable l st))
                      all_labels in
  Mem.put_stamp (list_meet p cands) mf.


(* LL: TODO: go through the whole thing and generate stamps! *)
(*
Definition generateStamps (st : State) : StampMap :=
  let '(St m p _ _ _) := st in
  fold_left (fun sm mf => updateStampMap sm mf (generateStamp st mf))
            (allocated m) emptyStampMap.
*)
