Require Import List. Import ListNotations.
Require Import Rules.
Require Import Instructions.
Require Import Machine.

Set Implicit Arguments.

Fixpoint break_expr n (e : rule_expr n) : list (rule_expr n) :=
  match e with
  | L_Bot => []
  | L_Var m => [L_Var m]
  | L_Join e1 e2 => break_expr e1 ++ break_expr e2
  end.

Fixpoint join_exprs n (es : list (rule_expr n)) : rule_expr n :=
  match es with
  | nil => L_Bot n
  | e :: nil => e
  | e :: es' => L_Join e (join_exprs es')
  end.

Fixpoint break_scond n (c : rule_scond n) : list (rule_scond n) :=
  match c with
  | A_True => []
  | A_LE e1 e2 => List.map (fun e1' => A_LE e1' e2) (break_expr e1)
  | A_And c1 c2 => break_scond c1 ++ break_scond c2
  | A_Or c1 c2 => [c]
  end.

Fixpoint and_sconds n (cs : list (rule_scond n)) : rule_scond n :=
  match cs with
  | nil => A_True n
  | c :: nil => c
  | c :: cs' => A_And c (and_sconds cs')
  end.

Fixpoint drop_each X (xs : list X) : list (list X) :=
  match xs with
  | nil => []
  | x :: xs' => xs' :: (map (fun xs'' => x :: xs'') (drop_each xs'))
  end.

Example ex_drop_each :
  drop_each [1;2;3;4] = [[2;3;4];[1;3;4];[1;2;4];[1;2;3]].
Proof. reflexivity. Qed.

Definition mutate_expr n (e : rule_expr n) : list (rule_expr n) :=
  let es := (break_expr e) in
  match es with
  | nil => []
  | _ => List.map (@join_exprs n) (drop_each es)
  end.

Definition eL1 : rule_expr 3 := Lab1.
Definition eL2 : rule_expr 3 := Lab2.
Definition eL3 : rule_expr 3 := Lab3.
Definition ePC : rule_expr 3 := LabPC.

Example ex_break_expr :
  break_expr (L_Join (L_Join eL1 eL2) eL3) = [eL1; eL2; eL3].
Proof. reflexivity. Qed.

Example ex_drop_each' :
  drop_each [eL1; eL2; eL3] = [[eL2;eL3]; [eL1;eL3]; [eL1;eL2]].
Proof. reflexivity. Qed.

Example ex_join_exprs :
  join_exprs [eL1; eL2; eL3] = L_Join eL1 (L_Join eL2 eL3).
Proof. reflexivity. Qed.

Example ex_mutate_expr :
  mutate_expr (L_Join (L_Join eL1 eL2) eL3) =
    [L_Join eL2 eL3; L_Join eL1 eL3; L_Join eL1 eL2].
Proof. reflexivity. Qed.

Example ex_mutate_expr_var : mutate_expr eL1 = [L_Bot 3].
Proof. reflexivity. Qed.

Example ex_mutate_expr_bot : mutate_expr (L_Bot 3) = [].
Proof. compute. reflexivity. Qed.

(* For the pc we move disjuncts to the result label;
   to prevent useless mutants we never move the pc label,
   but we do try to remove it if there is no result label *)
Fixpoint drop_each_but_not_lpc n (es : list (rule_expr n)) :
    list (rule_expr n * list (rule_expr n)) :=
  let f x xs'' := (fst xs'', x :: snd xs'') in
  match es with
  | nil => []
  | (L_Var labpc) :: xs' =>
      map (f (L_Var (@labpc n))) (drop_each_but_not_lpc xs')
  | x :: xs' =>
      (x, xs') :: (map (f x) (drop_each_but_not_lpc xs'))
  end.

Example ex_drop_each_but_not_lpc_1 :
  drop_each_but_not_lpc [eL1; ePC] = [(Lab1, [LabPC])].
Proof. reflexivity. Qed.

Example ex_drop_each_but_not_lpc_1' :
  drop_each_but_not_lpc [ePC; eL1] = [(Lab1, [LabPC])].
Proof. reflexivity. Qed.

Example ex_drop_each_but_not_lpc_2 :
  drop_each_but_not_lpc [eL1; eL2; ePC] =
    [(Lab1, [Lab2; LabPC]); (Lab2, [Lab1; LabPC])].
Proof. reflexivity. Qed.

Example ex_drop_each_but_not_lpc_2' :
  drop_each_but_not_lpc [eL1; ePC; eL2] =
    [(Lab1, [LabPC; Lab2]); (Lab2, [Lab1; LabPC])].
Proof. reflexivity. Qed.

Example ex_drop_each_but_not_lpc_2'' :
  drop_each_but_not_lpc [ePC; eL1; eL2] =
    [(Lab1, [LabPC; Lab2]); (Lab2, [LabPC; Lab1])].
Proof. reflexivity. Qed.

Definition mutate_pc n (ores : option (rule_expr n)) (epc : rule_expr n)
    : list (option (rule_expr n) * (rule_expr n)) :=
  let es := (break_expr epc) in
  match es with
  | nil => []
  | _ =>
      match ores with
      | Some eres =>
          let f xxs := (Some (L_Join eres (fst xxs)), join_exprs (snd xxs)) in
          List.map f (drop_each_but_not_lpc es)
      | None =>
          (* we just drop each pc disjunct as before *)
          let f xs := (None, join_exprs xs) in
          List.map f (drop_each es)
      end
  end.

Example ex_mutate_pc_1 :
  mutate_pc (Some eL2) (L_Join eL1 ePC) = [(Some (JOIN Lab2 Lab1), LabPC)].
Proof. reflexivity. Qed.

Example ex_mutate_pc_1' :
  mutate_pc (Some eL2) (L_Join ePC eL1) = [(Some (JOIN Lab2 Lab1), LabPC)].
Proof. reflexivity. Qed.

Example ex_mutate_pc_2 :
  mutate_pc (Some eL3) (L_Join (L_Join ePC eL1) eL2) =
    [(Some (JOIN Lab3 Lab1), JOIN LabPC Lab2);
     (Some (JOIN Lab3 Lab2), JOIN LabPC Lab1)].
Proof. reflexivity. Qed.

Definition mutate_scond n (c : rule_scond n) : list (rule_scond n) :=
  let cs := (break_scond c) in
  match cs with
  | nil => []
  | _ => List.map (@and_sconds n) (drop_each cs)
  end.

Definition c123 := A_LE (L_Join eL1 eL2) eL3.
Definition c321 := A_LE eL3 (L_Join eL1 eL2).
Definition c13 := A_LE eL1 eL3.
Definition c23 := A_LE eL2 eL3.

Example ex_break_scond :
  break_scond (A_And c123 c321) = [c13; c23; c321].
Proof. reflexivity. Qed.

Example ex_and_sconds :
  and_sconds [c13; c23; c321] = A_And c13 (A_And c23 c321).
Proof. reflexivity. Qed.

Example ex_mutate_scond :
  mutate_scond (A_And c123 c321) = [A_And c23 c321;
                                    A_And c13 c321;
                                    A_And c13 c23].
Proof. reflexivity. Qed.

Example ex_mutate_scond_true : mutate_scond (A_True 3) = [].
Proof. reflexivity. Qed.

Definition mutate_rule n (r : AllowModify n) : list (AllowModify n) :=
  let a := allow r in
  let res := labRes r in
  let pc := labResPC r in
  (List.map (fun a' => almod a' res pc) (mutate_scond a)) ++
  (match res with
   | Some lres =>
      List.map (fun lres' => almod a (Some lres') pc) (mutate_expr lres)
   | None => []
   end) ++
  (List.map (fun respc => almod a (fst respc) (snd respc)) (mutate_pc res pc)).

(* Printing
Eval cbv in (mutate_rule
  (≪ AND (LE Lab2 LabPC) (LE (JOIN LabPC (JOIN Lab1 Lab2)) Lab3),
     JOIN Lab1 Lab2, LabPC ≫)).
*)

(* This displays bad
Definition mutate_table (t : table) : list table :=
  fold_left (@List.app table)
    (List.map (fun (o : OpCode) =>
      (List.map (fun (mr : AllowModify (labelCount o)) (o' : OpCode) =>
        match opCode_eq_dec o o' with
        | left H => eq_rec_r _ (fun x => x) H mr
        | right _ => t o'
        end
      ) (mutate_rule (t o)))
    ) opCodes) [].
*)

(* Breaking this out gives more control on the evaluation *)
Definition helper o (mr : AllowModify (labelCount o)) o'
  (orig : AllowModify (labelCount o')) : AllowModify (labelCount o') :=
  match opCode_eq_dec o o' with
  | left H => eq_rec_r _ (fun x => x) H mr
  | right _ => orig
  end.

(* The dummy argument t' will be the same as t,
    just that I wanted more control on evaluation *)
Definition mutate_table' (t t' : table) : list table :=
  fold_left (@List.app table)
    (List.map (fun (o : OpCode) =>
      (List.map (fun (mr : AllowModify (labelCount o)) (o' : OpCode)
        => helper o mr o' (t' o')
      ) (mutate_rule (t o)))
    ) opCodes) [].
Definition mutate_table t := mutate_table' t t.

(* Printing
Definition copy_table := default_table.
Eval lazy -[labelCount helper copy_table] in
  (mutate_table' default_table copy_table).

Eval simpl in nth 21 (mutate_table default_table).
(* can achieve the same with partial application *)
Eval lazy -[labelCount helper] in
  (mutate_table' default_table).

Eval lazy in (List.length (mutate_table default_table)).
*)