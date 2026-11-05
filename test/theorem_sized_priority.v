From QuickChick Require Import QuickChick.

(* Automatic theorem testing prefers a sized generator over an unsized one.
   The sized instance only produces T1, so the theorem passes only when the
   derived test uses it. Kept apart from theorem_existing_gen.v: a Module
   there would make Coq 8.16 extract the test inside it, which cannot refer
   to constructors defined outside. *)
Inductive token := T0 | T1.

#[local] Instance show_token : Show token :=
  {| show t := match t with T0 => "T0" | T1 => "T1" end |}%string.
#[local] Instance gen_token : Gen token := {| arbitrary := ret T0 |}.
#[local] Instance dec_token (a b : token) : Dec (a = b).
Proof. dec_eq. Defined.

#[local] Instance sized_token : GenSized token :=
  {| arbitrarySized _ := ret T1 |}.

Theorem only_t1 : forall x : token, x = T1.
Proof.
  quickchick.
  lazymatch (eval unfold theorem in theorem) with
  | context [sized_token] => idtac
  | _ => fail "theorem testing did not prefer sized_token"
  end.
Admitted.
