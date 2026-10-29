From QuickChick Require Import QuickChick.

(* Automatic theorem testing must use an existing unsized Gen instance.
   This generator never produces T1, so testing the false theorem passes
   only when the derived test reuses it. *)
Inductive token := T0 | T1.

#[local] Instance show_token : Show token :=
  {| show t := match t with T0 => "T0" | T1 => "T1" end |}%string.
#[local] Instance gen_token : Gen token := {| arbitrary := ret T0 |}.
#[local] Instance dec_token (a b : token) : Dec (a = b).
Proof. dec_eq. Defined.

Theorem only_t0 : forall x : token, x = T0.
Proof.
  quickchick.
  lazymatch (eval unfold theorem in theorem) with
  | context [gen_token] => idtac
  | _ => fail "theorem testing did not reuse gen_token"
  end.
Admitted.

(* A sized instance takes priority over an unsized one. *)
Module PreferSized.
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
End PreferSized.
