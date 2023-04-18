Require Import List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia Arith.

Require Import QuickChick.Show.

(* Proof that Show for string round-trips. *)

Lemma not_digit_when (c : ascii) (x : nat) :
  (nat_of_ascii c < 48) \/ (57 < nat_of_ascii c) ->
  unit_digit x <> c.
Proof.
  assert (mod_fact : x mod 10 < 10).
  { apply Nat.mod_upper_bound; auto. }
  intros H e.
  unfold unit_digit in e.
  apply (f_equal nat_of_ascii) in e.
  rewrite nat_ascii_embedding in e.
  all: lia.
Qed.

Lemma unit_digit_ascii :
  forall n, digit_of_ascii (unit_digit n) = Some (n mod 10).
Proof.
  intro.
  assert (mod_fact : n mod 10 < 10).
  { apply Nat.mod_upper_bound; auto. }
  unfold unit_digit.
  unfold digit_of_ascii.
  rewrite nat_ascii_embedding.
  replace (48 <=? n mod 10 + 48) with true.
  replace (n mod 10 + 48 <=? 57) with true.
  rewrite Nat.add_sub.
  auto.
  { symmetry. apply leb_correct. lia. }
  { symmetry. apply leb_correct. lia. }
  { lia. }
Qed.

Lemma decimal_thousand : forall n,
    n < 256 ->
    (n / 100) mod 10 * 100 + (n / 10) mod 10 * 10 + n mod 10 = n.
Proof.
  intros.
  rewrite Nat.div_mod with (y:=10); auto.
  rewrite Nat.add_cancel_r.
  replace 100 with (10*10) by auto.
  rewrite Nat.mul_assoc.
  rewrite <- Nat.mul_add_distr_r.
  rewrite Nat.mul_comm.
  rewrite Nat.mul_cancel_l; auto.
  rewrite <- Nat.div_div; auto.
  rewrite (Nat.div_mod (n/10) 10) at 3; auto.
  rewrite Nat.add_cancel_r.
  rewrite Nat.mul_comm.
  rewrite Nat.mul_cancel_l; auto.
  rewrite Nat.mod_small; auto.
  rewrite Nat.div_div; auto.
  simpl.
  rewrite (Nat.div_lt_upper_bound n 100 9); auto.
  lia.
Qed.

Lemma unthree_three_digit (c : ascii) :
  let n := nat_of_ascii c in
  unthree_digit
    (unit_digit (n / 100)) (unit_digit (n / 10)) (unit_digit n)
  = Some (ascii_of_nat n).
Proof.
  unfold unthree_digit.
  do 3 rewrite unit_digit_ascii.
  rewrite decimal_thousand.
  auto.
  apply nat_ascii_bounded.
Qed.

Lemma read_show_quoted_string : forall (s : string),
    read_quoted_string (show_quoted_string s) = Some s.
Proof.
  induction s.
  - auto.
  - unfold show_quoted_string.
    destruct (ascii_dec a "009") as [is_tab | isn_tab].
    { fold show_quoted_string.
      simpl.
      rewrite IHs.
      rewrite is_tab; auto.
    }
    destruct (ascii_dec a "010") as [is_nl | isn_nl].
    { fold show_quoted_string.
      simpl; rewrite IHs.
      rewrite is_nl; auto.
    }
    destruct (ascii_dec a "013") as [is_cr | isn_cr].
    { fold show_quoted_string.
      simpl; rewrite IHs.
      rewrite is_cr; auto.
    }
    destruct (ascii_dec a """") as [is_dq | isn_dq].
    { fold show_quoted_string.
      simpl; rewrite IHs.
      rewrite is_dq; auto.
    }
    destruct (ascii_dec a "\") as [is_bs | isn_bs].
    { fold show_quoted_string.
      simpl; rewrite IHs.
      rewrite is_bs; auto.
    }
    destruct ((nat_of_ascii a <? 32) || (126 <? nat_of_ascii a))%bool.
    { fold show_quoted_string.
      simpl.
      destruct (ascii_dec _ "n") as [is_n2 | isn_n2].
      { apply not_digit_when in is_n2. contradict is_n2.
        compute. right. lia.
      }
      destruct (ascii_dec _ "r") as [is_r2 | isn_r2].
      { apply not_digit_when in is_r2. contradict is_r2.
        compute. right. lia.
      }
      destruct (ascii_dec _ "t") as [is_t2 | isn_t2].
      { apply not_digit_when in is_t2. contradict is_t2.
        compute. right. lia.
      }
      destruct (ascii_dec _ "\") as [is_bs2 | isn_bs2].
      { apply not_digit_when in is_bs2. contradict is_bs2.
        compute. right; lia.
      }
      destruct (ascii_dec _ """") as [is_dq2 | isn_dq2].
      { apply not_digit_when in is_dq2. contradict is_dq2.
        compute. left; lia.
      }
      fold (Nat.div (nat_of_ascii a) 100).
      fold (Nat.div (nat_of_ascii a) 10).
      rewrite unthree_three_digit.
      rewrite IHs.
      rewrite ascii_nat_embedding.
      auto.
    }
    { fold show_quoted_string.
      simpl.
      destruct (ascii_dec a """"); [contradiction |].
      destruct (ascii_dec a "\"); [contradiction |].
      rewrite IHs.
      auto.
    }
Qed.
                             
Lemma read_show_string : forall (s : string),
    read_string (show s) = Some s.
Proof.
  intro.
  simpl.
  apply read_show_quoted_string.
Qed.
