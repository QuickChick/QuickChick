Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From QuickChick Require Import QuickChick Tactics.
Require Import String. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import List.
Import ListNotations.
Import QcDefaultNotation. Open Scope qc_scope.

Require Export ExtLib.Structures.Monads.
Import MonadNotation.
Open Scope monad_scope.

Set Bullet Behavior "Strict Subproofs".

Derive ArbitrarySizedSuchThat for (fun x => eq x y).

Definition GenSizedSuchThateq_manual {A} (y_ : A) :=
  let fix aux_arb (init_size size : nat) (y_0 : A) {struct size} : G (option A) :=
      match size with
      | 0   => backtrack [(1, returnGen (Some y_0))]
      | S _ => backtrack [(1, returnGen (Some y_0))]
      end
  in fun size => aux_arb size size y_.

Theorem GenSizedSuchThateq_proof A (n : A) `{Dec_Eq A} `{Gen A} `{Enum A}:
  GenSizedSuchThateq_manual n = @arbitrarySizeST _ (fun x => eq x n) _.
Proof. reflexivity. Qed.

Inductive Foo :=
| Foo1 : Foo 
| Foo2 : Foo -> Foo
| Foo3 : nat -> Foo -> Foo.

QuickChickWeights [(Foo1, 1); (Foo2, size); (Foo3, size)].
Derive (Arbitrary, Show) for Foo.
Derive EnumSized for Foo.

(* Use custom formatting of generated code, and prove them equal (by reflexivity) *)

(* begin show_foo *)
Fixpoint showFoo' (x : Foo) := 
  match x with 
  | Foo1 => "Foo1"
  | Foo2 f => "Foo2 " ++ smart_paren (showFoo' f)
  | Foo3 n f => "Foo3 " ++ smart_paren (show n) ++
                        " " ++ smart_paren (showFoo' f)
  end%string.
(* end show_foo *)

Lemma show_foo_equality : showFoo' = (@show Foo _).
Proof. reflexivity. Qed.

(* begin genFooSized *)
Fixpoint genFooSized (size : nat) := 
  match size with 
  | O => returnGen Foo1
  | S size' => freq [ (1, returnGen Foo1) 
                    ; (S size', f <- genFooSized size';;
                                  ret (Foo2 f))
                    ; (S size', n <- arbitrary ;;
                                f <- genFooSized size' ;;
                                ret (Foo3 n f)) 
                    ]
  end.                 
(* end genFooSized *)                                           

(* begin shrink_foo *)
Fixpoint shrink_foo x := 
  match x with
  | Foo1 => []
  | Foo2 f => ([f] ++ map (fun f' => Foo2 f') (shrink_foo f) ++ []) ++ []
  | Foo3 n f => (map (fun n' => Foo3 n' f) (shrink n) ++ []) ++
                ([f] ++ map (fun f' => Foo3 n f') (shrink_foo f) ++ []) ++ []
  end.
(* end shrink_foo *)
(* JH: Foo2 -> Foo1, Foo3 n f -> Foo2 f *)
(* Avoid exponential shrinking *)

Lemma genFooSizedNotation : genFooSized = @arbitrarySized Foo _.
Proof. reflexivity. Qed.

Lemma shrinkFoo_equality : shrink_foo = @shrink Foo _.
Proof. reflexivity. Qed.

(* Completely unrestricted case *)
(* begin good_foo *)
Inductive goodFoo : nat -> Foo -> Prop :=
| GoodFoo : forall n foo,  goodFoo n foo.
(* end good_foo *)

Derive ArbitrarySizedSuchThat for (fun foo => goodFoo n foo).
Derive EnumSizedSuchThat for (fun foo => goodFoo n foo).

(* Need to write it as 'fun x => goodFoo 0 x'. Sadly, 'goodFoo 0' doesn't work *)
Definition g : G (option Foo) := @arbitrarySizeST _ (fun x => goodFoo 0 x) _ 4.
(* Sample g. *)

(* Simple generator for goodFoos *)
(* begin gen_good_foo_simple *)
(* Definition genGoodFoo {_ : Arbitrary Foo} (n : nat) : G Foo := arbitrary.*)
(* end gen_good_foo_simple *)

(* begin gen_good_foo *)
Definition genGoodFoo `{_ : Arbitrary Foo} (n : nat)  :=
  let fix aux_arb init_size size n := 
    match size with 
    | 0   => backtrack [(1, foo <- arbitrary ;; ret (Some foo))]
    | S _ => backtrack [(1, foo <- arbitrary ;; ret (Some foo))]
    end
  in fun sz => aux_arb sz sz n.
(* end gen_good_foo *)

Lemma genGoodFoo_equality n : 
  genGoodFoo n = @arbitrarySizeST _ (fun foo => goodFoo n foo) _.
Proof. reflexivity. Qed.

(* Copy to extract just the relevant generator part *)
Definition genGoodFoo'' `{_ : Arbitrary Foo} (n : nat) :=
  let fix aux_arb init_size size n := 
    match size with 
    | 0   => backtrack [(1, 
(* begin gen_good_foo_gen *)
      foo <- arbitrary;; ret (Some foo)
(* end gen_good_foo_gen *)
                        )]
    | S _ => backtrack [(1, foo <- arbitrary;; ret (Some foo))]
    end
  in fun sz => aux_arb sz sz n.

Lemma genGoodFoo_equality' : genGoodFoo = genGoodFoo''.
Proof. reflexivity. Qed.
 
(* Basic Unification *)
(* begin good_unif *)
Inductive goodFooUnif : nat -> Foo -> Prop := 
| GoodUnif : forall n, goodFooUnif n Foo1.
(* end good_unif *)

Derive ArbitrarySizedSuchThat for (fun foo => goodFooUnif n foo).

Definition genGoodUnif (n : nat) :=
  let fix aux_arb init_size size n := 
    match size with 
    | 0   => backtrack [(1, 
(* begin good_foo_unif_gen *)
  ret (Some Foo1)
(* end good_foo_unif_gen *)
                        )] 
    | S _ => backtrack [(1, ret (Some Foo1))] 
    end
  in fun sz => aux_arb sz sz n.

Lemma genGoodUnif_equality n : 
  genGoodUnif n = @arbitrarySizeST _ (fun foo => goodFooUnif n foo) _. 
Proof. reflexivity. Qed. 

(* The foo is generated by arbitrary *)
(* begin good_foo_combo *)
Inductive goodFooCombo : nat -> Foo -> Prop :=
| GoodCombo : forall n foo, goodFooCombo n (Foo2 foo).
(* end good_foo_combo *)

Derive ArbitrarySizedSuchThat for (fun foo => goodFooCombo n foo).

Definition genGoodCombo `{_ : Arbitrary Foo} (n : nat) :=
  let fix aux_arb init_size size n := 
    match size with 
    | 0   => backtrack [(1, 
(* begin good_foo_combo_gen *)
   foo <- arbitrary;; ret (Some (Foo2 foo))
(* end good_foo_combo_gen *)
                        )] 
    | S _ => backtrack [(1, foo <- arbitrary;; ret (Some (Foo2 foo)))]
    end
  in fun sz => aux_arb sz sz n.

Lemma genGoodCombo_equality n : 
  genGoodCombo n = @arbitrarySizeST _ (fun foo => goodFooCombo n foo) _.
Proof. reflexivity. Qed. 

(* Requires input nat to match 0 *)
(* begin good_input_match *)
Inductive goodFooMatch : nat -> Foo -> Prop := 
| GoodMatch : goodFooMatch 0 Foo1.
(* end good_input_match *)

Derive ArbitrarySizedSuchThat for (fun foo => goodFooMatch n foo).

Definition genGoodMatch (n : nat) :=
  let fix aux_arb init_size size n := 
    match size with 
    | 0   => backtrack [(1, 
(* begin good_foo_match_gen *)
  match n with
  | 0 => ret (Some Foo1)
  | _.+1 => ret None
  end
(* end good_foo_match_gen *)
                        )]
    | S _ => backtrack [(1,
           match n with
           | 0 => ret (Some Foo1)
           | _.+1 => ret None
           end)]
    end
  in fun sz => aux_arb sz sz n.

Lemma genGoodMatch_equality n : 
  genGoodMatch n = @arbitrarySizeST _ (fun foo => goodFooMatch n foo) _.
Proof. reflexivity. Qed. 

(* Requires recursive call of generator *)
(* begin good_foo_rec *)
Inductive goodFooRec : nat -> Foo -> Prop :=
| GoodRecBase : forall n, goodFooRec n Foo1
| GoodRec : forall n foo, goodFooRec 0 foo -> goodFooRec n (Foo2 foo).
(* end good_foo_rec *)

Derive ArbitrarySizedSuchThat for (fun foo => goodFooRec n foo).

(* begin gen_good_rec *)
Definition genGoodRec (n : nat) :=
  let fix aux_arb (init_size size : nat) n : G (option Foo) := 
    match size with 
    | 0 => backtrack [(1, ret (Some Foo1)); (1, ret None)]
    | S size' => backtrack [ (1, ret (Some Foo1))
                           ; (1, bindOpt (aux_arb init_size size' 0) (fun foo => 
                                 ret (Some (Foo2 foo)))) ]
    end
  in fun sz => aux_arb sz sz n.
(* end gen_good_rec *)

Lemma genGoodRec_equality n :
  genGoodRec n = @arbitrarySizeST _ (fun foo => goodFooRec n foo) _. 
Proof. reflexivity. Qed. 

(* Precondition *)
Inductive goodFooPrec : nat -> Foo -> Prop :=
| GoodPrecBase : forall n, goodFooPrec n Foo1
| GoodPrec : forall n foo, goodFooPrec 0 Foo1 -> goodFooPrec n foo.

Derive DecOpt for (goodFooPrec n foo).

Definition DecOptgoodFooPrec_manual (n_ : nat) (foo_ : Foo) := 
 let fix aux_arb (init_size size0 n_0 : nat) (foo_0 : Foo) {struct size0} : option bool :=
     match size0 with
     | 0 =>
       checker_backtrack
         [(fun u:unit =>
          match foo_0 with
          | Foo1 => Some true
          | _ => Some false
          end
         ); fun u:unit => None]
     | size'.+1 =>
       checker_backtrack
         [(fun u:unit =>
          match foo_0 with
          | Foo1 => Some true
          | _ => Some false
          end)
        ;(fun u:unit =>
          match aux_arb init_size size' 0 Foo1 with
          | Some true => Some true
          | Some false => Some false
          | None => None
          end)
         ]
     end in
 fun size0 : nat => aux_arb size0 size0 n_ foo_.


Theorem DecOptgoodFooPrec_proof n foo :
  DecOptgoodFooPrec_manual n foo = @decOpt (goodFooPrec n foo) _.
Proof. reflexivity. Qed.

Derive ArbitrarySizedSuchThat for (fun foo => goodFooPrec n foo).

Definition genGoodPrec (n : nat) : nat -> G (option (Foo)):=
 let
   fix aux_arb init_size size (n : nat) : G (option (Foo)) :=
     match size with
     | O => 
         backtrack [ (1, ret (Some Foo1))
                     ; (1, match @decOpt (goodFooPrec O Foo1) _ init_size with
                           | Some true => foo <- arbitrary;;
                                          ret (Some foo)
                           | _ => ret None
                           end)
           ]

     | S size' =>
         backtrack [ (1, ret (Some Foo1))
                     ; (1, match @decOpt (goodFooPrec O Foo1) _ init_size with
                           | Some true => foo <- arbitrary;;
                                          ret (Some foo)
                           | _ => ret None
                           end
                     )]
     end in fun sz => aux_arb sz sz n.

Lemma genGoodPrec_equality n : 
  genGoodPrec n = @arbitrarySizeST _ (fun foo => goodFooPrec n foo) _.
Proof. reflexivity. Qed. 

(* Generation followed by check - backtracking necessary *)
Inductive goodFooNarrow : nat -> Foo -> Prop :=
| GoodNarrowBase : forall n, goodFooNarrow n Foo1
| GoodNarrow : forall n foo, goodFooNarrow 0 foo -> 
                        goodFooNarrow 1 foo -> 
                        goodFooNarrow n foo.

Derive DecOpt for (goodFooNarrow n foo).

Definition goodFooNarrow_decOpt (n_ : nat) (foo_ : Foo) :=
  let fix aux_arb (init_size size0 n_0 : nat) (foo_0 : Foo) : option bool :=
      match size0 with
      | 0 =>
        checker_backtrack
          [(fun _ : unit =>
             match foo_0 with
             | Foo1 => Some true
             | _ => Some false
             end)
          ; (fun _ : unit => None)]
      | size'.+1 =>
        checker_backtrack
          [(fun _ : unit =>
             match foo_0 with
             | Foo1 => Some true
             | _ => Some false
             end) ;
           (fun _ : unit =>
                 match aux_arb init_size size' 0 foo_0 with
                 | Some true =>
                   match aux_arb init_size size' 1 foo_0 with
                   | Some true => Some true
                   | Some false => Some false
                   | None => None
                   end
                 | Some false => Some false
                 | None => None
                 end)]
      end in
  fun size0 : nat => aux_arb size0 size0 n_ foo_.

Lemma goodFooNarrow_decOpt_correct n foo :
  goodFooNarrow_decOpt n foo = @decOpt (goodFooNarrow n foo) _.
Proof. reflexivity. Qed. 

Derive ArbitrarySizedSuchThat for (fun foo => goodFooNarrow n foo).

Definition genGoodNarrow (n : nat) : nat -> G (option (Foo)) :=
 let
   fix aux_arb init_size size (n : nat) : G (option (Foo)) :=
     match size with
     | O => backtrack [(1, ret (Some Foo1)); (1, ret None)]
     | S size' =>
         backtrack [ (1, ret (Some Foo1))
                   ; (1, bindOpt (aux_arb init_size size' 0) (fun foo =>
                         match @decOpt (goodFooNarrow 1 foo) _  init_size with
                         | Some true => ret (Some foo)
                         | _ => ret None
                         end
                     ))]
     end in fun sz => aux_arb sz sz n.

Lemma genGoodNarrow_equality n : 
  genGoodNarrow n = @arbitrarySizeST _ (fun foo => goodFooNarrow n foo) _. 
Proof. reflexivity. Qed. 

(* Non-linear constraint *)
Inductive goodFooNL : nat -> Foo -> Foo -> Prop :=
| GoodNL : forall n foo, goodFooNL n (Foo2 foo) foo.

Instance EqDecFoo (f1 f2 : Foo) : Dec (f1 = f2).
Proof. dec_eq. Defined.

Derive ArbitrarySizedSuchThat for (fun foo => goodFooNL n m foo).
Derive DecOpt for (goodFooNL n m foo).

(* Parameters don't work yet :)  *)

(*
Inductive Bar A B :=
| Bar1 : A -> Bar A B
| Bar2 : Bar A B -> Bar A B
| Bar3 : A -> B -> Bar A B -> Bar A B -> Bar A B.

Arguments Bar1 {A} {B} _.
Arguments Bar2 {A} {B} _.
Arguments Bar3 {A} {B} _ _ _ _.

Inductive goodBar {A B : Type} (n : nat) : Bar A B -> Prop :=
| goodBar1 : forall a, goodBar n (Bar1 a)
| goodBar2 : forall bar, goodBar 0 bar -> goodBar n (Bar2 bar)
| goodBar3 : forall a b bar,
            goodBar n bar ->
            goodBar n (Bar3 a b (Bar1 a) bar).

*)

(* Generation followed by check - backtracking necessary *)

(* Untouched variables - ex soundness bug *)
Inductive goodFooFalse : Foo -> Prop :=
| GoodFalse : forall (x : False), goodFooFalse Foo1.

Instance arbFalse : Gen False. Admitted.

Set Warnings "+quickchick-uninstantiated-variables".
Fail Derive ArbitrarySizedSuchThat for (fun foo => goodFooFalse foo).
Set Warnings "quickchick-uninstantiated-variables".

Definition addFoo2 (x : Foo) := Foo2 x.

Fixpoint foo_depth f := 
  match f with
  | Foo1 => 0
  | Foo2 f => 1 + foo_depth f
  | Foo3 n f => 1 + foo_depth f
  end.


Derive ArbitrarySizedSuchThat for (fun n => goodFooPrec n x).

Inductive goodFun : Foo -> Prop :=
| GoodFun : forall (n : nat) (a : Foo), goodFooPrec n (addFoo2 a) ->
                                        goodFun a.

Derive ArbitrarySizedSuchThat for (fun a => goodFun a).

Definition success := "success".
Print success.

