Set Warnings "-notation-overridden,-parsing".
Set Warnings "-extraction-opaque-accessed,-extraction".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.

From QuickChick Require Import QuickChick Tactics.
Import QcDefaultNotation. Open Scope qc_scope.

(* /IMPORTS *)

(* Maps as functions are bad, explicit maps instead *)

(* TODO: Put these back in QC? *)

Inductive id : Type :=
  | Id : string -> id.

Derive (Arbitrary, Show) for id.

Instance eq_dec_id (x y : id) : Dec (x = y).
constructor. unfold ssrbool.decidable. repeat decide equality. Defined.

Definition beq_id x y :=
  match x,y with
    | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Theorem beq_id_refl : forall id, true = beq_id id id.
Admitted. (* QuickChick beq_id_refl. *) 

Theorem beq_id_true_iff : forall x y : id,
  beq_id x y = true <-> x = y.
Admitted. (* Prop *)

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false
  <-> x <> y.
Admitted. (* Prop *)

Theorem false_beq_id : forall x y : id,
   x <> y
   -> beq_id x y = false.
Admitted. (* QuickChick false_beq_id. *)

Definition partial_map := list (id * value).

Definition empty : partial_map := nil.

Definition update := @cons (id * value).

Inductive bind : partial_map -> id -> value -> Prop :=
  | BindNow   : forall x a m, bind (cons (x, a) m) x a
  | BindLater : forall x x' a a' m',
                  ~ (x = x') ->
                  bind m' x a -> 
                  bind (cons (x',a') m') x a.

(* DELETE -- write by hand *)
Derive ArbitrarySizedSuchThat for (fun x => bind m x a).

(* NOT NEEDED
Instance adm_st m a : SuchThatCorrect (fun x => bind m x a) (genST (fun x => bind m x a)).
Admitted.
*)

(* MOVE TO QC *)
Instance checkFalse : Checkable False := {| checker := fun _ => checker false |}.

Instance bind_dec m x v : Dec (bind m x v) :=
  {| dec := _ |}.
(* remove ssr...
Proof.
  move: x v.
  induction m => x v.
  - right => contra. inversion contra.
  - destruct a as [x' v'].
    destruct (eq_dec_id x x') as [[Eq | Neq]].
    + destruct (Dec_eq_nat v v') as [[EqV | NeqV]].
      * subst; left ; constructor; eauto.
      * subst; right => Contra.
        inversion Contra; subst; eauto.
    + subst; specialize (IHm x v).
      destruct IHm as [L | R].
      * left; constructor; eauto.
      * right => Contra; inversion Contra; subst; eauto.
Defined.
*) Admitted.

(* TODO: Correct equivalence of maps *)
Definition equiv_map m1 m2 :=
  forall x v , bind m1 x v <-> bind m2 x v.

Conjecture apply_empty : forall x a, ~ (bind empty x a).
(* QuickChick apply_empty. *)
(* Gave Up! - QuickChick apply_empty_unfolded. *)

Conjecture update_eq : forall (m: partial_map) x v,
    bind (update (x,v) m) x v.
(* QuickChick update_eq. *)

(* TODO: Change it to equivalence === -- use Equivalence
   typeclass?  (These are sadly false at the moment) *)

Theorem update_neq : forall v x1 x2
                       (m : partial_map),
  x2 <> x1 ->
    forall v' v'', bind (cons (x2, v) m) x1 v' ->
                   bind m x1 v'' ->
                   v' = v''.
Admitted. (* Leo: TODO QuickChick update_neq. *)

Lemma update_shadow : forall (m: partial_map) v1 v2 x,
  update (x, v2) (update (x, v1) m)  = update (x, v2) m.
Admitted. (* QuickChick update_shadow. *)

Theorem update_same : forall v x (m : partial_map),
  bind m x v ->
  update (x, v) m = m.
Admitted. (* QuickChick update_same. *)

Theorem update_permute : forall v1 v2 x1 x2
                                (m : partial_map),
  x2 <> x1 ->
    (update (x1,v1) (update (x2,v2) m))
  = (update (x2,v2) (update (x1,v1) m)).
Admitted. (* QuickChick update_permute. *)

Inductive value := VNat : nat -> value | VBool : bool -> value.

(* ################################################################# *)
(** * Arithmetic and Boolean Expressions *)

(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)

(* ================================================================= *)
(** ** Syntax *)

Module AExp.

(** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

Inductive exp : Type :=
  | Var : id -> exp
  | ANum : nat -> exp
  | APlus : exp -> exp -> exp
  | AMinus : exp -> exp -> exp
  | AMult : exp -> exp -> exp
  | BTrue : exp
  | BFalse : exp
  | BEq : exp -> exp -> exp
  | BLe : exp -> exp -> exp
  | BNot : exp -> exp
  | BAnd : exp -> exp -> exp.

Definition state := partial_map nat.

Definition empty_state : state :=
  t_empty 0.

(* ================================================================= *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)

Inductive exp : Type :=
  | ANum : nat -> exp
  | AId : id -> exp                (* <----- NEW *)
  | APlus : exp -> exp -> exp
  | AMinus : exp -> exp -> exp
  | AMult : exp -> exp -> exp.

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".

(** (This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in the chapters
    devoped to Imp, this overloading should not cause confusion.) *)

(** The definition of [exp]s is unchanged (except for using the new
    [exp]s): *)

Inductive exp : Type :=
  | BTrue : exp
  | BFalse : exp
  | BEq : exp -> exp -> exp
  | BLe : exp -> exp -> exp
  | BNot : exp -> exp
  | BAnd : exp -> exp -> exp.

(* ================================================================= *)
(** ** Evaluation *)

(** The arith and boolean evaluators are extended to handle
    variables in the obvious way, taking a state as an extra
    argument: *)

Fixpoint aeval (st : state) (a : exp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : exp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Example exp1 :
  aeval (t_update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example exp1 :
  beval (t_update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (sometimes called _statements_). *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.  (We choose this slightly awkward concrete syntax for the
    sake of being able to define Imp syntax using Coq's Notation
    mechanism.  In particular, we use [IFB] to avoid conflicting with
    the [if] notation from the standard library.)

     c ::= SKIP | x ::= a | c ;; c | IFB b THEN c ELSE c FI
         | WHILE b DO c END
*)
(**
    For example, here's factorial in Imp:

     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END

   When this command terminates, the variable [Y] will contain the
   factorial of the initial value of [X]. *)

(** Here is the formal definition of the abstract syntax of
    commands: *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> exp -> com
  | CSeq : com -> com -> com
  | CIf : exp -> com -> com -> com
  | CWhile : exp -> com -> com.

(** As usual, we can use a few [Notation] declarations to make things
    more readable.  To avoid conflicts with Coq's built-in notations,
    we keep this light -- in particular, we don't introduce any
    notations for [exps] and [exps] to avoid confusion with the
    numeric and boolean operators we've already defined. *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** For example, here is the factorial function again, written as a
    formal definition to Coq: *)

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

(* ================================================================= *)
(** ** More Examples *)

(** Assignment: *)

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

(* ----------------------------------------------------------------- *)
(** *** Loops *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

(* ----------------------------------------------------------------- *)
(** *** An infinite loop: *)

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

(* ################################################################# *)
(** * Evaluating Commands *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [WHILE] loops don't necessarily terminate makes defining
    an evaluation function tricky... *)

(* ================================================================= *)
(** ** Evaluation as a Function (Failed Attempt) *)

(** Here's an attempt at defining an evaluation function for commands,
    omitting the [WHILE] case. *)

Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        t_update st x (aeval st a1)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* bogus *)
  end.

(** In a traditional functional programming language like OCaml or
    Haskell we could add the [WHILE] case as follows:

  Fixpoint ceval_fun (st : state) (c : com) : state :=
    match c with
      ...
      | WHILE b DO c END =>
          if (beval st b)
            then ceval_fun st (c; WHILE b DO c END)
            else st
    end.

    Coq doesn't accept such a definition ("Error: Cannot guess
    decreasing argument of fix") because the function we want to
    define is not guaranteed to terminate. Indeed, it _doesn't_ always
    terminate: for example, the full version of the [ceval_fun]
    function applied to the [loop] program above would never
    terminate. Since Coq is not just a functional programming
    language but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is
    an (invalid!) program showing what would go wrong if Coq
    allowed non-terminating recursive functions:

         Fixpoint loop_false (n : nat) : False := loop_false n.

    That is, propositions like [False] would become provable
    ([loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs,
    of [ceval_fun] cannot be written in Coq -- at least not without
    additional tricks and workarounds (see chapter [ImpCEvalFun]
    if you're curious about what those might be). *)

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., define it in [Prop] instead of [Type], as we
    did for [aevalR] above. *)

(** This is an important change.  Besides freeing us from awkward
    workarounds, it gives us a lot more flexibility in the definition.
    For example, if we add nondeterministic features like [any] to the
    language, we want the definition of evaluation to be
    nondeterministic -- i.e., not only will it not be total, it will
    not even be a function! *)

(** We'll use the notation [c / st \\ st'] for the [ceval] relation:
    [c / st \\ st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           ----------------                            (E_Skip)
                           SKIP / st \\ st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   x := a1 / st \\ (t_update st x n)

                           c1 / st \\ st'
                          c2 / st' \\ st''
                         -------------------                            (E_Seq)
                         c1;;c2 / st \\ st''

                          beval st b1 = true
                           c1 / st \\ st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st \\ st'

                         beval st b1 = false
                           c2 / st \\ st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st \\ st'

                         beval st b = false
                    ------------------------------               (E_WhileFalse)
                    WHILE b DO c END / st \\ st

                          beval st b = true
                           c / st \\ st'
                  WHILE b DO c END / st' \\ st''
                  ---------------------------------               (E_WhileTrue)
                    WHILE b DO c END / st \\ st''
*)

(** Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules. *)

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   \\ (t_update (t_update empty_state X 2) Z 4).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (t_update empty_state X 2).
  - (* assignment command *)
    apply E_Ass. reflexivity.
  - (* if command *)
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.  Qed.

(** **** Exercise: 2 stars (ceval_example2)  *)
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state \\
    (t_update (t_update (t_update empty_state X 0) Y 1) Z 2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (pup_to_n)  *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for [X] = [2]
   (this is trickier than you might expect). *)

Definition pup_to_n : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem pup_to_2_ceval :
  pup_to_n / (t_update empty_state X 2) \\
    t_update (t_update (t_update (t_update (t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Determinism of Evaluation *)

(** Changing from a computational to a relational definition of
    evaluation is a good move because it frees us from the artificial
    requirement that evaluation should be a total function.  But it
    also raises a question: Is the second definition of evaluation
    really a partial function?  Or is it possible that, beginning from
    the same state [st], we could evaluate some command [c] in
    different ways to reach two different output states [st'] and
    [st'']?

    In fact, this cannot happen: [ceval] _is_ a partial function: *)

Theorem ceval_deterministic: forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
           intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b1 evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b1 evaluates to false (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b1 evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H2. inversion H2.
  - (* E_WhileTrue, b1 evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* E_WhileTrue, b1 evaluates to true *)
      assert (st' = st'0) as EQ1.
      { (* Proof of assertion *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * Reasoning About Imp Programs *)

(** We'll get deeper into systematic techniques for reasoning about
    Imp programs in the following chapters, but we can do quite a bit
    just working with the bare definitions.  This section explores
    some examples. *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st \\ st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.

  (** Inverting [Heval] essentially forces Coq to expand one step of
      the [ceval] computation -- in this case revealing that [st']
      must be [st] extended with the new value of [X], since [plus2]
      is an assignment *)

  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.

(** **** Exercise: 3 stars, recommendedM (XtimesYinZ_spec)  *)
(** State and prove a specification of [XtimesYinZ]. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, recommended (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(loop / st \\ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef
           eqn:Heqloopdef.

  (** Proceed by induction on the assumed derivation showing that
      [loopdef] terminates.  Most of the cases are immediately
      contradictory (and so can be solved in one step with
      [inversion]). *)

  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (no_whilesR)  *)
(** Consider the following function: *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  =>
      false
  end.

(** This predicate yields [true] just on programs that have no while
    loops.  Using [Inductive], write a property [no_whilesR] such that
    [no_whilesR c] is provable exactly when [c] is a program with no
    while loops.  Then prove its equivalence with [no_whiles]. *)

Inductive no_whilesR: com -> Prop :=
 (* FILL IN HERE *)
.

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 starsM (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)
(** Use either [no_whiles] or [no_whilesR], as you prefer. *)

(* FILL IN HERE *)
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (stack_compiler)  *)
(** HP Calculators, programming languages like Forth and Postscript
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a stack. For instance, the expression

      (2*3)+(3*(4-2))

   would be entered as

      2 3 * 3 4 2 - * +

   and evaluated like this (where we show the program being evaluated
   on the right and the contents of the stack on the left):

      [ ]           |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

  The task of this exercise is to write a small compiler that
  translates [exp]s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad x]: Load the identifier [x] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract.
     - [SMult]:   Similar, but multiply. *)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(** Write a function to evaluate programs in the stack language. It
    should take as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and it should return the
    stack after executing the program.  Test your function on the
    examples below.

    Note that the specification leaves unspecified what to do when
    encountering an [SPlus], [SMinus], or [SMult] instruction if the
    stack contains less than two elements.  In a sense, it is
    immaterial what we do, since our compiler will never emit such a
    malformed program. *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example s_execute1 :
     s_execute empty_state []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
(* FILL IN HERE *) Admitted.

Example s_execute2 :
     s_execute (t_update empty_state X 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
(* FILL IN HERE *) Admitted.

(** Next, write a function that compiles an [exp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : exp) : list sinstr
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced (stack_compiler_correct)  *)
(** Now we'll prove the correctness of the compiler implemented in the
    previous exercise.  Remember that the specification left
    unspecified what to do when encountering an [SPlus], [SMinus], or
    [SMult] instruction if the stack contains less than two
    elements.  (In order to make your correctness proof easier you
    might find it helpful to go back and change your implementation!)

    Prove the following theorem.  You will need to start by stating a
    more general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)


Theorem s_compile_correct : forall (st : state) (e : exp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (short_circuit)  *)
(** Most modern programming languages use a "short-circuit" evaluation
    rule for boolean [and]: to evaluate [BAnd b1 b2], first evaluate
    [b1].  If it evaluates to [false], then the entire [BAnd]
    expression evaluates to [false] immediately, without evaluating
    [b2].  Otherwise, [b2] is evaluated to determine the result of the
    [BAnd] expression.

    Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval]. *)

(* FILL IN HERE *)
(** [] *)

Module BreakImp.
(** **** Exercise: 4 stars, advanced (break_imp)  *)

(** Imperative languages like C and Java often include a [break] or
    similar statement for interrupting the execution of loops. In this
    exercise we consider how to add [break] to Imp.  First, we need to
    enrich the language of commands with an additional case. *)

Inductive com : Type :=
  | CSkip : com
  | CBreak : com               (* <-- new *)
  | CAss : id -> exp -> com
  | CSeq : com -> com -> com
  | CIf : exp -> com -> com -> com
  | CWhile : exp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** Next, we need to define the behavior of [BREAK].  Informally,
    whenever [BREAK] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the [BREAK]
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given [BREAK]. In those cases, [BREAK] should only
    terminate the _innermost_ loop. Thus, after executing the
    following...

       X ::= 0;;
       Y ::= 1;;
       WHILE 0 <> Y DO
         WHILE TRUE DO
           BREAK
         END;;
         X ::= 1;;
         Y ::= Y - 1
       END

    ... the value of [X] should be [1], and not [0].

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [BREAK] statement: *)

Inductive result : Type :=
  | SContinue : result
  | SBreak : result.

Reserved Notation "c1 '/' st '\\' s '/' st'"
                  (at level 40, st, s at level 39).

(** Intuitively, [c / st \\ s / st'] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that the innermost surrounding loop (or the whole program) should
    exit immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[c / st \\ s / st']" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([c / st \\ st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [SKIP], then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is [BREAK], the state stays unchanged but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [IFB b THEN c1 ELSE c2 FI], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ;; c2], we first execute
      [c1].  If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state is the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal
      generated there.

    - Finally, for a loop of the form [WHILE b DO c END], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises.  If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration.  In either case, since [BREAK] only terminates the
      innermost loop, [WHILE] signals [SContinue]. *)

(** Based on the above description, complete the definition of the
    [ceval] relation. *)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      CSkip / st \\ SContinue / st
  (* FILL IN HERE *)

  where "c1 '/' st '\\' s '/' st'" := (ceval c1 st s st').

(** Now prove the following properties of your definition of [ceval]: *)

Theorem break_ignore : forall c st st' s,
     (BREAK;; c) / st \\ s / st' ->
     st = st'.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st \\ s / st' ->
  s = SContinue.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st \\ SBreak / st' ->
  (WHILE b DO c END) / st \\ SContinue / st'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (while_break_true)  *)
Theorem while_break_true : forall b c st st',
  (WHILE b DO c END) / st \\ SContinue / st' ->
  beval st' b = true ->
  exists st'', c / st'' \\ SBreak / st'.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ceval_deterministic)  *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     c / st \\ s1 / st1  ->
     c / st \\ s2 / st2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)
End BreakImp.

(** **** Exercise: 4 stars, optional (add_for_loop)  *)
(** Add C-style [for] loops to the language of commands, update the
    [ceval] definition to define the semantics of [for] loops, and add
    cases for [for] loops as needed so that all the proofs in this file
    are accepted by Coq.

    A [for] loop should be parameterized by (a) a statement executed
    initially, (b) a test that is run on each iteration of the loop to
    determine whether the loop should continue, (c) a statement
    executed at the end of each loop iteration, and (d) a statement
    that makes up the body of the loop.  (You don't need to worry
    about making up a concrete Notation for [for] loops, but feel free
    to play with this too if you like.) *)

(* FILL IN HERE *)
(** [] *)

(* $Date: 2017-07-04 07:52:33 -0400 (Tue, 04 Jul 2017) $ *)

