From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import List ZArith.
Import ListNotations.
Import MonadNotation.

Inductive Ctx :=
| EmptyCtx
| CtxBind : Type -> Ctx -> Ctx.

Declare Scope prop_scope.
Notation "'∅'" := EmptyCtx : prop_scope.
Notation " A '·' C " :=
  (CtxBind A C) (at level 70) : prop_scope.

Local Open Scope prop_scope.

Fixpoint interpCtx (C : Ctx) : Type :=
  match C with
  | ∅ => unit
  | T·C => T * interpCtx C
  end.

Notation "'⟦' C '⟧'" := (interpCtx C) : prop_scope.

Inductive CProp : Ctx -> Type -> Type :=
| ForAll : forall A C F
      (name: string)
      (generator : ⟦C⟧ -> G A)
      (mutator   : ⟦C⟧ -> nat -> A -> G A)
      (shrinker  : ⟦C⟧ -> A -> list A)
      (printer   : ⟦C⟧ -> A -> string),
      CProp (A · C) F -> CProp C F
  | Predicate : forall C F,
      (⟦C⟧ -> option bool * F) -> CProp C F.

Fixpoint inputTypes {C : Ctx} {F : Type}
         (cprop : CProp C F) : Ctx :=
  match cprop with
  | ForAll A C _ _ _ _ _ _ cprop' =>
      A · (inputTypes cprop')
  | Predicate _ _ _ => ∅
  end.

Notation "'⦗' c '⦘'" := (@inputTypes _ _ c).

Definition typeHead {C : Ctx} {F : Type}
         (cprop : CProp C F) : Type :=
  match cprop with
  | ForAll A C _ _ _ _ _ _ cprop' => A
  | Predicate _ _ _ => unit
  end.

Definition arb : G nat := choose (0,1000).
Definition gen (n : nat) : G nat := choose (0, n).
Definition mut (k n : nat) : G nat :=
  choose (n - (5 + k), n + (5 + k)).
Definition test (x y : nat) : option bool :=
  Some (Nat.ltb y x).

Local Open Scope string.

Definition example :=
  @ForAll _ ∅ _ "x" (fun tt => arb) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) _ "y" (fun '(x, tt) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (nat · (nat · ∅)) unit
             (fun '(y, (x, tt)) => (test x y, tt)))).

Fixpoint genAndRun {C : Ctx} {F : Type}
         (cprop : CProp C F)
  : ⟦C⟧ -> G (⟦⦗cprop⦘⟧ * (option bool * F)) :=
  match cprop with
  | ForAll _ _ _ _ gen mut shr pri cprop' =>
      fun env =>
        a <- gen env;;
        res <- genAndRun cprop' (a,env);;
        let '(env', (truth, feedback)) := res in
        ret ((a,env'), (truth, feedback))
  | Predicate C F prop =>
      fun env => returnGen (tt, prop env)
  end.

Fixpoint justGen {C : Ctx} {F : Type}
         (cprop : CProp C F)
  : ⟦C⟧ -> G (⟦⦗cprop⦘⟧) :=
  match cprop with
  | ForAll _ _ _ _ gen mut shr pri cprop' =>
      fun env =>
        a <- gen env;;
        env <- justGen cprop' (a,env);;
        ret (a,env)
  | Predicate C F prop =>
      fun env => ret tt
  end.

Fixpoint mutAll {C : Ctx} {F : Type}
         (cprop : CProp C F) (t: nat)
  : ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> (G (⟦⦗cprop⦘⟧)) :=
  match cprop with
  | ForAll A C F name gen mut shr pri cprop' =>
      fun env '(x,xs) =>
        x' <- mut env t x;;
        xs' <- mutAll cprop' t (x', env) xs;;
        ret (x', xs')
  | Predicate C F prop =>
      fun _ _ => ret tt
  end.

Fixpoint mutSome {C : Ctx} {F : Type}
  (cprop : CProp C F) (t: nat)
: ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> (G (⟦⦗cprop⦘⟧)) :=
  match cprop with
  | ForAll A C F name gen mut shr pri cprop' =>
    fun env '(x,xs) =>
    mut_oracle <- choose (0, 1);;
    x' <- mut env t x;;
    xs' <- mutSome cprop' t (x', env) xs;;
    match mut_oracle with
    | 0 => ret (x', xs')
    | _ => ret (x, xs')
    end
  | Predicate C F prop =>
  fun _ _ => ret tt
end.

Fixpoint print {C : Ctx} {F} (cprop : CProp C F)
  : ⟦C⟧ -> ⟦⦗ cprop ⦘⟧ -> list (string * string) :=
  match cprop with
  | ForAll A C F name gen mut shr pr cprop' =>
      fun env '(a,inps') =>
        (name, pr env a) :: (print cprop' (a, env) inps')
  | Predicate C F prop =>
      fun _ _ => nil
  end.

Fixpoint showElemList (l: list (string * string)) : string :=
  match l with
  | [] => ""
  | ((k, v) :: []) => (k ++ ": " ++ v) 
  | ((k, v) :: t) => (k ++ ": " ++ v ++ ", " ++ showElemList t)
  end.

Local Open Scope Z.

Record Seed {A F: Type} := {
  input: A;
  feedback: F;
  energy: Z;
}.

Definition mkSeed {A F: Type} (a: A) (f: F) (e: Z): Seed := {| input := a; feedback := f; energy := e |}.

Definition Temperature := Z.

Inductive Directive {A F: Type} :=
| Generate : Directive
| Mutate : @Seed A F -> Temperature -> Directive
.

#[global] Instance showDirective {A F: Type} : Show (@Directive A F) :=
{|
  show d := match d with
            | Generate => "Generate"
            | Mutate _ t => "Mutate(" ++ show t ++ ")"
            end
|}.


Class SeedPool {A F Pool: Type} := {
  (* Creates an empty pool. *)
  mkPool  : unit -> Pool;
  (* Adds a useful seed into the pool. *)
  invest  : (A * F) -> Pool -> Pool;
  (* Decreases the energy of a seed after a useless trial. *)
  revise  : Pool -> A -> (A * F) -> Pool;
  (* Samples the pool for an input. *)
  sample  : Pool -> @Directive A F;
  (* Returns the best seed in the pool. *)
  best    : Pool -> option (@Seed A F);
}.



Class Utility {A F Pool: Type} `{SeedPool A F Pool} := {
  (* Returns true if the feedback is interesting. *)
  useful  : Pool -> F -> bool;
  (* Returns a metric of how interesting the feedback is. *)
  utility : Pool -> F -> Z;
}.

Class Scalar (A : Type) :=
  { scale : A -> Z }.

#[global] Instance ScalarZ : Scalar Z :=
  {| scale := fun x => x |}.


(* Class Scheduler {A F Pool: Type} `{SeedPool A F Pool} := {
  invest  : (A * F) -> Pool -> Pool;
  revise  : Pool -> A -> (A * F) -> Pool;
}. *)

Record SingletonPool {A F: Type} := {
  seed: option (@Seed A F);
}.

#[global] Instance StaticSingletonPool {A F: Type} `{Dec_Eq A} `{Scalar F} : @SeedPool A F (@SingletonPool A F) :=
  {| mkPool _ := {| seed := None |};
     invest seed pool := match seed with 
                         | (a, f) => {| seed := Some (mkSeed a f 1) |}
                         end ;
     revise pool a _ := pool ;
     sample pool := match seed pool with
                    | None => Generate
                    | Some seed => Mutate seed 1
                    end ;
     best pool := seed pool
  |}.

#[global] Instance DynamicMonotonicSingletonPool {A F: Type} `{Dec_Eq A} `{Scalar F} : @SeedPool A F (@SingletonPool A F) :=
  {| mkPool _ := {| seed := None |};
    invest seed pool := match seed with 
                        | (a, f) => {| seed := Some (mkSeed a f 100) |}
                        end ;
    revise pool a _ := match seed pool with
                       | None => pool
                       | Some seed => 
                        let a' := input seed in
                        let f := feedback seed in
                        let n := energy seed in
                        if (a = a')? then {| seed := Some (mkSeed a f (n - 1)) |} else pool
                        end ;               
    sample pool := match seed pool with
                   | None => Generate
                   | Some seed => if (energy seed =? 0) 
                                    then Generate
                                    else if (energy seed >=? 93) then Mutate seed (energy seed - 50)
                                    else Mutate seed (100 - energy seed)

                   end ;
    best pool := seed pool
|}.

#[global] Instance DynamicResettingSingletonPool {A F: Type} `{Dec_Eq A} `{Scalar F} : @SeedPool A F (@SingletonPool A F) :=
  {| mkPool _ := {| seed := None |};
    invest seed pool := match seed with 
                        | (a, f) => {| seed := Some (mkSeed a f 100) |}
                        end ;
    revise pool a _ := match seed pool with
                       | None => pool
                       | Some seed => 
                        let a' := input seed in
                        let f := feedback seed in
                        let n := energy seed in
                        if (a = a')? then {| seed := Some (mkSeed a f (n - 1)) |} else pool
                        end ;               
    sample pool := match seed pool with
                   | None => Generate
                   | Some seed => if (energy seed =? 0) 
                                    then Generate
                                    else if (energy seed >=? 96) then Mutate seed (energy seed - 50)
                                    else Mutate seed (100 - energy seed)
                   end ;
    best pool := match seed pool with
                 | None => None
                 | Some seed => if (energy seed =? 0) then None else Some seed
                 end
|}.


#[global] Instance HillClimbingUtility {A F Pool} `{SeedPool A F Pool} `{Scalar F} 
: Utility := 
{|
  useful  := fun pool feedback' => match best pool with
                                  | None => true
                                  | Some seed => (scale feedback') >? (scale (feedback seed))
                                  end;
  utility := fun pool feedback' => match best pool with
                                  | None => scale feedback'
                                  | Some seed => scale feedback' - (scale (feedback seed))
                                  end
|}.

(* 
Record DoubleQueuePool {A E : Type} := {
  hpq: list (A * E);
  lpq: list (A * E);
}.

Definition insertHighPrioritySeed {A E: Type} (seed: (A * E)) (pool: DoubleQueuePool) : DoubleQueuePool :=
  {| hpq := (seed :: (hpq pool)) ; lpq := (lpq pool) |}.

Definition insertLowPrioritySeed {A E: Type} (seed: (A * E)) (pool: DoubleQueuePool) : DoubleQueuePool :=
  {| hpq := (hpq pool) ; lpq := (seed :: (lpq pool)) |} .

Fixpoint maxSeed {A E: Type} `{OrdType E} (cmax: option (A * E)) (q: list (A * E)) : option A :=
  match q with
  | [] => match cmax with
          | None => None
          | Some (a, e) => Some a
          end
  | (h :: t) => match cmax with
                | None => maxSeed (Some h) t
                | Some (a, e) => if leq e (snd h) then maxSeed (Some h) t else maxSeed (Some (a, e)) t
                end
  end.

Definition sampleSeedDQP {A E : Type} `{OrdType E} (pool: DoubleQueuePool) : option A * DoubleQueuePool :=
  match (hpq pool) with
  | []  => (maxSeed None (lpq pool), pool)
  | _   => (maxSeed None (hpq pool), pool)
  end.


  #[global] Instance SeedPoolDQP {A E : Type} `{OrdType E} : @SeedPool A E (@DoubleQueuePool A E) :=
  {| mkPool _ := {| hpq := []; lpq := [] |};
     schedule pool seed := pool;
     insert seed pool := {| hpq := seed :: (hpq pool); lpq := lpq pool |};
     sample pool :=
       match (hpq pool) with
       | []  => (maxSeed None (lpq pool), pool)
       | _   => (maxSeed None (hpq pool), pool)
       end
  |}. *)



Fixpoint runAndTest {C:Ctx} {F : Type} (cprop : CProp C F)
         (cenv : ⟦C⟧)
         (fenv :  ⟦⦗cprop⦘⟧)
         {struct cprop}
  : option bool * F.
Proof.
  induction cprop; simpl in *.
  - destruct fenv as [a fenv'] eqn:H.
    apply IHcprop.
    + exact (a, cenv).
    + exact fenv'.
  - exact (p cenv).
Defined.


Fixpoint shrinkOnTheFly
  {C : Ctx} {F: Type}
  (cprop : CProp C F)
  (cenv :  ⟦C⟧)
  (fenv :  ⟦⦗cprop⦘⟧)
  {struct cprop}
  : option ⟦⦗cprop⦘⟧.
Proof.
  induction cprop; simpl in *.
  - destruct fenv as [a fenv']. 
    (* Recurse through the list of shrinks *)
    induction (shrinker cenv a).
    (* No more shrinks - try the next element of the property *)
    + destruct (shrinkOnTheFly _ _ cprop (a,cenv) fenv') eqn:M.
      * exact (Some (a, i)).
      * exact None.
    (* More shrinks - run the property on the shrunk possibility. *)
    + destruct (runAndTest cprop (a0,cenv) fenv') eqn:T. destruct o.
      * destruct b.
        (* Test succeeded - recurse down the list. *)
        -- apply IHl.
        (* Test failed - end with current result. *)
        -- exact (Some (a0, fenv')).     
      * (* Test discarded - recurse down the list. *)
        apply IHl.
  - exact None.
Defined.

Fixpoint shrinkLoop {F: Type} (fuel : nat)
  (cprop: CProp ∅ F) (counterexample : ⟦⦗cprop⦘⟧) :
  ⟦⦗cprop⦘⟧ :=
  match fuel with
  | O => counterexample
  | S fuel' =>
      match shrinkOnTheFly cprop tt counterexample with
      | Some c' => shrinkLoop fuel' cprop c'
      | None => counterexample
      end
  end.

Definition generator (cprop: CProp ∅ Z) (directive: @Directive ⟦⦗cprop⦘⟧ Z) :=
  match directive with
  | Generate => justGen cprop tt
  | Mutate seed t => mutAll cprop (Z.to_nat t) tt (input seed)
  end.

  
Fixpoint targetLoop (fuel : nat)
         (cprop : CProp ∅ Z)
         {Pool : Type}
         (seeds : Pool)
         (poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool)
         (utility: Utility)
  : G (list (string * string)) :=
  match fuel with
  | O => ret []
  | S fuel' => 
      let directive := sample seeds in
      seed <- generator cprop directive;;
      let res := runAndTest cprop tt seed in
      let '(truth, feedback) := res in
      match truth with
      | Some false =>
          (* Fails *)
          let shrinkingResult := shrinkLoop 10 cprop seed in
          let printingResult := print cprop tt shrinkingResult in
          ret printingResult
      | Some true =>
          (* Passes *)
          match useful seeds feedback with
          | true =>
              let seeds' := invest (seed, feedback) seeds in
              targetLoop fuel' cprop seeds' poolType utility
          | false =>
              let seeds' := match directive with
                            | Generate => seeds
                            | Mutate source _ => revise seeds (input source) (seed, feedback)
                            end in
              targetLoop fuel' cprop seeds' poolType utility
          end
      | None => 
          (* Discard *)
          targetLoop fuel' cprop seeds poolType utility
      end
  end.

Definition test2 (x y : nat) : option bool :=
  Some (negb (Nat.eqb y  x)).


Definition example2 :=
  @ForAll _ ∅ _ "x" (fun tt => arb) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) _ "y" (fun '(x, tt) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (nat · (nat · ∅)) Z
              (fun '(y, (x, tt)) => (test2 x y, 0)))).

Definition example3 :=
  @ForAll _ ∅ _ "x" (fun tt => arb) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) _ "y" (fun '(x, tt) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (nat · (nat · ∅)) Z
              (fun '(y, (x, tt)) => (test2 x y, (2000 - Z.of_nat(x - y) - Z.of_nat(y - x)))))).
              

    
(* Sample (targetLoop 1000 example2 (mkPool tt) StaticSingletonPool HillClimbingUtility).
Sample (targetLoop 1000 example3 (mkPool tt) StaticSingletonPool HillClimbingUtility).
Sample (targetLoop 1000 example2 (mkPool tt) DynamicSingletonPool HillClimbingUtility).
Sample (targetLoop 1000 example3 (mkPool tt) DynamicSingletonPool HillClimbingUtility). *)


Definition Log := list (string).

Definition printSeed (cprop : CProp ∅ Z ) (seed: @Seed ⟦⦗cprop⦘⟧ Z) : string :=
   showElemList (print cprop tt (input seed)) ++ ", feedback: " ++ show (feedback seed) ++ ", energy: " ++ show (energy seed).

#[local] Instance showListNL {A: Type} `{Show A} : Show (list A) :=
  {| show l := String.concat nl (map show l) |}.


Fixpoint targetLoopLogged (fuel : nat)
         (cprop : CProp ∅ Z)
         {Pool : Type}
         (seeds : Pool)
         (poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool)
         (utility: Utility)
         (log   : Log)
  : G Log :=
  match fuel with
  | O => ret (rev log)
  | S fuel' => 
      let directive := sample seeds in
      seed <- generator cprop directive;;
      let res := runAndTest cprop tt seed in
      let '(truth, feedback) := res in
      let printedSeed := showElemList (print cprop tt seed) in
      
      let printedSource := match directive with 
                           | Generate => "None"
                           | Mutate seed _ => printSeed cprop seed
                           end in
      let log := ("source: [" ++ printedSource ++ "], seed: [" ++ printedSeed ++ ", feedback: " ++ show feedback ++ "], truth: " ++ show truth ++ ", fuel: " ++ show fuel ++ ", directive:" ++ show directive) :: log in
      match truth with
      | Some false =>
          (* Fails *)
          ret (rev log)
      | Some true =>
          (* Passes *)
          match useful seeds feedback with
          | true =>
              let seeds' := invest (seed, feedback) seeds in
              targetLoopLogged fuel' cprop seeds' poolType utility log
          | false =>
              let seeds' := match directive with
                          | Generate => seeds
                          | Mutate source _ => revise seeds (input source) (seed, feedback)
                          end in
              targetLoopLogged fuel' cprop seeds' poolType utility log
          end
      | None => 
          (* Discard *)
          targetLoopLogged fuel' cprop seeds poolType utility log
      end
  end.

Sample1 (targetLoopLogged 1000 example3 (mkPool tt) StaticSingletonPool HillClimbingUtility nil).
Sample1 (targetLoopLogged 1000 example3 (mkPool tt) DynamicMonotonicSingletonPool HillClimbingUtility nil).
Sample1 (targetLoopLogged 1000 example3 (mkPool tt) DynamicResettingSingletonPool HillClimbingUtility nil).

(*

Fixpoint generalizedTargeting (fuel : nat) {C} {F}
         (cprop: CProp C F)
    (* TODO : better data structure for seed pool *)
         (seed_pool : SeedPool ⟦C⟧)
         {K V Agg : Type}
         {d: @Domain K V Agg}
         (update_agg : Agg -> F -> ⟦C⟧ -> Agg)
         (is_waypoint: Agg -> F -> bool)
         (priority : Agg -> F -> nat) : G option bool :=
  match fuel with 
  | O => _
  | S fuel' =>
      (* Zero: Decide how to generate based on seed_pool *)
      (* This is just random *)
      res <- genAndRun cprop ∅;;
      let '(inputs, (truth, feedback)) := res in
      (* First: Check truth.. *)
      match truth with
      | None => generalizedTargeting ....
      | Some true => 
        (* Second: Check feedback *)
        if is_waypoint agg feedback then
          let agg' := update_agg agg feedback inputs in
          let seed_pool := ... in
          generalizedTargeting ....                            
        else
          generalizedTargeting ....
      | Some false =>
          generalizedTargeting ....
      end



(*
Inductive Domain {K V A: Type} :=
| D : forall
            (a0: A)  
            (reducer: (A * V) -> A),
            Domain.

Definition a0 {K V A: Type} (d: @Domain K V A) : A :=
  match d with
  | D a0 _ => a0
  end.


Inductive Dsf (K V: Type) := 
| l: list (K * V) -> Dsf K V
.

Axiom find : forall {K V: Type} (dsf: Dsf K V) (k: K), V.

Definition apply_reducer {K V A: Type} (d: @Domain K V A) (agg: A) (k: K) (feedback: Dsf K V) : A :=
  match d with
  | D _ reducer => reducer (agg, find feedback k)
  end.
  
  
Fixpoint aggregate_feedback {K V A: Type} (d: Domain) (k: K) (feedback_list: list (Dsf K V)) : A :=
  match feedback_list with
  | [] => a0 d
  | (cons h t) => apply_reducer d (aggregate_feedback d k t) k h
  end.

Axiom eq_agg : forall {K V A: Type} {d: @Domain K V A} (a1 a2: A), bool.

(* 

Definitions:

  A(S,k,d) = a0 |> dsf_i1(k) |> dsf_i2(k) |> ... |> dsf_in(k), where d =(K,V,A,a0,|>)

  is_waypoint(i,S,d) = ∃k ∈K :A(S,k,d),A(S ∪ {i},k,d),whered =(K,V,A,a0,|>)

Observation;

  A(S,k,d) = a0 |> dsf_i1(k) |> dsf_i2(k) |> ... |> dsf_in(k)
  => A(S ∪ {i},k,d) = A(S,k,d) |> dsf_i(k)

  dsf_i = feedback(i)

  
  A(S,k,d) ~~> A(DSF,k,d)
    where DSF = {dsf_i1, dsf_i2, ..., dsf_in}




*)

(* Definition is_waypoint_for_key {K V A: Type} (k: K) (d: @Domain K V A) (agg: A) (feedback: (dsf K V)) : bool :=
    let augmented_agg := apply_reducer d agg k feedback in
    if (eq_agg augmented_agg agg) then false else true. *)

Axiom is_waypoint_for_key : forall {K V A: Type} (k: K) (d: @Domain K V A) (agg: A) (feedback: (Dsf K V)), bool.

    
Definition is_waypoint {K V A: Type} (d: @Domain K V A) (agg: A) (feedback: (Dsf K V)) : bool :=
  match feedback with
  | l  _ _ feedback_list => 
    let results := map (fun kv => (is_waypoint_for_key (fst kv) d agg feedback)) feedback_list in 
    fold_left orb results false
  end.
*)

Fixpoint runAndTest (C:Ctx) (cprop : CProp C)
         (cenv : ⟦C⟧)
         (fenv :  ⟦finalCtx C cprop⟧)
         {struct cprop}
  : option bool.
Proof.
  induction cprop; simpl in *.
  - destruct fenv as [a fenv'] eqn:H.
    apply IHcprop.
    + exact (a, cenv).
    + exact fenv'.
  - exact (o cenv).
Defined.

Compute (runAndTest ∅ example tt (3,(4,tt))).
Compute (runAndTest ∅ example tt (4,(3,tt))).


Fixpoint shrinkLoopLog (fuel : nat)
  (cprop: CProp ∅) (counterexample : ⟦finalCtx ∅ cprop⟧) :
  list  ⟦finalCtx ∅ cprop⟧ :=
  match fuel with
  | O => [counterexample]
  | S fuel' =>
      match shrinkOnTheFly ∅ cprop tt counterexample with
      | Some c' => (counterexample :: shrinkLoopLog fuel' cprop c')
      | None => [counterexample]
      end
  end.

Compute (shrinkLoopLog 10  example (3,(4,tt))).

Fixpoint runLoop1 (fuel: nat)
         (cprop: CProp ∅) : G (list string) :=
  match fuel with
  | 0 => returnGen []
  | S fuel' =>
      bindGen (genAndTestResult ∅ emptyEnv cprop)
              (fun res =>
                  returnGen (print ∅ cprop tt (fst res)))
               
  end.

Fixpoint runLoop2 (fuel: nat)
         (cprop: CProp ∅) : G (list string) :=
  match fuel with
  | 0 => returnGen []
  | S fuel' =>
      bindGen (genAndTestResult ∅ emptyEnv cprop)
              (fun res =>
                 match res with
                 | (variables, result) =>
                     match result with
                     | Some false =>
                                let shrinked := shrinkLoop 10 cprop (fst res) in
                                 returnGen (print ∅ cprop tt shrinked)
                     | None | Some true => runLoop2 fuel' cprop
                     end
                 end)
               
  end.

Fixpoint genAndTestLoop (fuel: nat)
         (cprop: CProp ∅) : G (option ⟦finalCtx ∅ cprop⟧) :=
  match fuel with
  | 0 => returnGen None
  | S fuel' =>
      bindGen (genAndTestResult ∅ emptyEnv cprop)
              (fun res =>
                 match res with
                 | (variables, result) =>
                     match result with
                     | Some false => returnGen (Some variables)
                     | None | Some true => genAndTestLoop fuel' cprop
                     end
                 end)
               
  end.

Fixpoint runLoop3 (fuel: nat)
         (cprop: CProp ∅) : G (list string) :=
  generationResult <- genAndTestLoop fuel cprop ;;
  match generationResult with
  | None => returnGen []
  | Some variables =>
      let shrinkingResult := shrinkLoop 10 cprop variables in
      let printingResult := print ∅ cprop tt shrinkingResult in
      returnGen printingResult
  end
.


Sample (runLoop3 10 example).
*)
