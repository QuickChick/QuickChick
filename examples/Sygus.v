From QuickChick Require Import QuickChick.
Require Import List.
Import ListNotations.

Inductive exp :=
| X
| Y
| Zero
| One
| P (e1 e2: exp)
| ite (e e1 e2 : exp)
| T
| F
| Not (e : exp)
| And (e1 e2 : exp)
| Or (e1 e2 : exp)
| Lt (e1 e2 : exp).

Inductive res :=
| N (n : nat)
| B (b : bool).

Inductive eval : exp -> nat -> nat -> res -> Prop :=
| Eval_X : forall x y, eval X x y (N x)
| Eval_Y : forall x y, eval Y x y (N y)                            
| Eval_0 : forall x y, eval Zero x y (N 0)
| Eval_1 : forall x y, eval One x y (N 1)
(* | Eval_P : forall x y e1 e2 r1 r2,
    eval e1 x y (N r1) ->
    eval e2 x y (N r2) ->                       
    eval (P e1 e2) x y (N (r1 + r2)) (* Issue 1 *) *)
| Eval_ITE_T : forall x y e e1 e2 r,
    eval e x y (B true) ->
    eval e1 x y r ->
    eval (ite e e1 e2) x y r
| Eval_ITE_F : forall x y e e1 e2 r,
    eval e x y (B false) ->
    eval e2 x y r ->
    eval (ite e e1 e2) x y r
| Eval_T : forall x y, eval T x y (B true)
| Eval_F : forall x y, eval T x y (B false)                            
(* | Eval_Not : forall x y e b,
   eval e x y (B b) ->
   eval (Not e) x y (B (negb b)) *) 
| Eval_Lt_T : forall x y e1 e2 n1 n2,
    le (S n1) n2 -> 
    eval e1 x y (N n1) ->
    eval e2 x y (N n2) ->
    eval (Lt e1 e2) x y (B true)
| Eval_Lt_F : forall x y e1 e2 n1 n2,
    le n2 n1 ->     
    eval e1 x y (N n1) ->
    eval e2 x y (N n2) ->
    eval (Lt e1 e2) x y (B false).

Derive Show for res.
Derive (Arbitrary, Show) for exp.
Derive Generator for (fun y => le x y).
Derive Generator for (fun e => eval e x y r).

(*
QuickChickDebug Debug On.
Derive Enumerator for (fun r => eval e x y r).
Derive Checker for (eval e x y r).
 *)
Fixpoint evalc (e : exp) (x y : nat) : option res :=
  match e with
  | X => Some (N x)
  | Y => Some (N y)
  | Zero => Some (N 0)
  | One => Some (N 1)
  | ite e e1 e2 =>
      match evalc e x y with
      | Some (B true) => evalc e1 x y
      | Some (B false) => evalc e2 x y
      | _ => None
      end
  | T => Some (B true)
  | F => Some (B false)
  | Lt e1 e2 =>
      match evalc e1 x y, evalc e2 x y with
      | Some (N n1), Some (N n2) => Some (B (Nat.ltb n1 n2))
      | _, _ => None
      end
  | _ => None
  end.

Fixpoint partial_eval (e : exp) : exp :=
  match e with
  | X => X
  | Y => Y
  | Zero => Zero
  | One => One
  | ite e e1 e2 =>
      match partial_eval e with
      | T => partial_eval e1
      | F => partial_eval e2
      | e' => ite e' (partial_eval e1) (partial_eval e2)
      end
  | T => T
  | F => F
  | Lt e1 e2 =>
      match partial_eval e1, partial_eval e2 with
      | Zero, Zero => F
      | Zero, One => T
      | One, Zero => F
      | One, One => F
      | e1', e2' => Lt e1' e2'
      end
  | _ => e
  end.

Instance DecEqexp : Dec_Eq exp. dec_eq. Defined.

Definition stuck (e : exp) : bool := (e = (partial_eval e)) ? . 

Compute (stuck (ite X X Y)).

Definition shrinker e := if stuck e then [] else [partial_eval e].

Definition g :=
  genSizedST (fun e => eval e 2 4 (N 4)).

Instance DecEqRes : Dec_Eq res.
Proof. dec_eq. Defined.

Search shrink.

Definition forAllShrinkMaybe {A prop : Type} {_ : Checkable prop} `{Show A}
           (gen : G (option A)) (shrinker : A -> list A) (pf : A -> prop) : Checker :=
  bindGen gen (fun mx =>
                 match mx with
                 | Some x => shrinking shrinker x (fun x' =>
                                         printTestCase (show x' ++ newline) (pf x'))
                 | None => checker tt
                 end
              ).

Definition prop (ts : list (nat * nat * res)) :=
  let genSize := 5 in
  let defElemIgnore := (0,0, N 0) in
  forAll (elems_ defElemIgnore ts) (fun '(x,y,r) =>
  forAllShrinkMaybe (genSizedST (fun e => eval e x y r) genSize) shrinker (fun e => 
  negb (forallb (fun '(x,y,r) => 
  match evalc e x y with
  | Some r' => (r = r')?
  | _ => false
  end) ts))).

Definition test_cases : list (nat * nat * res) :=
  [ (4,2,N 4);(2,5,N 5);(1,1,N 1) ].

Extract Constant defNumTests => "100000". (*
QuickChick (prop test_cases).
QuickChick (prop [(1,1,B true); (3,3,B true); (0,1,B false); (0,2,B false); (0,0,B true); (2,0,B false)]).
*)
Derive Inductive Schedule eval 3 derive "Gen" opt "true".

Check ((let GenSizedSuchThateval_IIIOGen :=
   fix rec (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) (v10_ : @exp) (v11_ : @nat) (v12_ : @nat) :=
     match size with
     | @Coq.Init.Datatypes.O =>
         @QuickChick.Generators.backtrack _
           (@Coq.Init.Datatypes.cons _
              (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                 (@QuickChick.Generators.thunkGen _
                    (fun '_ =>
                     match v10_ with
                     | @X => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@N v11_))
                     | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                     end)))
              (@Coq.Init.Datatypes.cons _
                 (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                    (@QuickChick.Generators.thunkGen _
                       (fun '_ =>
                        match v10_ with
                        | @Y => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@N v12_))
                        | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                        end)))
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _
                          (fun '_ =>
                           match v10_ with
                           | @Zero => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@N (@Coq.Init.Datatypes.O)))
                           | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                           end)))
                    (@Coq.Init.Datatypes.cons _
                       (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                          (@QuickChick.Generators.thunkGen _
                             (fun '_ =>
                              match v10_ with
                              | @One =>
                                  @QuickChick.Generators.returnGen _
                                    (@Coq.Init.Datatypes.Some _ (@N (@Coq.Init.Datatypes.S (@Coq.Init.Datatypes.O))))
                              | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                              end)))
                       (@Coq.Init.Datatypes.cons _
                          (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                             (@QuickChick.Generators.thunkGen _
                                (fun '_ =>
                                 match v10_ with
                                 | @T => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@B (@Coq.Init.Datatypes.true)))
                                 | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                 end)))
                          (@Coq.Init.Datatypes.cons _
                             (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                                (@QuickChick.Generators.thunkGen _
                                   (fun '_ =>
                                    match v10_ with
                                    | @T =>
                                        @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@B (@Coq.Init.Datatypes.false)))
                                    | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                    end)))
                             (@Coq.Init.Datatypes.cons _
                                (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                                   (@QuickChick.Generators.thunkGen _
                                      (fun '_ =>
                                       match v10_ with
                                       | @Lt e1 e2 =>
                                           @QuickChick.Generators.bindGen _ _ (@QuickChick.Classes.arbitrarySized (@nat) _ init_size)
                                             (fun 'n1 =>
                                              if
                                               @QuickChick.Decidability.decOpt (@eval e1 v11_ v12_ (@N n1)) _
                                                 QuickChick.Decidability.checkable_size_limit
                                              then
                                               @QuickChick.Producer.bindOpt _ _ _ _
                                                 (@QuickChick.DependentClasses.arbitrarySizeST _
                                                    (fun 'n2 => @le (@Coq.Init.Datatypes.S n1) n2) _ init_size)
                                                 (fun 'n2 =>
                                                  if
                                                   @QuickChick.Decidability.decOpt (@eval e2 v11_ v12_ (@N n2)) _
                                                     QuickChick.Decidability.checkable_size_limit
                                                  then
                                                   @QuickChick.Generators.returnGen _
                                                     (@Coq.Init.Datatypes.Some _ (@B (@Coq.Init.Datatypes.true)))
                                                  else @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _))
                                              else @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _))
                                       | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                       end)))
                                (@Coq.Init.Datatypes.cons _
                                   (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                                      (@QuickChick.Generators.thunkGen _
                                         (fun '_ =>
                                          match v10_ with
                                          | @Lt e1 e2 =>
                                              @QuickChick.Generators.bindGen _ _ (@QuickChick.Classes.arbitrarySized (@nat) _ init_size)
                                                (fun 'n1 =>
                                                 if
                                                  @QuickChick.Decidability.decOpt (@eval e1 v11_ v12_ (@N n1)) _
                                                    QuickChick.Decidability.checkable_size_limit
                                                 then
                                                  @QuickChick.Producer.bindOpt _ _ _ _
                                                    (@QuickChick.DependentClasses.arbitrarySizeST _ (fun 'n2 => @le n2 n1) _ init_size)
                                                    (fun 'n2 =>
                                                     if
                                                      @QuickChick.Decidability.decOpt (@eval e2 v11_ v12_ (@N n2)) _
                                                        QuickChick.Decidability.checkable_size_limit
                                                     then
                                                      @QuickChick.Generators.returnGen _
                                                        (@Coq.Init.Datatypes.Some _ (@B (@Coq.Init.Datatypes.false)))
                                                     else @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _))
                                                 else @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _))
                                          | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                          end))) (@Coq.Init.Datatypes.nil _)))))))))
     | @Coq.Init.Datatypes.S size' =>
         @QuickChick.Generators.backtrack _
           (@Coq.Init.Datatypes.cons _
              (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                 (@QuickChick.Generators.thunkGen _
                    (fun '_ =>
                     match v10_ with
                     | @X => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@N v11_))
                     | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                     end)))
              (@Coq.Init.Datatypes.cons _
                 (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                    (@QuickChick.Generators.thunkGen _
                       (fun '_ =>
                        match v10_ with
                        | @Y => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@N v12_))
                        | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                        end)))
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _
                          (fun '_ =>
                           match v10_ with
                           | @Zero => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@N (@Coq.Init.Datatypes.O)))
                           | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                           end)))
                    (@Coq.Init.Datatypes.cons _
                       (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                          (@QuickChick.Generators.thunkGen _
                             (fun '_ =>
                              match v10_ with
                              | @One =>
                                  @QuickChick.Generators.returnGen _
                                    (@Coq.Init.Datatypes.Some _ (@N (@Coq.Init.Datatypes.S (@Coq.Init.Datatypes.O))))
                              | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                              end)))
                       (@Coq.Init.Datatypes.cons _
                          (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                             (@QuickChick.Generators.thunkGen _
                                (fun '_ =>
                                 match v10_ with
                                 | @T => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@B (@Coq.Init.Datatypes.true)))
                                 | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                 end)))
                          (@Coq.Init.Datatypes.cons _
                             (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                                (@QuickChick.Generators.thunkGen _
                                   (fun '_ =>
                                    match v10_ with
                                    | @T =>
                                        @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@B (@Coq.Init.Datatypes.false)))
                                    | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                    end)))
                             (@Coq.Init.Datatypes.cons _
                                (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                                   (@QuickChick.Generators.thunkGen _
                                      (fun '_ =>
                                       match v10_ with
                                       | @Lt e1 e2 =>
                                           @QuickChick.Generators.bindGen _ _ (@QuickChick.Classes.arbitrarySized (@nat) _ init_size)
                                             (fun 'n1 =>
                                              if
                                               @QuickChick.Decidability.decOpt (@eval e1 v11_ v12_ (@N n1)) _
                                                 QuickChick.Decidability.checkable_size_limit
                                              then
                                               @QuickChick.Producer.bindOpt _ _ _ _
                                                 (@QuickChick.DependentClasses.arbitrarySizeST _
                                                    (fun 'n2 => @le (@Coq.Init.Datatypes.S n1) n2) _ init_size)
                                                 (fun 'n2 =>
                                                  if
                                                   @QuickChick.Decidability.decOpt (@eval e2 v11_ v12_ (@N n2)) _
                                                     QuickChick.Decidability.checkable_size_limit
                                                  then
                                                   @QuickChick.Generators.returnGen _
                                                     (@Coq.Init.Datatypes.Some _ (@B (@Coq.Init.Datatypes.true)))
                                                  else @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _))
                                              else @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _))
                                       | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                       end)))
                                (@Coq.Init.Datatypes.cons _
                                   (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                                      (@QuickChick.Generators.thunkGen _
                                         (fun '_ =>
                                          match v10_ with
                                          | @Lt e1 e2 =>
                                              @QuickChick.Generators.bindGen _ _ (@QuickChick.Classes.arbitrarySized (@nat) _ init_size)
                                                (fun 'n1 =>
                                                 if
                                                  @QuickChick.Decidability.decOpt (@eval e1 v11_ v12_ (@N n1)) _
                                                    QuickChick.Decidability.checkable_size_limit
                                                 then
                                                  @QuickChick.Producer.bindOpt _ _ _ _
                                                    (@QuickChick.DependentClasses.arbitrarySizeST _ (fun 'n2 => @le n2 n1) _ init_size)
                                                    (fun 'n2 =>
                                                     if
                                                      @QuickChick.Decidability.decOpt (@eval e2 v11_ v12_ (@N n2)) _
                                                        QuickChick.Decidability.checkable_size_limit
                                                     then
                                                      @QuickChick.Generators.returnGen _
                                                        (@Coq.Init.Datatypes.Some _ (@B (@Coq.Init.Datatypes.false)))
                                                     else @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _))
                                                 else @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _))
                                          | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                          end)))
                                   (@Coq.Init.Datatypes.cons _
                                      (@Coq.Init.Datatypes.pair _ _ size
                                         (@QuickChick.Generators.thunkGen _
                                            (fun '_ =>
                                             match v10_ with
                                             | @ite e e1 e2 =>
                                                 if
                                                  @QuickChick.Decidability.decOpt (@eval e v11_ v12_ (@B (@Coq.Init.Datatypes.true))) _
                                                    QuickChick.Decidability.checkable_size_limit
                                                 then
                                                  @QuickChick.Producer.bindOpt _ _ _ _ (@rec init_size size' e1 v11_ v12_)
                                                    (fun 'v13_ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ v13_))
                                                 else @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                             | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                             end)))
                                      (@Coq.Init.Datatypes.cons _
                                         (@Coq.Init.Datatypes.pair _ _ size
                                            (@QuickChick.Generators.thunkGen _
                                               (fun '_ =>
                                                match v10_ with
                                                | @ite e e1 e2 =>
                                                    if
                                                     @QuickChick.Decidability.decOpt
                                                       (@eval e v11_ v12_ (@B (@Coq.Init.Datatypes.false))) _
                                                       QuickChick.Decidability.checkable_size_limit
                                                    then
                                                     @QuickChick.Producer.bindOpt _ _ _ _ (@rec init_size size' e2 v11_ v12_)
                                                       (fun 'v13_ =>
                                                        @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ v13_))
                                                    else @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                                | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                                end))) (@Coq.Init.Datatypes.nil _)))))))))))
     end in
 fun size : Coq.Init.Datatypes.nat => @GenSizedSuchThateval_IIIOGen size size)).

Derive Valid Schedules eval 3 consnum 8.

Derive Density eval 0.

Compute (evalc (ite (Lt X Y) Y X) 1 1).
Definition eqe x y := ite (Lt x y) F (ite (Lt y x) F T).

Compute (evalc (eqe X Y) 1 1).

(* And, Or *)
