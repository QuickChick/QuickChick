From QuickChick Require Import QuickChick.

Inductive Foo (X : Type) :=
| A : X -> Foo X
| B : X -> Foo X.

Derive GenSized for Foo. Print GenSizedFoo. Check @freq_. 
Derive EnumSized for Foo. Print EnumSizedFoo. Locate oneOf_.
Check @oneOf_.

Check @freq_. 

Arguments A {X}.
Arguments B {X}.
Derive Show for Foo.

Set Printing All.

(*
Definition f :=
  let fix f (x : Foo) :=
    match x with
    | A => 42
    | B => 0
    end in f A.
 *)

Locate oneof.

Derive GenSized for nat.
Print GenSizednat.

Inductive Fooish {T} : Foo T -> Foo T -> Prop :=
| AS : forall x, Fooish (A x) (A x)
| BS : forall x y, Fooish (B x) (B y).



(* 
Instance GenSizedSuchThat_foo :
  GenSizedSuchThat _ (fun '(x,y) => Fooish x y) :=
  { arbitrarySizeST := fun n => returnGen (Some (A,A)) }.

Sample (@arbitraryST _ (fun '(x,y) => Fooish x y) _).
 *)
QuickChickDebug Debug On. Check @forAll.

Derive Generator for (fun ft => Fooish ft ft'). Print Coq.Init.Nat.one.
Derive Checker for (Fooish a b).
Derive Enumerator for (fun ft => Fooish ft ft').
(**

Definition a := (@QuickChick.Checker.forAllMaybe _ _ _ _ (@QuickChick.DependentClasses.arbitraryST _ (fun 'e' => @bigstep' e e') _)
   (fun 'e' =>
    @Quickchick.Checker.forAllMaybe _ _ _ _ (@QuickChick.DependentClasses.arbitraryST _ (fun 'e => @typing' Gamma e tau) _)
      (fun 'e =>
       @Quickchick.Checker.forAll _ _ _ _ (@Quickchick.Classes.arbitrary (@type) _)
         (fun 'tau =>
          @Quickchick.Checker.forAll _ _ _ _ (@Quickchick.Classes.arbitrary (@list (@type)) _)
            (fun 'Gamma =>
             match @Quickchick.Decidability.decOpt (@typing' Gamma e' tau) _ Quickchick.Decidability.checkable_size_limit with
             | @Some _ (@true) =>
                 @Quickchick.Checker.checker _ _ (@Coq.Init.Datatypes.Some Coq.Init.Datatypes.bool Coq.Init.Datatypes.true)
             | @Some _ (@false) =>
                 @Quickchick.Checker.checker _ _ (@Coq.Init.Datatypes.Some Coq.Init.Datatypes.bool Coq.Init.Datatypes.false)
             | @None => @Quickchick.Checker.checker _ _ Coq.Init.Datatypes.tt
             end))))).*)

Theorem qaegweg : @Fooish nat (A 0) (A 0).
Proof. 

  Fixpoint blah n := match n with | 0 => 0 | S n => S (blah n) end

  with blur n := match n with | 0 => 0 | S n => S (S (blur n)) end.
  
Abort.

Inductive type := N | Arrow (i o : type).

Inductive term :=
| Const (n : nat)
| App (f x : term)
| Abs (ty : type) (e : term)
| Id (x : nat)
.

Print blur.

Inductive bind : list type -> nat -> type -> Prop :=
| BindNow   : forall tau env, bind (tau :: env) O tau
| BindLater : forall tau tau' x env,
    bind env x tau -> bind (tau' :: env) (S x) tau.

  Inductive typing (G : list type) : term -> type -> Prop :=
  | TId :
      forall x t,
        bind G x t ->
        typing G (Id x) t
  | TConst :
      forall n,
        typing G (Const n) N
  | TAbs :
      forall e t1 t2,
        typing (t1 :: G) e t2 ->
        typing G (Abs t1 e) (Arrow t1 t2)
  | TApp :
      forall e1 e2 t1 t2,
        typing G e2 t1 ->
        typing G e1 (Arrow t1 t2) ->
        typing G (App e1 e2) t2.


#[global] Instance Dec_Eqtype (t t' : type) : Dec (t = t').
Proof. dec_eq. Defined.
Derive DecOpt for (bind env x t).
Derive EnumSized for type.
Derive Enumerator for (fun ty => typing env e ty).



Definition check_typing := (fix rec init_size size G e tau :=
   match size with
   | @Coq.Init.Datatypes.O =>
       @QuickChick.Decidability.checker_backtrack
         (@Coq.Init.Datatypes.cons _
            (fun '_ =>
             match tau with
             | t =>
                 match e with
                 | @Id x =>
                     @QuickChick.Decidability.andBind
                       (@QuickChick.Decidability.decOpt (@bind G x t) _ QuickChick.Decidability.checkable_size_limit)
                       (@Coq.Init.Datatypes.Some Coq.Init.Datatypes.bool Coq.Init.Datatypes.true)
                 | _ => @Coq.Init.Datatypes.None _
                 end
             end)
            (@Coq.Init.Datatypes.cons _
               (fun '_ =>
                match tau with
                | @N =>
                    match e with
                    | @Const n => @Coq.Init.Datatypes.Some Coq.Init.Datatypes.bool Coq.Init.Datatypes.true
                    | _ => @Coq.Init.Datatypes.None _
                    end
                | _ => @Coq.Init.Datatypes.None _
                end) (@Coq.Init.Datatypes.nil _)))
   | @Coq.Init.Datatypes.S size' =>
       @QuickChick.Decidability.checker_backtrack
         (@Coq.Init.Datatypes.cons _
            (fun '_ =>
             match tau with
             | t =>
                 match e with
                 | @Id x =>
                     @QuickChick.Decidability.andBind
                       (@QuickChick.Decidability.decOpt (@bind G x t) _ QuickChick.Decidability.checkable_size_limit)
                       (@Coq.Init.Datatypes.Some Coq.Init.Datatypes.bool Coq.Init.Datatypes.true)
                 | _ => @Coq.Init.Datatypes.None _
                 end
             end)
            (@Coq.Init.Datatypes.cons _
               (fun '_ =>
                match tau with
                | @N =>
                    match e with
                    | @Const n => @Coq.Init.Datatypes.Some Coq.Init.Datatypes.bool Coq.Init.Datatypes.true
                    | _ => @Coq.Init.Datatypes.None _
                    end
                | _ => @Coq.Init.Datatypes.None _
                end)
               (@Coq.Init.Datatypes.cons _
                  (fun '_ =>
                   match tau with
                   | @Arrow t1' t2 =>
                       match e with
                       | @Abs t1 e =>
                           @QuickChick.Decidability.andBind
                             (@QuickChick.Decidability.decOpt (@eq (@type) t1 t1') _ QuickChick.Decidability.checkable_size_limit)
                             (@QuickChick.Decidability.andBind
                                (rec init_size size' (cons t1 G) e t2)
                                (@Coq.Init.Datatypes.Some Coq.Init.Datatypes.bool Coq.Init.Datatypes.true))
                       | _ => @Coq.Init.Datatypes.None _
                       end
                   | _ => @Coq.Init.Datatypes.None _
                   end)
                  (@Coq.Init.Datatypes.cons _
                     (fun '_ =>
                      match tau with
                      | t2 =>
                          match e with
                          | @App e1 e2 =>
                              @QuickChick.Enumerators.enumeratingOpt _
                                (@QuickChick.DependentClasses.enumSuchThat _ (fun t1 => @typing G e2 t1) _)
                                (fun t1 =>
                                 @QuickChick.Decidability.andBind
                                   (rec init_size size' G e1 (@Arrow t1 t2))
                                   (@Coq.Init.Datatypes.Some Coq.Init.Datatypes.bool Coq.Init.Datatypes.true)) init_size
                          | _ => @Coq.Init.Datatypes.None _
                          end
                      end) (@Coq.Init.Datatypes.nil _)))))
   end).

Check check_typing.

Print check_typing.

Derive Checker for (typing G e ty).

Compute check_typing.

Compute (check_typing 100 100 nil (Const 0) N).

Locate bindOpt.

Definition gen_bind := (let name_Gen :=
   fix rec init_size size (env : list type) :=
     match size with
     | @Coq.Init.Datatypes.O =>
         @QuickChick.Generators.backtrack _
           (@Coq.Init.Datatypes.cons _
              (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                 (@QuickChick.Generators.thunkGen _
                    (fun '_ =>
                     match env with
                     | @cons _ tau env => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@pair _ _ (@O) tau))
                     | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                     end))) (@Coq.Init.Datatypes.nil _))
     | @Coq.Init.Datatypes.S size' =>
         @QuickChick.Generators.backtrack _
           (@Coq.Init.Datatypes.cons _
              (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                 (@QuickChick.Generators.thunkGen _
                    (fun '_ =>
                     match env with
                     | @cons _ tau env => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@pair _ _ (@O) tau))
                     | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                     end)))
              (@Coq.Init.Datatypes.cons _
                 (@Coq.Init.Datatypes.pair _ _ size
                    (@QuickChick.Generators.thunkGen _
                       (fun '_ =>
                        match env with
                        | @cons _ tau' env =>
                            @QuickChick.Producer.bindOpt _ _ _ _ (@rec init_size size' env)
                              (fun '(@Coq.Init.Datatypes.pair _ _ x tau) =>
                               @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@pair _ _ (@S x) tau)))
                        | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                        end))) (@Coq.Init.Datatypes.nil _)))
     end in
                        fun size => @name_Gen size size).

Definition gen_bind' := (let bind_iooGen :=
   fix rec
     (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat)
     (env : @list (@type)) :=
     match size with
     | @Coq.Init.Datatypes.O =>
         @QuickChick.Generators.backtrack _
           (@Coq.Init.Datatypes.cons _
              (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                 (@QuickChick.Generators.thunkGen _
                    (fun '_ =>
                     match env with
                     | @cons _ tau env =>
                         @QuickChick.Generators.returnGen _
                           (@Coq.Init.Datatypes.Some _ (@pair _ _ (@O) tau))
                     | _ =>
                         @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                     end))) (@Coq.Init.Datatypes.nil _))
     | @Coq.Init.Datatypes.S size' =>
         @QuickChick.Generators.backtrack _
           (@Coq.Init.Datatypes.cons _
              (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                 (@QuickChick.Generators.thunkGen _
                    (fun '_ =>
                     match env with
                     | @cons _ tau env =>
                         @QuickChick.Generators.returnGen _
                           (@Coq.Init.Datatypes.Some _ (@pair _ _ (@O) tau))
                     | _ =>
                         @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                     end)))
              (@Coq.Init.Datatypes.cons _
                 (@Coq.Init.Datatypes.pair _ _ size
                    (@QuickChick.Generators.thunkGen _
                       (fun '_ =>
                        match env with
                        | @cons _ tau' env =>
                            @QuickChick.Producer.bindOpt _ _ _ _
                              (@rec init_size size' env)
                              (fun '(@Coq.Init.Datatypes.pair _ _ x tau) =>
                               @QuickChick.Generators.returnGen _
                                 (@Coq.Init.Datatypes.Some _ (@pair _ _ (@S x) tau)))
                        | _ =>
                            @QuickChick.Generators.returnGen _
                              (@Coq.Init.Datatypes.None _)
                        end))) (@Coq.Init.Datatypes.nil _)))
     end in
 fun size : Coq.Init.Datatypes.nat => @bind_iooGen size size).

Check gen_bind'. Locate nat.

QuickChickDebug Debug Off.
Derive Testing for (fun '(x,y,z,w) => Fooish x y z). 
Derive Testing for (Fooish x y). 
Derive Testing for (fun x => Fooish x y). 





