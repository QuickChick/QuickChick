Inductive typ : Set :=
| TNat
| TArrow (t1 t2 : typ)
.

Inductive term : Set :=
| Var (x : nat)
| Abs (x : nat) (t : typ) (e : term)
| App (e1 e2 : term)
| Const (n : nat)
.

Inductive value : term -> Prop :=
| VAbs : forall x t e, value (Abs x t e)
| VConst : forall n, value (Const n)
.

Inductive bind_val : list (nat * term) -> nat -> term -> Prop :=
| bv_here : forall env v t, bind_val ((v,t) :: env) v t 
| bv_later : forall env v t v' t', v <> v' -> True -> bind_val env v t -> bind_val ((v',t') :: env) v t 
.

Require Import Init Arith Logic Bool List.
Import ListNotations. 

Fixpoint eq_nat (x y : nat) : bool :=
  match x, y with
  | 0,0 => true
  | S x, S y => eq_nat x y
  | _, _ => false
  end.

Fixpoint mem (x : nat) (l : list nat) :=
  match l with
  | nil => false
  | (cons y l) => if eq_nat x y then true else mem x l
  end.

Definition is_free_in (x : nat) (e : term) : bool := 
  let fix aux (e : term) (env : list nat) : bool :=
    match e with
    | Var y => eq_nat x y
    | Abs y t body => if eq_nat x y then false else aux body (cons y env)
    | App fe xe => aux fe env || aux xe env  
    | Const _ => false
    end in
  aux e nil.

Definition free_vars (e : term) : list nat :=
  let fix aux (e : term) (env : list nat) : list nat :=
    match e with
    | Var y => if mem y env then nil else cons y nil
    | Abs y t body => aux body (cons y env)
    | App fe xe => aux fe env ++ aux xe env
    | Const _ => nil
    end in
  aux e nil.

Definition new_var (l : list nat) : nat := S (list_max l).

Fixpoint subst (x : nat) (v e : term) : term :=
  match e with
  | Var y => if eq_nat x y then v else Var y
  | Abs y t body => if eq_nat x y then Abs y t body else
                    if is_free_in y v then
                      let y' := new_var (y :: free_vars v) in
                      Abs y' t (subst y (Var y') body)
                    else Abs y t (subst x v body)
  | App fe xe => App (subst x v fe) (subst x v xe)
  | Const n => Const n
  end.

Inductive bigstep : term -> term -> Prop :=
| big_abs : forall x t e, bigstep (Abs x t e) (Abs x t e)
| big_app : forall e1 e2 x t body v v',
  bigstep e1 (Abs x t body) ->
  bigstep e2 v ->
  bigstep (subst x v body) v' ->
  bigstep (App e1 e2) v'
| big_app2 e1 v1 e2 : bigstep e1 v1 -> bigstep (App e1 e2) v1
| big_const : forall n, bigstep (Const n) (Const n)
.

Inductive smallstep : term -> term -> Prop :=
| small_app1 : forall e1 e1' e2,
  smallstep e1 e1' ->
  smallstep (App e1 e2) (App e1' e2)
| small_app2 : forall v e2 e2',
  value v ->
  smallstep e2 e2' ->
  smallstep (App v e2) (App v e2')
| small_app_abs : forall x t body v,
  value v ->
  smallstep (App (Abs x t body) v) (subst x v body).

Inductive bind_typ : list (nat * typ) -> nat -> typ -> Prop :=
| bind_here : forall env v t, bind_typ ((v,t) :: env) v t 
| bind_later : forall env v t v' t', v <> v' -> bind_typ env v t -> bind_typ ((v',t') :: env) v t 
.

Inductive typing : list (nat * typ) -> term -> typ -> Prop :=
| typ_var : forall x ty g, bind_typ g x ty ->
                         typing g (Var x) ty
| typ_abs : forall x t body tbody g, typing ((x,t) :: g) body tbody ->
                                   typing g (Abs x t body) (TArrow t tbody)
| typ_app : forall fe xe tfrom tto g, typing g fe (TArrow tfrom tto) ->
                                    typing g xe tfrom ->
                                    typing g (App fe xe) tto
| typ_const : forall n g, typing g (Const n) TNat
.

From QuickChick Require Import QuickChick.

QuickChickDebug Debug On.

Instance DecEq_typ : Dec_Eq typ. dec_eq. Defined.
Instance DeqEq_term : Dec_Eq term. dec_eq. Defined.
Derive Show for typ.
Derive Show for term.

Theorem bigstep_deterministic : forall e v1 v2,
  bigstep e v1 -> bigstep e v2 -> v1 = v2.
Proof.
  quickchick.
 (* QuickChick (sized (fun n => theorem (n + 2))).*)
  theorem_dependencies.
  Derive Used Inds smallstep.
  Derive Used Inds typing.
  Derive Density typing derive "Gen".
  Abort.

  
Theorem preservation : forall g e e' t, typing g e t -> bigstep e e' -> typing g e' t.
Proof.
  quickchick.

Theorem typ_abs' :  forall g x t body tbody, typing ((x,t) :: g) body tbody ->
                                             typing g (Abs x t body) (TArrow t tbody).
  
  theorem_dependencies.
  QuickChickDebug Debug Off.
  schedules.
  (*valid_schedules.*)
  (*Derive Schedules typing 1  consnum 1.*) Locate eq.
  Derive Valid Schedules eq consnum 0 derive "Check".

  Derive Inductive Schedule Coq.Init.Logic.eq  derive "Check" opt "true". 

  Derive Show for typ. Derive EnumSized for typ.
Print EnumSizedtyp. Locate oneOf_. Print QuickChick.Enumerators. Check @oneOf_.
Compute ((let EnumSizedtyp_Enum :=
   fix rec (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) :=
     match size with
     | @Coq.Init.Datatypes.O =>
         @QuickChick.Producer.oneOf_ _ _ _ (@QuickChick.Enumerators.returnEnum _ (@TNat))
           (@Coq.Init.Datatypes.cons _ (@QuickChick.Enumerators.returnEnum _ (@TNat)) (@Coq.Init.Datatypes.nil _))
     | @Coq.Init.Datatypes.S size' =>
         @QuickChick.Producer.oneOf_ _ _ _ (@QuickChick.Enumerators.returnEnum _ (@TNat))
           (@Coq.Init.Datatypes.cons _ (@QuickChick.Enumerators.returnEnum _ (@TNat))
              (@Coq.Init.Datatypes.cons _
                 (@QuickChick.Enumerators.bindEnum _ _ (@rec init_size size')
                    (fun 't1 =>
                     @QuickChick.Enumerators.bindEnum _ _ (@rec init_size size')
                       (fun 't2 => @QuickChick.Enumerators.returnEnum _ (@TArrow t1 t2)))) (@Coq.Init.Datatypes.nil _)))
     end in
 fun size : Coq.Init.Datatypes.nat => @EnumSizedtyp_Enum size size) 3).
  
  
Sample ((let GenSizedtyp_Gen :=
   fix rec (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) :=
     match size with
     | @Coq.Init.Datatypes.O =>
         @QuickChick.Generators.freq_ _ (@QuickChick.Generators.returnGen _ (@TNat))
           (@Coq.Init.Datatypes.cons _
              (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                 (@QuickChick.Generators.thunkGen _ (fun '_ => @QuickChick.Generators.returnGen _ (@TNat)))) 
              (@Coq.Init.Datatypes.nil _))
     | @Coq.Init.Datatypes.S size' =>
         @QuickChick.Generators.freq_ _ (@QuickChick.Generators.returnGen _ (@TNat))
           (@Coq.Init.Datatypes.cons _
              (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                 (@QuickChick.Generators.thunkGen _ (fun '_ => @QuickChick.Generators.returnGen _ (@TNat))))
              (@Coq.Init.Datatypes.cons _
                 (@Coq.Init.Datatypes.pair _ _ size
                    (@QuickChick.Generators.thunkGen _
                       (fun '_ =>
                        @QuickChick.Generators.bindGen _ _ (@rec init_size size')
                          (fun 't1 =>
                           @QuickChick.Generators.bindGen _ _ (@rec init_size size')
                             (fun 't2 => @QuickChick.Generators.returnGen _ (@TArrow t1 t2)))))) (@Coq.Init.Datatypes.nil _)))
     end in
 fun size : Coq.Init.Datatypes.nat => @GenSizedtyp_Gen size size) 4).
  
Derive Valid Schedules typing 1 consnum 1 derive "Gen".
Abort.
#[global] Instance DecOpt_not {A} `{DecOpt A} : DecOpt (~ A). 
constructor.
intros n.
destruct (A ?? n) eqn: E.
- exact (Some (negb b)).
- exact None.
Defined.

Derive Inductive Schedule bind_typ 2 derive "Gen" opt "true".

Instance DecEq_typ : Dec_Eq typ. 
dec_eq.
Defined. Check @bindOpt. 

Sample ((fix GenSizedSuchThatbind_typ_IIO size :=
   let GenSizedSuchThatbind_typ_IIOGen :=
     fix rec
       (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) (v451_ : @list (@prod (@nat) (@typ))) (v452_ : @nat) :=
       match size with
       | @Coq.Init.Datatypes.O =>
           @QuickChick.Generators.backtrack _
             (@Coq.Init.Datatypes.cons _
                (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                   (@QuickChick.Generators.thunkGen _
                      (fun '_ =>
                       match v451_ with
                       | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v t) env =>
                           match
                             @QuickChick.Decidability.decOpt (@Coq.Init.Logic.eq _ v v452_) _
                               QuickChick.Decidability.checkable_size_limit
                           with
                           | @Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.true) =>
                               @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ t)
                           | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                           end
                       | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                       end))) (@Coq.Init.Datatypes.nil _))
       | @Coq.Init.Datatypes.S size' =>
           @QuickChick.Generators.backtrack _
             (@Coq.Init.Datatypes.cons _
                (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                   (@QuickChick.Generators.thunkGen _
                      (fun '_ =>
                       match v451_ with
                       | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v t) env =>
                           match
                             @QuickChick.Decidability.decOpt (@Coq.Init.Logic.eq _ v v452_) _
                               QuickChick.Decidability.checkable_size_limit
                           with
                           | @Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.true) =>
                               @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ t)
                           | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                           end
                       | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                       end)))
                (@Coq.Init.Datatypes.cons _
                   (@Coq.Init.Datatypes.pair _ _ size
                      (@QuickChick.Generators.thunkGen _
                         (fun '_ =>
                          match v451_ with
                          | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v' t') env =>
                              match
                                @QuickChick.Decidability.negbOpt
                                  (@QuickChick.Decidability.decOpt (@eq (@nat) v452_ v') _ QuickChick.Decidability.checkable_size_limit)
                              with
                              | @Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.true) =>
                                  @QuickChick.Producer.bindOpt _ _ _ _ (@rec init_size size' env v452_)
                                    (fun 'v453_ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ v453_))
                              | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                              end
                          | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                          end))) (@Coq.Init.Datatypes.nil _)))
       end in
    @GenSizedSuchThatbind_typ_IIOGen size size) 1 [(1,TNat);(2,TArrow TNat TNat)] 2

).


Derive Inductive Schedule bind_typ derive "Check" opt "true". Check @pair. Check typ.

Definition check_bind := (let DecOptbind_typ_IIICheck :=
   fix rec
     (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) (v340_ : @list (@prod (@nat) (@typ))) 
     (v341_ : @nat) (v342_ : @typ) :=
     match size with
     | @Coq.Init.Datatypes.O =>
         @QuickChick.Decidability.checker_backtrack
           (@Coq.Init.Datatypes.cons _
              (fun '_ =>
               match v340_ with
               | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v t) env =>
                   @QuickChick.Decidability.andBind
                     (@QuickChick.Decidability.decOpt (@Coq.Init.Logic.eq _ t v342_) _ QuickChick.Decidability.checkable_size_limit)
                     (@QuickChick.Decidability.andBind
                        (@QuickChick.Decidability.decOpt (@Coq.Init.Logic.eq _ v v341_) _ QuickChick.Decidability.checkable_size_limit)
                        (@Coq.Init.Datatypes.Some Coq.Init.Datatypes.bool Coq.Init.Datatypes.true))
               | _ => @Coq.Init.Datatypes.Some _ Coq.Init.Datatypes.false
               end) (@Coq.Init.Datatypes.nil _))
     | @Coq.Init.Datatypes.S size' =>
         @QuickChick.Decidability.checker_backtrack
           (@Coq.Init.Datatypes.cons _
              (fun '_ =>
               match v340_ with
               | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v t) env =>
                   @QuickChick.Decidability.andBind
                     (@QuickChick.Decidability.decOpt (@Coq.Init.Logic.eq _ t v342_) _ QuickChick.Decidability.checkable_size_limit)
                     (@QuickChick.Decidability.andBind
                        (@QuickChick.Decidability.decOpt (@Coq.Init.Logic.eq _ v v341_) _ QuickChick.Decidability.checkable_size_limit)
                        (@Coq.Init.Datatypes.Some Coq.Init.Datatypes.bool Coq.Init.Datatypes.true))
               | _ => @Coq.Init.Datatypes.Some _ Coq.Init.Datatypes.false
               end)
              (@Coq.Init.Datatypes.cons _
                 (fun '_ =>
                  match v340_ with
                  | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v' t') env =>
                      @QuickChick.Decidability.andBind
                        (@QuickChick.Decidability.negbOpt
                           (@QuickChick.Decidability.decOpt (@eq (@nat) v341_ v') _ QuickChick.Decidability.checkable_size_limit))
                        (@QuickChick.Decidability.andBind (@rec init_size size' env v341_ v342_)
                           (@Coq.Init.Datatypes.Some Coq.Init.Datatypes.bool Coq.Init.Datatypes.true))
                  | _ => @Coq.Init.Datatypes.Some _ Coq.Init.Datatypes.false
                  end) (@Coq.Init.Datatypes.nil _)))
     end in
 fun size : Coq.Init.Datatypes.nat => @DecOptbind_typ_IIICheck size size).

Eval cbn in check_bind 0 [(1,TNat)] 1 TNat.

Derive Inductive Schedule bind_typ 2 derive "Gen" opt "true".

Definition gen_bind := ((let GenSizedSuchThatbind_typ_IIOGen :=
   fix rec (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) (v355_ : @list (@prod (@nat) (@typ))) (v356_ : @nat) :=
     match size with
     | @Coq.Init.Datatypes.O =>
         @QuickChick.Generators.backtrack _
           (@Coq.Init.Datatypes.cons _
              (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                 (@QuickChick.Generators.thunkGen _
                    (fun '_ =>
                     match v355_ with
                     | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v t) env =>
                         match
                           @QuickChick.Decidability.decOpt (@Coq.Init.Logic.eq _ v v356_) _ QuickChick.Decidability.checkable_size_limit
                         with
                         | @Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.true) =>
                             @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ t)
                         | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                         end
                     | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                     end))) (@Coq.Init.Datatypes.nil _))
     | @Coq.Init.Datatypes.S size' =>
         @QuickChick.Generators.backtrack _
           (@Coq.Init.Datatypes.cons _
              (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                 (@QuickChick.Generators.thunkGen _
                    (fun '_ =>
                     match v355_ with
                     | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v t) env =>
                         match
                           @QuickChick.Decidability.decOpt (@Coq.Init.Logic.eq _ v v356_) _ QuickChick.Decidability.checkable_size_limit
                         with
                         | @Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.true) =>
                             @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ t)
                         | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                         end
                     | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                     end)))
              (@Coq.Init.Datatypes.cons _
                 (@Coq.Init.Datatypes.pair _ _ size
                    (@QuickChick.Generators.thunkGen _
                       (fun '_ =>
                        match v355_ with
                        | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v' t') env =>
                            match
                              @QuickChick.Decidability.negbOpt
                                (@QuickChick.Decidability.decOpt (@eq (@nat) v356_ v') _ QuickChick.Decidability.checkable_size_limit)
                            with
                            | @Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.true) =>
                                @QuickChick.Producer.bindOpt _ _ _ _ (@rec init_size size' env v356_)
                                  (fun 'v357_ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ v357_))
                            | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                            end
                        | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                        end))) (@Coq.Init.Datatypes.nil _)))
     end in
 fun size : Coq.Init.Datatypes.nat => @GenSizedSuchThatbind_typ_IIOGen size size))
.
Print gen_bind. Search Dec_Eq.



QuickChickDebug Debug Off.

Derive Inductive Schedule typing 1 2  derive "Gen" opt "true".

Print GenSizedSuchThattyping_IOO.

Search GenSizedSuchThat typing.

Derive Show for term.
Derive Show for typ.

Sample (GenSizedSuchThattyping_IOO 3 [(1,TNat)]).

Sample ((((fix GenSizedSuchThattyping_IOO (size : Coq.Init.Datatypes.nat) :=
   match size with
   | @Coq.Init.Datatypes.O =>
       fun v_g307_ : @list (@prod (@nat) (@typ)) => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
   | @Coq.Init.Datatypes.S size =>
       let GenSizedSuchThattyping_IOOGen :=
         fix rec (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) (v_g307_ : @list (@prod (@nat) (@typ))) :=
           match size with
           | @Coq.Init.Datatypes.O =>
               @QuickChick.Generators.backtrack _
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _
                          (fun '_ =>
                           @QuickChick.Producer.bindOpt _ _ _ _ (@GenSizedSuchThatbind_typ_IOO size v_g307_)
                             (fun '(@Coq.Init.Datatypes.pair _ _ x v309_) =>
                              @QuickChick.Generators.returnGen _
                                (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@Var x) v309_))))))
                    (@Coq.Init.Datatypes.cons _
                       (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                          (@QuickChick.Generators.thunkGen _
                             (fun '_ =>
                              @QuickChick.Generators.bindGen _ _ (@GenSizednat_ size)
                                (fun 'n =>
                                 @QuickChick.Generators.returnGen _
                                   (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@Const n) (@TNat)))))))
                       (@Coq.Init.Datatypes.nil _)))
           | @Coq.Init.Datatypes.S size' =>
               @QuickChick.Generators.backtrack _
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _
                          (fun '_ =>
                           @QuickChick.Producer.bindOpt _ _ _ _ (@GenSizedSuchThatbind_typ_IOO size v_g307_)
                             (fun '(@Coq.Init.Datatypes.pair _ _ x v309_) =>
                              @QuickChick.Generators.returnGen _
                                (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@Var x) v309_))))))
                    (@Coq.Init.Datatypes.cons _
                       (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                          (@QuickChick.Generators.thunkGen _
                             (fun '_ =>
                              @QuickChick.Generators.bindGen _ _ (@GenSizednat_ size)
                                (fun 'n =>
                                 @QuickChick.Generators.returnGen _
                                   (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@Const n) (@TNat)))))))
                       (@Coq.Init.Datatypes.cons _
                          (@Coq.Init.Datatypes.pair _ _ size
                             (@QuickChick.Generators.thunkGen _
                                (fun '_ =>
                                 @QuickChick.Generators.bindGen _ _ (@GenSizedtyp_ size)
                                   (fun 't =>
                                    @QuickChick.Generators.bindGen _ _ (@GenSizednat_ size)
                                      (fun 'x =>
                                       @QuickChick.Producer.bindOpt _ _ _ _
                                         (@rec init_size size'
                                            (@Coq.Init.Datatypes.cons (@prod (@nat) (@typ)) (@Coq.Init.Datatypes.pair (@nat) (@typ) x t)
                                               v_g307_))
                                         (fun '(@Coq.Init.Datatypes.pair _ _ body tbody) =>
                                          @QuickChick.Generators.returnGen _
                                            (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@Abs x t body) (@TArrow t tbody)))))))))
                          (@Coq.Init.Datatypes.cons _
                             (@Coq.Init.Datatypes.pair _ _ size
                                (@QuickChick.Generators.thunkGen _
                                   (fun '_ =>
                                    @QuickChick.Generators.bindGen _ _ (@GenSizedtyp_ size)
                                      (fun 'v309_ =>
                                       @QuickChick.Producer.bindOpt _ _ _ _ (@rec init_size size' v_g307_)
                                         (fun '(@Coq.Init.Datatypes.pair _ _ xe tfrom) =>
                                          @QuickChick.Producer.bindOpt _ _ _ _
                                            (@GenSizedSuchThattyping_IOI size v_g307_ (@TArrow tfrom v309_))
                                            (fun 'fe =>
                                             @QuickChick.Generators.returnGen _
                                               (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@App fe xe) v309_))))))))
                             (@Coq.Init.Datatypes.nil _)))))
           end in
       @GenSizedSuchThattyping_IOOGen size size
   end
 with GenSizedSuchThatbind_typ_IOO (size : Coq.Init.Datatypes.nat) :=
   match size with
   | @Coq.Init.Datatypes.O => fun v341_ : @list (@prod (@nat) (@typ)) => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
   | @Coq.Init.Datatypes.S size =>
       let GenSizedSuchThatbind_typ_IOOGen :=
         fix rec (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) (v341_ : @list (@prod (@nat) (@typ))) :=
           match size with
           | @Coq.Init.Datatypes.O =>
               @QuickChick.Generators.backtrack _
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _
                          (fun '_ =>
                           match v341_ with
                           | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v t) env =>
                               @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ v t))
                           | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                           end))) (@Coq.Init.Datatypes.nil _))
           | @Coq.Init.Datatypes.S size' =>
               @QuickChick.Generators.backtrack _
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _
                          (fun '_ =>
                           match v341_ with
                           | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v t) env =>
                               @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ v t))
                           | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                           end)))
                    (@Coq.Init.Datatypes.cons _
                       (@Coq.Init.Datatypes.pair _ _ size
                          (@QuickChick.Generators.thunkGen _
                             (fun '_ =>
                              match v341_ with
                              | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v' t') env =>
                                  match @DecOptTrue_ size with
                                  | @Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.true) =>
                                      @QuickChick.Producer.bindOpt _ _ _ _ (@rec init_size size' env)
                                        (fun '(@Coq.Init.Datatypes.pair _ _ v342_ v343_) =>
                                         match
                                           @QuickChick.Decidability.negbOpt
                                             (@QuickChick.Decidability.decOpt (@eq (@nat) v342_ v') _
                                                QuickChick.Decidability.checkable_size_limit)
                                         with
                                         | @Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.true) =>
                                             @QuickChick.Generators.returnGen _
                                               (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ v342_ v343_))
                                         | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                         end)
                                  | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                  end
                              | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                              end))) (@Coq.Init.Datatypes.nil _)))
           end in
       @GenSizedSuchThatbind_typ_IOOGen size size
   end
 with DecOptTrue_ (size : Coq.Init.Datatypes.nat) :=
   match size with
   | @Coq.Init.Datatypes.O => @Coq.Init.Datatypes.None _
   | @Coq.Init.Datatypes.S size =>
       let DecOptTrue_Check :=
         fix rec (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) :=
           match size with
           | @Coq.Init.Datatypes.O =>
               @QuickChick.Decidability.checker_backtrack
                 (@Coq.Init.Datatypes.cons _ (fun '_ => @Coq.Init.Datatypes.Some Coq.Init.Datatypes.bool Coq.Init.Datatypes.true)
                    (@Coq.Init.Datatypes.nil _))
           | @Coq.Init.Datatypes.S size' =>
               @QuickChick.Decidability.checker_backtrack
                 (@Coq.Init.Datatypes.cons _ (fun '_ => @Coq.Init.Datatypes.Some Coq.Init.Datatypes.bool Coq.Init.Datatypes.true)
                    (@Coq.Init.Datatypes.nil _))
           end in
       @DecOptTrue_Check size size
   end
 with GenSizednat_ (size : Coq.Init.Datatypes.nat) :=
   match size with
   | @Coq.Init.Datatypes.O => @QuickChick.Generators.returnGen _ (@O)
   | @Coq.Init.Datatypes.S size =>
       let GenSizednat_Gen :=
         fix rec (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) :=
           match size with
           | @Coq.Init.Datatypes.O =>
               @QuickChick.Generators.freq_ _ (@QuickChick.Generators.returnGen _ (@O))
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _ (fun '_ => @QuickChick.Generators.returnGen _ (@O))))
                    (@Coq.Init.Datatypes.nil _))
           | @Coq.Init.Datatypes.S size' =>
               @QuickChick.Generators.freq_ _ (@QuickChick.Generators.returnGen _ (@O))
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _ (fun '_ => @QuickChick.Generators.returnGen _ (@O))))
                    (@Coq.Init.Datatypes.cons _
                       (@Coq.Init.Datatypes.pair _ _ size
                          (@QuickChick.Generators.thunkGen _
                             (fun '_ =>
                              @QuickChick.Generators.bindGen _ _ (@rec init_size size')
                                (fun 'mu311_ => @QuickChick.Generators.returnGen _ (@S mu311_))))) (@Coq.Init.Datatypes.nil _)))
           end in
       @GenSizednat_Gen size size
   end
 with GenSizedtyp_ (size : Coq.Init.Datatypes.nat) :=
   match size with
   | @Coq.Init.Datatypes.O => @QuickChick.Generators.returnGen _ (@TNat)
   | @Coq.Init.Datatypes.S size =>
       let GenSizedtyp_Gen :=
         fix rec (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) :=
           match size with
           | @Coq.Init.Datatypes.O =>
               @QuickChick.Generators.freq_ _ (@QuickChick.Generators.returnGen _ (@TNat))
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _ (fun '_ => @QuickChick.Generators.returnGen _ (@TNat))))
                    (@Coq.Init.Datatypes.nil _))
           | @Coq.Init.Datatypes.S size' =>
               @QuickChick.Generators.freq_ _ (@QuickChick.Generators.returnGen _ (@TNat))
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _ (fun '_ => @QuickChick.Generators.returnGen _ (@TNat))))
                    (@Coq.Init.Datatypes.cons _
                       (@Coq.Init.Datatypes.pair _ _ size
                          (@QuickChick.Generators.thunkGen _
                             (fun '_ =>
                              @QuickChick.Generators.bindGen _ _ (@rec init_size size')
                                (fun 't1 =>
                                 @QuickChick.Generators.bindGen _ _ (@rec init_size size')
                                   (fun 't2 => @QuickChick.Generators.returnGen _ (@TArrow t1 t2)))))) (@Coq.Init.Datatypes.nil _)))
           end in
       @GenSizedtyp_Gen size size
   end
 with GenSizedSuchThattyping_IOI (size : Coq.Init.Datatypes.nat) :=
   match size with
   | @Coq.Init.Datatypes.O =>
       fun (v_g477_ : @list (@prod (@nat) (@typ))) (v479_ : @typ) => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
   | @Coq.Init.Datatypes.S size =>
       let GenSizedSuchThattyping_IOIGen :=
         fix rec
           (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) (v_g477_ : @list (@prod (@nat) (@typ))) (v479_ : @typ) :=
           match size with
           | @Coq.Init.Datatypes.O =>
               @QuickChick.Generators.backtrack _
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _
                          (fun '_ =>
                           @QuickChick.Producer.bindOpt _ _ _ _ (@GenSizedSuchThatbind_typ_IOI size v_g477_ v479_)
                             (fun 'x => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@Var x))))))
                    (@Coq.Init.Datatypes.cons _
                       (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                          (@QuickChick.Generators.thunkGen _
                             (fun '_ =>
                              match v479_ with
                              | @TNat =>
                                  @QuickChick.Generators.bindGen _ _ (@GenSizednat_ size)
                                    (fun 'n => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@Const n)))
                              | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                              end))) (@Coq.Init.Datatypes.nil _)))
           | @Coq.Init.Datatypes.S size' =>
               @QuickChick.Generators.backtrack _
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _
                          (fun '_ =>
                           @QuickChick.Producer.bindOpt _ _ _ _ (@GenSizedSuchThatbind_typ_IOI size v_g477_ v479_)
                             (fun 'x => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@Var x))))))
                    (@Coq.Init.Datatypes.cons _
                       (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                          (@QuickChick.Generators.thunkGen _
                             (fun '_ =>
                              match v479_ with
                              | @TNat =>
                                  @QuickChick.Generators.bindGen _ _ (@GenSizednat_ size)
                                    (fun 'n => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@Const n)))
                              | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                              end)))
                       (@Coq.Init.Datatypes.cons _
                          (@Coq.Init.Datatypes.pair _ _ size
                             (@QuickChick.Generators.thunkGen _
                                (fun '_ =>
                                 match v479_ with
                                 | @TArrow t tbody =>
                                     @QuickChick.Generators.bindGen _ _ (@GenSizednat_ size)
                                       (fun 'x =>
                                        @QuickChick.Producer.bindOpt _ _ _ _
                                          (@rec init_size size'
                                             (@Coq.Init.Datatypes.cons (@prod (@nat) (@typ))
                                                (@Coq.Init.Datatypes.pair (@nat) (@typ) x t) v_g477_) tbody)
                                          (fun 'body => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@Abs x t body))))
                                 | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                 end)))
                          (@Coq.Init.Datatypes.cons _
                             (@Coq.Init.Datatypes.pair _ _ size
                                (@QuickChick.Generators.thunkGen _
                                   (fun '_ =>
                                    @QuickChick.Generators.bindGen _ _ (@GenSizedtyp_ size)
                                      (fun 'tfrom =>
                                       @QuickChick.Producer.bindOpt _ _ _ _ (@rec init_size size' v_g477_ (@TArrow tfrom v479_))
                                         (fun 'fe =>
                                          @QuickChick.Producer.bindOpt _ _ _ _ (@rec init_size size' v_g477_ tfrom)
                                            (fun 'xe => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ (@App fe xe))))))))
                             (@Coq.Init.Datatypes.nil _)))))
           end in
       @GenSizedSuchThattyping_IOIGen size size
   end
 with GenSizedSuchThatbind_typ_IOI (size : Coq.Init.Datatypes.nat) :=
   match size with
   | @Coq.Init.Datatypes.O =>
       fun (v321_ : @list (@prod (@nat) (@typ))) (v323_ : @typ) => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
   | @Coq.Init.Datatypes.S size =>
       let GenSizedSuchThatbind_typ_IOIGen :=
         fix rec
           (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) (v321_ : @list (@prod (@nat) (@typ))) (v323_ : @typ) :=
           match size with
           | @Coq.Init.Datatypes.O =>
               @QuickChick.Generators.backtrack _
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _
                          (fun '_ =>
                           match v321_ with
                           | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v t) env =>
                               match
                                 @QuickChick.Decidability.decOpt (@Coq.Init.Logic.eq _ t v323_) _
                                   QuickChick.Decidability.checkable_size_limit
                               with
                               | @Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.true) =>
                                   @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ v)
                               | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                               end
                           | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                           end))) (@Coq.Init.Datatypes.nil _))
           | @Coq.Init.Datatypes.S size' =>
               @QuickChick.Generators.backtrack _
                 (@Coq.Init.Datatypes.cons _
                    (@Coq.Init.Datatypes.pair _ _ Coq.Init.Nat.one
                       (@QuickChick.Generators.thunkGen _
                          (fun '_ =>
                           match v321_ with
                           | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v t) env =>
                               match
                                 @QuickChick.Decidability.decOpt (@Coq.Init.Logic.eq _ t v323_) _
                                   QuickChick.Decidability.checkable_size_limit
                               with
                               | @Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.true) =>
                                   @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ v)
                               | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                               end
                           | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                           end)))
                    (@Coq.Init.Datatypes.cons _
                       (@Coq.Init.Datatypes.pair _ _ size
                          (@QuickChick.Generators.thunkGen _
                             (fun '_ =>
                              match v321_ with
                              | @Coq.Init.Datatypes.cons _ (@Coq.Init.Datatypes.pair _ _ v' t') env =>
                                  match @DecOptTrue_ size with
                                  | @Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.true) =>
                                      @QuickChick.Producer.bindOpt _ _ _ _ (@rec init_size size' env v323_)
                                        (fun 'v322_ =>
                                         match
                                           @QuickChick.Decidability.negbOpt
                                             (@QuickChick.Decidability.decOpt (@eq (@nat) v322_ v') _
                                                QuickChick.Decidability.checkable_size_limit)
                                         with
                                         | @Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.true) =>
                                             @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.Some _ v322_)
                                         | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                         end)
                                  | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                                  end
                              | _ => @QuickChick.Generators.returnGen _ (@Coq.Init.Datatypes.None _)
                              end))) (@Coq.Init.Datatypes.nil _)))
           end in
       @GenSizedSuchThatbind_typ_IOIGen size size
   end
 for
 GenSizedSuchThattyping_IOO)
)
        ) 4 [(1,TNat);(2,TArrow TNat TNat); (3, TNat)]).


Derive Inductive Schedule nat derive "Enum" opt "false".

Eval compute in ((fix EnumSizednat_ (size : Coq.Init.Datatypes.nat) :=
   match size with
   | @Coq.Init.Datatypes.O => @QuickChick.Enumerators.returnEnum _ (@O)
   | @Coq.Init.Datatypes.S size =>
       let EnumSizednat_Enum :=
         fix rec (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) :=
           match size with
           | @Coq.Init.Datatypes.O =>
               @QuickChick.Producer.oneOf_ _ _ _ (@QuickChick.Enumerators.returnEnum _ (@O))
                 (@Coq.Init.Datatypes.cons _ (@QuickChick.Enumerators.returnEnum _ (@O)) (@Coq.Init.Datatypes.nil _))
           | @Coq.Init.Datatypes.S size' =>
               @QuickChick.Producer.oneOf_ _ _ _ (@QuickChick.Enumerators.returnEnum _ (@O))
                 (@Coq.Init.Datatypes.cons _ (@QuickChick.Enumerators.returnEnum _ (@O))
                    (@Coq.Init.Datatypes.cons _
                       (@QuickChick.Enumerators.bindEnum _ _ (@rec init_size size')
                          (fun 'mu818_ => @QuickChick.Enumerators.returnEnum _ (@S mu818_))) (@Coq.Init.Datatypes.nil _)))
           end in
       @EnumSizednat_Enum size size
   end) 3).
