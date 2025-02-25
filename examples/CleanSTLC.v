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
| bv_later : forall env v t v' t', v <> v' -> bind_val env v t -> bind_val ((v',t') :: env) v t 
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

Inductive typing (g : list (nat * typ)) : term -> typ -> Prop :=
| typ_var : forall x ty, bind_typ g x ty -> typing g (Var x) ty
| typ_abs : forall x t body tbody, typing ((x,t) :: g) body tbody -> typing g (Abs x t body) (TArrow t tbody)
| typ_app : forall fe xe tfrom tto, typing g fe (TArrow tfrom tto) -> typing g xe tfrom -> typing g (App fe xe) tto
| typ_const : forall n, typing g (Const n) TNat
.

From QuickChick Require Import QuickChick.

QuickChickDebug Debug On.

Theorem bigstep_deterministic : forall e v1 v2,
  bigstep e v1 -> bigstep e v2 -> v1 = v2.
Proof.
  theorem_dependencies.
  Derive Used Inds smallstep.
  Derive Used Inds typing.
  Derive Density typing.
  Abort. 


Theorem typ_abs' :  forall g x t body tbody, typing ((x,t) :: g) body tbody ->
                                             typing g (Abs x t body) (TArrow t tbody).
  
  theorem_dependencies.
  QuickChickDebug Debug Off.
  schedules.
  valid_schedules.
  Derive Schedules typing 1  consnum 1.
  Derive Valid Schedules typing 1 consnum 2.
  Derive Inductive Schedule typing derive "Check" opt "true". Check @bind.

Check (let EnumSizedSuchThattyping_IOOEnum :=
   fix rec
     (init_size : Coq.Init.Datatypes.nat) (size : Coq.Init.Datatypes.nat) (v_g5142_ : @list (@prod (@nat) (@typ))) 
     (v5143_ : @term) (v5144_ : @typ) :=
     match size with
     | @Coq.Init.Datatypes.O =>
         @QuickChick.Enumerators.enumerate _
           (@Coq.Init.Datatypes.cons _
              (@QuickChick.Producer.bindOpt _ _ _ _
                 (@QuickChick.DependentClasses.enumSizeST _
                    (fun '(@Coq.Init.Datatypes.pair _ _ v5144_ x) => @bind_typ v_g5142_ x v5144_) _ init_size)
                 (fun '(@Coq.Init.Datatypes.pair _ _ v5144_ x) =>
                  @QuickChick.Enumerators.returnEnum _ (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@Var x) v5144_))))
              (@Coq.Init.Datatypes.cons _
                 (@QuickChick.Producer.bindOpt _ _ _ _
                    (@QuickChick.DependentClasses.enumSizeST _
                       (fun '(@Coq.Init.Datatypes.pair _ _ (@Coq.Init.Datatypes.pair _ _ (@Coq.Init.Datatypes.pair _ _ body t) tbody) x)
                        =>
                        @typing (@Coq.Init.Datatypes.cons (@prod (@nat) (@typ)) (@Coq.Init.Datatypes.pair (@nat) (@typ) x t) v_g5142_)
                          body tbody) _ init_size)
                    (fun '(@Coq.Init.Datatypes.pair _ _ (@Coq.Init.Datatypes.pair _ _ (@Coq.Init.Datatypes.pair _ _ body t) tbody) x) =>
                     @QuickChick.Enumerators.returnEnum _
                       (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@Abs x t body) (@TArrow t tbody)))))
                 (@Coq.Init.Datatypes.cons _
                    (@QuickChick.Producer.bindOpt _ _ _ _
                       (@QuickChick.DependentClasses.enumSizeST _
                          (fun '(@Coq.Init.Datatypes.pair _ _ fe tfromto) => @typing v_g5142_ fe tfromto) _ init_size)
                       (fun '(@Coq.Init.Datatypes.pair _ _ fe tfromto) =>
                        @QuickChick.Producer.bindOpt _ _ _ _
                          (@QuickChick.DependentClasses.enumSizeST _
                             (fun '(@Coq.Init.Datatypes.pair _ _ tfrom xe) => @typing v_g5142_ xe tfrom) _ init_size)
                          (fun '(@Coq.Init.Datatypes.pair _ _ tfrom xe) =>
                           @QuickChick.Enumerators.bindEnum _ _ (@QuickChick.Classes.enumSized (@typ) _ init_size)
                             (fun 'v5144_ =>
                              @QuickChick.Enumerators.returnEnum _
                                (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@App fe xe) v5144_))))))
                    (@Coq.Init.Datatypes.cons _
                       (@QuickChick.Enumerators.bindEnum _ _ (@QuickChick.Classes.enumSized (@nat) _ init_size)
                          (fun 'n =>
                           @QuickChick.Enumerators.returnEnum _
                             (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@Const n) (@TNat)))))
                       (@Coq.Init.Datatypes.nil _)))))
     | @Coq.Init.Datatypes.S size' =>
         @QuickChick.Enumerators.enumerate _
           (@Coq.Init.Datatypes.cons _
              (@QuickChick.Producer.bindOpt _ _ _ _
                 (@QuickChick.DependentClasses.enumSizeST _
                    (fun '(@Coq.Init.Datatypes.pair _ _ v5144_ x) => @bind_typ v_g5142_ x v5144_) _ init_size)
                 (fun '(@Coq.Init.Datatypes.pair _ _ v5144_ x) =>
                  @QuickChick.Enumerators.returnEnum _ (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@Var x) v5144_))))
              (@Coq.Init.Datatypes.cons _
                 (@QuickChick.Producer.bindOpt _ _ _ _
                    (@QuickChick.DependentClasses.enumSizeST _
                       (fun '(@Coq.Init.Datatypes.pair _ _ (@Coq.Init.Datatypes.pair _ _ (@Coq.Init.Datatypes.pair _ _ body t) tbody) x)
                        =>
                        @typing (@Coq.Init.Datatypes.cons (@prod (@nat) (@typ)) (@Coq.Init.Datatypes.pair (@nat) (@typ) x t) v_g5142_)
                          body tbody) _ init_size)
                    (fun '(@Coq.Init.Datatypes.pair _ _ (@Coq.Init.Datatypes.pair _ _ (@Coq.Init.Datatypes.pair _ _ body t) tbody) x) =>
                     @QuickChick.Enumerators.returnEnum _
                       (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@Abs x t body) (@TArrow t tbody)))))
                 (@Coq.Init.Datatypes.cons _
                    (@QuickChick.Producer.bindOpt _ _ _ _
                       (@QuickChick.DependentClasses.enumSizeST _
                          (fun '(@Coq.Init.Datatypes.pair _ _ fe tfromto) => @typing v_g5142_ fe tfromto) _ init_size)
                       (fun '(@Coq.Init.Datatypes.pair _ _ fe tfromto) =>
                        @QuickChick.Producer.bindOpt _ _ _ _
                          (@QuickChick.DependentClasses.enumSizeST _
                             (fun '(@Coq.Init.Datatypes.pair _ _ tfrom xe) => @typing v_g5142_ xe tfrom) _ init_size)
                          (fun '(@Coq.Init.Datatypes.pair _ _ tfrom xe) =>
                           @QuickChick.Enumerators.bindEnum _ _ (@QuickChick.Classes.enumSized (@typ) _ init_size)
                             (fun 'v5144_ =>
                              @QuickChick.Enumerators.returnEnum _
                                (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@App fe xe) v5144_))))))
                    (@Coq.Init.Datatypes.cons _
                       (@QuickChick.Enumerators.bindEnum _ _ (@QuickChick.Classes.enumSized (@nat) _ init_size)
                          (fun 'n =>
                           @QuickChick.Enumerators.returnEnum _
                             (@Coq.Init.Datatypes.Some _ (@Coq.Init.Datatypes.pair _ _ (@Const n) (@TNat)))))
                       (@Coq.Init.Datatypes.nil _)))))
     end in
 fun size : Coq.Init.Datatypes.nat => @EnumSizedSuchThattyping_IOOEnum size size).
