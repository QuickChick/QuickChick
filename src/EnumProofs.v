Require Import String micromega.Lia List.

Require Import Tactics TacticsUtil Instances Classes DependentClasses Sets
        Producer Enumerators Checker Decidability CheckerProofs.

Import ListNotations.

From Ltac2 Require Import Ltac2.

Set Warnings "-notation-overwritten, -parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Local Open Scope set_scope.

Set Bullet Behavior "Strict Subproofs".

Section Lemmas. 

  Lemma semProdSizeOpt_bicupNone A s (S : set A) :
    \bigcup_(x in [:: returnEnum (@None A)]) semProdSizeOpt x s \subset S.
  Proof.
    intros x Hin. inv Hin. inv H. inv H0.
    - inv H1. congruence.
      inv H.
    - inv H.
  Qed.

  Lemma list_subset_cons {A} (h : A) (t : seq A) (s : set A)  :
    s h ->
    t \subset s ->
    (h :: t) \subset s.
  Proof.
    intros H1 H2 x Hin. inv Hin; eauto.
  Qed.

  Lemma list_subset_nil {A} (s : set A)  :
    [::] \subset s.
  Proof. intros x Hin. inv Hin. Qed.


  Lemma exists_oneOf_hd A (x : A) g' (g : nat -> E A) (l : nat -> seq (E A)) :
    (exists s : nat, semProd (g s) x) ->
    exists s : nat, semProd (oneOf_ g' ((g s) :: (l s))) x.
  Proof.
    intros Hin. inv Hin.
    eexists. eapply semOneof. now eauto with typeclass_instances.
    eexists. split; eauto. now left. 
  Qed.

  Lemma exists_oneOf_tl A (x : A) g' (g : nat -> E A) (l : nat -> seq (E A)) :
    (exists s : nat, match l s with
                     | nil => False
                     | g1 :: gs => semProd (oneOf_ g' (g1 :: gs)) x
                     end) ->
    exists s : nat, semProd (oneOf_ g' ((g s) :: (l s))) x.
  Proof.
    intros Hin. inv Hin.
    eexists. eapply semOneof. 
    now eauto with typeclass_instances.
    destruct (l x0)  eqn:Heq.
    - exfalso; eauto.
    - eapply semOneof in H > [ | now eauto with typeclass_instances ].
      rewrite Heq. inv H. destruct H0. eexists. split > [ | eassumption ].
      now right; eauto.
  Qed.

  Lemma exists_bind A B (x : A) (g : E B) (f : nat -> B -> E A) :
    Correct B g ->
    SizeMonotonic g ->
    (forall a s, SizeMonotonic (f a s)) ->

    (exists z s, semProd (f s z) x) ->  
    exists s : nat, semProd (bindEnum g (f s)) x.
  Proof.
    intros Hc Hs1 Hs2 He. inv He. inv H. inv H0.
    inv H.
    assert (Hin : [set : B] x0) by reflexivity.
    eapply Hc in Hin. inv Hin. inv H.
    exists x1, (Nat.max x2 x3). split. reflexivity.
    eapply (@semBindSize E ProducerEnum _ B A).
    eexists. split.

    eapply Hs1 > [ | eassumption ]. now ssromega.
    eapply Hs2 > [ | eassumption ]. now ssromega.
  Qed.

  Lemma exists_return A (x : A) :
    exists s : nat, semProd (returnEnum x) x.
  Proof.
    exists 0. eapply (@semReturn E _ ProducerSemanticsEnum); reflexivity.
  Qed.

  Lemma exists_bind_Sized_alt A B
        (g : nat -> E B) (f : B -> nat -> E A)
        (x : A) (z : B) (s' : nat) :
    SizedMonotonic g ->
    (forall s, SizeMonotonic (g s)) ->

    (forall a, SizedMonotonic (f a)) ->
    (forall a s, SizeMonotonic (f a s)) ->

    semProd (g s') z ->
    (exists s, semProd (f z s) x) ->  
    exists s : nat, semProd (bindEnum (g s) (fun x => f x s)) x.
  Proof.
    intros Hs Hs' Hsf Hsf' Hprod Hex. inv Hex. inv Hprod.
    inv H. destruct H0.
    exists (Nat.max s' x0). inv H1.
    exists (Nat.max x1 x2).
    
    split. reflexivity.
    
    eapply (@semBindSize E ProducerEnum _ B A).

    eexists. split.
    eapply Hs > [ | eapply Hs' > [ | eassumption ] ]. ssromega. ssromega.

    eapply Hsf > [ | eapply Hsf' > [ | eassumption ] ]. ssromega. ssromega.
  Qed.

  Lemma semProd_mon {A} (g : nat -> E A) {_ : SizedMonotonic g} :
    forall s1 s2,
      (s1 <= s2)%coq_nat -> 
      semProd (g s1) \subset semProd (g s2).
  Proof.
    intros s1 s2 Hleq.
    intros x Hin. inv Hin. inv H0.
    eexists x0. split; eauto.
    eapply H > [ | eassumption ].
    destruct (leqP s1 s2); eauto.
  Qed.

  
  Lemma exists_enum_hd A (g : nat -> E (option A)) (gs : nat -> list (E (option A))) x : 
    (exists s, semProdOpt (g s) x) ->
    exists s, semProdOpt (enumerate (g s :: gs s)) x.
  Proof.
    intros [s He].
    exists s.
    eapply (@enumerate_correct_opt A).
    eexists. split. now left. eassumption.
  Qed.

  Lemma exists_enum_tl A (g : nat -> E (option A)) (gs : nat -> list (E (option A))) x : 
    (exists s, semProdOpt (enumerate (gs s)) x) ->
    exists s, semProdOpt (enumerate (g s :: gs s)) x.
  Proof.
    intros [s He].
    exists s.
    eapply (@enumerate_correct_opt A).
    eapply (@enumerate_correct_opt A) in He. destruct He as [z [Hin Hsem]].
    eexists. split. now right; eauto. eassumption.
  Qed.


  Lemma exists_bind_Opt A B (x : A) (g : E B) (f : B -> nat -> E (option A)) z :
    Correct B g ->
    SizeMonotonic g ->
    (forall a s, SizeMonotonicOpt (f a s)) ->

    (exists s, semProdOpt (f z s) x) ->  
    exists s : nat, semProdOpt (bindEnum g (fun x => f x s)) x.
  Proof.
    intros Hc Hs1 Hs2 He. inv He. inv H. inv H0.
    inv H.
    assert (Hin : [set : B] z) by reflexivity.
    eapply Hc in Hin. inv Hin. inv H.
    exists x0, (Nat.max x1 x2). split. reflexivity.
    eapply (@semBindSize E ProducerEnum _ B).
    eexists. split.

    eapply Hs1 > [ | eassumption ]. now ssromega.
    eapply Hs2 > [ | eassumption ]. now ssromega.
  Qed.

  Lemma exists_return_Opt A (x : A) :
    exists s : nat, semProdOpt (returnEnum (Some x)) x.
  Proof.
    exists 0. eapply (@semReturn E _ ProducerSemanticsEnum); reflexivity.
  Qed.

  Lemma exists_bindOpt_Opt A B (x : A) (g : E (option B)) (f : B -> nat -> E (option A)) z :
    SizeMonotonicOpt g ->
    (forall a s, SizeMonotonicOpt (f a s)) ->

    semProdOpt g z ->
    (exists s, semProdOpt (f z s) x) ->  
    exists s : nat, semProdOpt (bindOpt g (fun x => f x s)) x.
  Proof.
    intros Hc Hs1 Hs2 He. destruct He as [s1 He].
    exists s1.
    eapply (@semOptBindOpt E _ _ B); eauto with typeclass_instances.

    eexists. split; eassumption.
  Qed.

  Lemma exists_bindOpt_Opt_Sized A B (x : A) (g : nat -> E (option B)) (f : B -> nat -> E (option A)) z :
    SizedMonotonicOpt g ->
    (forall s, SizeMonotonicOpt (g s)) ->

    (forall a, SizedMonotonicOpt (f a)) ->
    (forall a s, SizeMonotonicOpt (f a s)) ->

    (exists s, semProdOpt (g s) z) ->
    (exists s, semProdOpt (f z s) x) ->  
    exists s : nat, semProdOpt (bindOpt (g s) (fun z => f z s)) x.
  Proof.
    intros Hs1 Hs1' Hs2 Hs2' Hg Hf. destruct Hg as [s1 He].
    destruct Hf.
    exists (max x0 s1).
    eapply (@semOptBindOpt E _ _ B); eauto with typeclass_instances.
    inv He. inv H. inv H0. inv H1. 
    eexists. split. 
    eexists. split. reflexivity.
    eapply Hs1 > [ | eassumption ]. ssromega.
    eexists. split. reflexivity.
    eapply Hs2 > [ | eassumption ]. ssromega.  
  Qed.

  Lemma exists_match_DecOpt {B} P {_ : DecOpt P} (k : nat -> E (option B)) z :
    DecOptSizeMonotonic P ->
    DecOptCompletePos P -> 
    SizedMonotonicOpt k ->
    P ->
    (exists s, semProdOpt (k s) z) ->
    exists (s : nat),
      semProdOpt (match decOpt s.+1 with
                  | Some true => k s
                  | Some false => failEnum
                  | None => returnEnum None
                  end) z.
  Proof.
    intros Hmon Hcom Hmonk Hp [s1 [s [_ He]]].
    eapply Hcom in Hp. destruct Hp as [s2 Hdec].
    eexists (max s1 s2).
    eapply Hmon in Hdec. rewrite Hdec.

    eexists. split. reflexivity. eapply Hmonk > [ | eassumption ].
    ssromega. ssromega.
  Qed.

  Lemma exists_match_DecOpt_neg {B} P {_ : DecOpt P} (k : nat -> E (option B)) z :
    DecOptSizeMonotonic P ->
    DecOptCompleteNeg P -> 
    SizedMonotonicOpt k ->
    ~ P ->
    (exists s, semProdOpt (k s) z) ->
    exists (s : nat),
      semProdOpt (match decOpt s.+1 with
                  | Some false => k s
                  | Some true => failEnum
                  | None => returnEnum None
                  end) z.
  Proof.
    intros Hmon Hcom Hmonk Hp [s1 [s [_ He]]].
    eapply Hcom in Hp. destruct Hp as [s2 Hdec].
    eexists (max s1 s2).
    eapply Hmon in Hdec. rewrite Hdec.

    eexists. split. reflexivity. eapply Hmonk > [ | eassumption ].
    ssromega. ssromega.
  Qed.

  Lemma semProdSizeOpt_semProdOpt {A} {G : Type -> Type} {_ : Producer G} (e1 e2 : E (option A)) :
    (forall s, semProdSizeOpt e1 s \subset semProdSizeOpt e2 s) ->
    semProdOpt e1 \subset semProdOpt e2.
  Proof.
    intros H x Hin. inv Hin. inv H0. eexists. split; eauto. eapply H. eassumption.
  Qed. 


  Global Instance SizeMonotonicOpt_failEnum A :
    @SizeMonotonicOpt A E _ failEnum.
  Proof.
    intros s1 s2 Hleq.
    eapply subset_refl.
  Qed.

  Lemma semProdOpt_failEnum A :
    semProdOpt failEnum <--> (@set0 A). 
  Proof.
    intro x; split; intros H1.
    inv H1. inv H. now inv H1.
    now inv H1. 
  Qed.

  Lemma semProdOpt_return_None {A} :
    semProdOpt (returnEnum None) <--> (@set0 A).
  Proof.
    intro x; split; intro H; inv H.
    inv H0. inv H1. congruence. inv H0.
  Qed.

  Lemma SizeMonotonicOptFP_proof A (g : nat -> E (option A)) :
    (forall s s1 s2,
        (s1 <= s2)%coq_nat ->
        (* monotonic Opt *) 
        (semProdSizeOpt (g s1) s \subset semProdSizeOpt (g s2) s) /\
        (* sizeFP *)
        (~ semProdSize (g s1) s None ->
         semProdSize (g s1) s <--> semProdSize (g s2) s) /\
        (* Antimonotonic None *) 
        (isNone :&: semProdSize (g s2) s \subset isNone :&: semProdSize (g s1) s)) ->
    SizedMonotonicOptFP g.
  Proof.
    intros H. constructor.
    intro; intros. eapply H; eauto. 
    intro; intros. eapply H; eauto. 
    intro; intros. eapply H; eauto. 
  Qed.

End Lemmas.

Ltac2 guarded_subset_refl (_ : unit) :=
  match! goal with
  | [ |- ?s \subset ?s ] => now eapply subset_refl
  end.

(** ** Enum **)

Ltac2 simpl_minus_enumSized (_ : unit) :=
  ltac1:(with_strategy opaque [enumSized] simplstar).

Ltac2 simpl_enumSized (_ : unit) :=
  unfold enumSized; simpl_minus_enumSized (). 


Ltac2 find_size_mon_inst (_ : unit) :=
  first [ tci
        | eapply sizedSizeMonotonicOpt; tci
        | eapply sizedSizeMonotonic; tci ].

(*** Sized Monotonicity *)

Ltac2 rec enum_sized_mon (ih : ident) :=
  first
    [ (* ret *)
      guarded_subset_refl ()
    | (* bind *)
    eapply (@semBindSize_subset_compat _ _ ProducerSemanticsEnum) >
    [ let x := Fresh.in_goal (id_of_string "x") in
      intros $x;
    first
      [ now eapply subset_refl (* for calls to enum *)
      | let ih' := Control.hyp ih in (* for recursive calls *)
        eapply $ih'; now ssromega ]
    | let x := Fresh.in_goal (id_of_string "x") in
      let s := Fresh.in_goal (id_of_string "s") in
      intros $x $s; enum_sized_mon ih
    ]
    ].

Ltac2 rec find_enum (_ : unit) :=
  first
    [ now eapply incl_bigcup_list_nil
    | eapply incl_bigcup_compat_list > [ now eapply subset_refl  | find_enum () ]
    | eapply incl_bigcup_list_hd; now eapply subset_refl
    | eapply incl_bigcup_list_tl; find_enum ()
    ].


Ltac2 base_case_size_mon (_ : unit) :=
  destruct s2 > 
  [ guarded_subset_refl () | simpl_enumSized (); first [ guarded_subset_refl ()
                                                       | rewrite !&Hone; now find_enum () ] ]. 


Ltac2 rec enums_sized_mon (ih : ident) :=
  first
    [ now eapply incl_bigcup_list_nil
    | eapply incl_bigcup_compat_list > [ now enum_sized_mon @IHs1 | enums_sized_mon ih ] ].

Ltac2 ind_case_sized_mon (_ : unit) :=
  destruct s2 > 
  [ now ssromega | simpl_enumSized (); first [ now enum_sized_mon @IHs1
                                             | rewrite !&Hone; now enums_sized_mon @IHs1 ] ]. 


Ltac2 derive_enum_SizedMonotonic (_ : unit) :=
    assert (Hone := @semOneofSize E _ ProducerSemanticsEnum);
    
    match! goal with
    | [ |- @SizedMonotonic ?t _ _ (@enumSized _ ?inst) ] =>
      (intros s s1; revert s; induction s1 as [| s1 IHs1 ];
      intros s s2 Hleq) > [ now base_case_size_mon () | now ind_case_sized_mon () ]
    end. 


(*** Size monotonicity *) 

Ltac2 rec enum_size_mon (ih : ident) :=
  first
    [ (* ret *)
      eapply returnGenSizeMonotonic; tci
    | (* bind *)
      eapply bindMonotonic >
      [ tci
      | first
          [ now find_size_mon_inst ()  (* for calls to enum *)
          | let ih' := Control.hyp ih in (* for recursive calls *)
            eapply $ih'; now ssromega ]
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; enum_size_mon ih
      ]
    ].

Ltac2 rec enums_size_mon (t : constr) (ih : ident) :=
  first
    [ now eapply (@list_subset_nil (E $t))
    | eapply (@list_subset_cons (E $t)) > 
      [ now enum_size_mon ih
      | enums_size_mon t ih ] ]. 

Ltac2 derive_enum_SizeMonotonic (_ : unit) :=
  intros s;
    match! goal with
    | [ |- @SizeMonotonic ?t _ _ _ ] =>
      induction s as [ | s IHs ];
        simpl_enumSized ();
        first [ eapply oneofMonotonic >  
                [ tci
                | now enum_size_mon @IHs
                | now enums_size_mon t @IHs ]
              | now enum_size_mon @IHs ]
    end.

(*** Correct *) 

Ltac2 find_corr_inst (_ : unit) :=
  first [ tci
        | match! goal with
          | [ |- Correct ?ty (sizedEnum enumSized) ] =>
            eapply (@EnumCorrectOfSized $ty _) >
            [ tci
            | now find_size_mon_inst ()
            | tci ]
          end ].

Ltac2 solve_sized_mon (hs : ident) :=
  (* let t := Fresh.in_goal (id_of_string "t") in *)
  (* let s := Fresh.in_goal (id_of_string "s") in *)
  (* let s1 := Fresh.in_goal (id_of_string "s1") in *)
  (* let s2 := Fresh.in_goal (id_of_string "s2") in *)
  (* let hleq := Fresh.in_goal (id_of_string "Hleq") in *)
  intros ? ? ? ? ?; now enum_sized_mon hs.      

Ltac2 solve_size_mon (hs : ident) :=
  intros ? ?; now enum_size_mon hs.      

Ltac2 if_exists tac :=
  match! goal with
  | [|- exists s, semProd _ _ ] => tac
  end.

Ltac2 rec enum_size_correct (_ : unit) :=
  first
    [ (* return *)
      now eapply exists_return; eauto
                                  
    | (* bind non rec *)
      match! goal with
      |  [ |- exists _ : nat, semProd (bindEnum (* enum *) _ _) _ ] => 
         eapply exists_bind > [ now find_corr_inst ()
                              | now find_size_mon_inst ()
                              | now solve_size_mon @Hsize
                              | now eexists; enum_size_correct () ]
      end
    | (* bind rec *)
      match! goal with
      | [|- exists z, semProd (bindEnum (&_aux_enum z) _) _  ] =>
        eapply exists_bind_Sized_alt >
        [ tci
        | now find_size_mon_inst ()
        | now solve_sized_mon @Hsized
        | now solve_size_mon @Hsize
        |
        | now enum_size_correct () ]; eassumption
      end
    ]. 

Ltac2 destructIH (_ : unit) :=
  match! goal with
  | [ h : (exists s, semProd _ _) |- _ ] =>
    let h' := Control.hyp h in destruct $h'
  end.


Ltac2 rec try_solve_correct (_ : unit) :=
  first
    [ eapply exists_oneOf_hd; now enum_size_correct ()
    | eapply exists_oneOf_tl; try_solve_correct ()
    ].

Ltac2 derive_enum_Correct (_ : unit) := 
  match! goal with
  | [ |- @CorrectSized ?typ _ _ ?en ] =>  
    simpl_enumSized ();
    match! goal with
    | [ |- @CorrectSized _ _ _ [eta ?en_simpl] ] =>
      (* get the enum body *)
      set (_aux_enum := ltac2:(exact $en_simpl));
      let hsize := Fresh.in_goal (id_of_string "Hsize") in
      let hsized := Fresh.in_goal (id_of_string "Hsized") in
      let ind := Fresh.in_goal (id_of_string "t") in
      (* Derive monotonicity instances *)
      assert ($hsized : SizedMonotonic $en) > [ tci | ];
      assert ($hsize : forall s, SizeMonotonic ($en s)) > [ tci | ];
      econstructor; intro $ind; split > [ intro; exact I | intros _ ];
      let ind' := Control.hyp ind in
      induction $ind'; eapply exists_Sn; repeat (destructIH ()); simpl_enumSized ();
      first [ enum_size_correct () | try_solve_correct () ]
    end
  end.


(** ** EnumST **) 


Ltac2 simpl_minus_enumSizeST (_ : unit) :=
  ltac1:(with_strategy opaque [enumSizeST enum decOpt enumSizeST] simplstar).

Ltac2 simpl_enumSizeST (_ : unit) :=
  unfold enumSizeST; simpl_minus_enumSizeST (). 

Ltac2 get_ty (e : constr) :=
  match Constr.Unsafe.kind e with
  | Constr.Unsafe.Lambda b app =>
    match Constr.Unsafe.kind app with
    | Constr.Unsafe.App ty args  => ty
    | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
    end
  | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting a function"))))
  end.

Ltac2 get_args (pred : constr) :=
  match Constr.Unsafe.kind pred with
  | Constr.Unsafe.Lambda b app =>
    match Constr.Unsafe.kind app with
    | Constr.Unsafe.App ty args  =>
      List.filter (fun x =>
                     match Constr.Unsafe.kind x with
                     | Constr.Unsafe.Rel _ => (* the arg we are enumeting *)
                       false
                     | Constr.Unsafe.Var _ => (* other args *) 
                       true
                     | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Internal error : args must be free or bound vars"))))
                     end) (Array.to_list args)
                           
    | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
    end
  | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting a function"))))
  end.

Ltac2 revert_params (pred : constr) :=
  let args := get_args pred in 
  let l := constrs_to_idents args in
  List.iter (fun x => try (revert $x)) l. 

Ltac2 intro_params (pred : constr) :=
  let args := get_args pred in 
  let l := constrs_to_idents args in
  List.iter (fun x => try (intro $x)) (List.rev l).


          
(*** Sized monotonic *) 

Ltac2 rec enumST_sized_mon (ih : ident) :=
  first
    [ (* ret *)
      guarded_subset_refl ()
    | (* dec matching *)
      match! goal with
      | [ |- semProdSizeOpt (match @decOpt ?p ?i ?s1 with _ => _ end) _ \subset
             semProdSizeOpt (match decOpt ?s2 with _ => _ end) _ ] =>
        let hdec := Fresh.in_goal (id_of_string "Hdec") in 
        destruct (@decOpt $p $i $s1) eqn:$hdec >
        [ ((erewrite (@CheckerProofs.mon $p $i _ $s1 $s2) > [ | | first [ eassumption | ssromega ] ]) > [ enumST_sized_mon ih | ssromega ])
        | rewrite (@semReturnSizeOpt_None E _ ProducerSemanticsEnum); now eapply sub0set ]
      end
     | (* input matching *) 
      match! goal with
      | [ |- semProdSizeOpt (match ?p with _ => _ end) _ \subset _ ] =>
        destruct $p; enumST_sized_mon ih
      end
    | (* bindOpt *)
      eapply (@semBindOptSizeOpt_subset_compat E _ ProducerSemanticsEnum) >
      [ first
          [ now eapply subset_refl (* for calls to enum *)
          | let ih' := Control.hyp ih in (* for recursive calls *)
            eapply $ih'; now ssromega ]
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; enumST_sized_mon ih
      ]
    | (* bind *)
      eapply (@semBindSizeOpt_subset_compat E _ ProducerSemanticsEnum) >
      [ now eapply subset_refl 
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; enumST_sized_mon ih
      ]
    | ()
    ].

Ltac2 rec find_enumST (ih : ident) :=
  first
    [ now eapply incl_bigcup_list_nil
    | now eapply semProdSizeOpt_bicupNone
    | eapply incl_bigcup_compat_list > [ (now enumST_sized_mon ih)  | find_enumST ih ]
    | eapply incl_bigcup_list_tl; find_enumST ih
    ].

Ltac2 base_case_st_size_mon (s2 : constr) :=
  destruct $s2 > 
  [ first [ guarded_subset_refl () | rewrite !enumerate_correct_size_opt; find_enumST @dummy ]
  | rewrite !enumerate_correct_size_opt; find_enumST @dummy ]. 

Ltac2 ind_case_st_sized_mon (s2 : constr) (ih : ident) :=
  destruct $s2 > 
  [ now ssromega |  rewrite !enumerate_correct_size_opt; find_enumST ih ]. 

Ltac2 derive_enumST_SizedMonotonic (_ : unit) :=
  match! goal with
  | [ |- SizedMonotonicOpt (@enumSizeST ?typ ?pred ?inst) ] =>
    (* assert (Henum := @enumerate_correct_size $typ); *)
      
    let s := Fresh.in_goal (id_of_string "s") in
    let s1 := Fresh.in_goal (id_of_string "s1") in
    let s2 := Fresh.in_goal (id_of_string "s2") in
    let s1i := Fresh.in_goal (id_of_string "s1i") in
    let s2i := Fresh.in_goal (id_of_string "s2i") in
    let hleq := Fresh.in_goal (id_of_string "Hleq") in
    let hleqi := Fresh.in_goal (id_of_string "Hleqi") in
    let ihs1 := Fresh.in_goal (id_of_string "ihs1") in
    intros $s $s1 $s2 $hleq; simpl_enumSizeST ();
      let hleq' := Control.hyp hleq in
      let s1' := Control.hyp s1 in
      let s2' := Control.hyp s2 in
      assert ($hleqi := $hleq');
      revert $hleqi $hleq;
      generalize $s2' at 1 3; generalize $s1' at 1 3; revert $s $s2; revert_params pred;
        (induction $s1' as [| $s1 $ihs1 ]; intro_params pred; intros $s $s2 $s1i $s2i $hleqi $hleq) >
        [ base_case_st_size_mon s2' | ind_case_st_sized_mon s2' ihs1 ]
  end.


Ltac2 rec enumST_antimon (ih : ident) :=
  first
    [ (* ret *)
      guarded_subset_refl ()
    | (* dec matching *)
      match! goal with
      | [ |- _ :&: semProdSize (match @decOpt _ _ ?s2 with _ => _ end) _ \subset
             _ :&: semProdSize (match  @decOpt ?p ?i ?s1 with _ => _ end) _ ] =>
        let hdec := Fresh.in_goal (id_of_string "Hdec") in
        destruct (@decOpt $p $i $s1) eqn:$hdec > 
        [ (erewrite (@CheckerProofs.mon $p $i _ $s1 $s2) > [ | | first [ eassumption | ssromega ] ]) >
          [ enumST_antimon ih | ssromega ]
        |  now eapply semProdSize_return_None  ]
    end
  | (* input matching *)
    match! goal with
    | [ |- _ :&: semProdSize (match ?p with _ => _ end) _ \subset _ ] =>
      destruct $p; enumST_antimon ih
    end
 | (* bindOpt *)
    eapply semBindOptSize_isNone_subset_compat >
    [ first
        [ intros; now eapply subset_refl (* for calls to enum *)
        | let ih' := Control.hyp ih in (* for recursive calls *)
          eapply $ih'; now ssromega ]
    | first
        [ intros; now eapply subset_refl (* for calls to enum *)
        | let ih' := Control.hyp ih in (* for recursive calls *)
          eapply $ih'; now ssromega ] 
    | let x := Fresh.in_goal (id_of_string "x") in
      intros $x; enumST_antimon ih
    ]
    (* | (* bind *) *)
    (*   eapply (@semBindSizeOpt_subset_compat E _ ProducerSemanticsEnum) > *)
    (*   [ now eapply subset_refl *)
    (*   | let x := Fresh.in_goal (id_of_string "x") in *)
    (*     intros $x; enumST_sized_mon ih *)
    (*   ] *)
 | () ].

Ltac2 rec base_case_antimon (_ : unit) :=
  match! goal with
  | [|- ?s1 :&: ?s2 \subset ?s3 :&: (@bigcup ?t ?u (seq_In (cons _ (cons _ _))) ?g)] =>
    eapply (@incl_bigcup_list_tl_inter $t $u); base_case_antimon ()
   | [|- _ \subset _  :&: (@bigcup ?t ?u (seq_In (cons _ nil)) _)] =>
     eapply semProdSize_bigcup_isNone
end.

Ltac2 rec ind_case_antimon (ih : ident) :=
  match! goal with
  | [|- ?s1 :&: ?s2 \subset ?s3 :&: (@bigcup ?t ?u (@seq_In _ (@nil _)) _)] =>
    now eapply subset_refl
  | [|- ?s1 :&: ?s2 \subset ?s3 :&: (@bigcup ?t ?u _ _)] =>
    eapply (@incl_bigcup_compat_list_inter $t $u) > [ enumST_antimon ih | ind_case_antimon ih ]
  end.

Ltac2 rec base_case_fp (_ : unit) :=
  match! goal with
  | [|- (@bigcup ?t ?u (seq_In (cons _ (cons _ _))) ?g) _] =>
    eapply (@in_bigcup_list_tl $t $u); base_case_fp ()
   | [|- (@bigcup ?t ?u (seq_In (cons _ nil)) _) _] =>
     eapply in_bigcup_list_hd; eapply semReturnSizeEnum; reflexivity
end.

Ltac2 rewrite_eqs (eqs: constr list) :=
  List.iter (fun eq => try (rewrite $eq)) eqs.


Ltac2 rec pick_enum (cnt : int) :=
  if Int.equal cnt 0 then
    (eapply in_bigcup_list_hd)
  else
    (eapply in_bigcup_list_tl; pick_enum (Int.sub cnt 1)).

Ltac2 rec find_none (eqs : constr list) (binds : constr list) :=
  first
    [ (* ret *)
      eapply semReturnSizeEnum; reflexivity
    | (* dec matching *) 
      match! goal with
      | [ |- semEnumSize (match  @decOpt ?p ?i ?s1 with _ => _ end) _ _ ] =>
        rewrite_eqs eqs; simpl_minus_methods (); find_none eqs binds
      end
    (* | (* input matching *) () *)
      (* match! goal with *)
      (* | [ |- _ :&: semProdSize (match ?p with _ => _ end) _ \subset _ ] => *)
      (*   destruct $p; enumST_antimon ih *)
      (* end *)
    | (* bindOpt *)
      first
        [ eapply semProdSize_bindOpt_1; eassumption 
        | eapply semProdSize_bindOpt_2 > [ let h := List.hd binds in eapply $h
                                         | simpl_minus_methods (); find_none eqs (List.tl binds) ] ] 
    | ()
    ].

Ltac2 rec solve_ih_hyp (hnin : constr) (cnt : int) (typ : constr) (eqs : constr list) (binds : constr list) :=
  let hc := Fresh.in_goal (id_of_string "Hc") in intros $hc;
  eapply $hnin; eapply (@enumerate_correct_size' $typ);
  pick_enum cnt; simpl_minus_methods (); find_none eqs binds.

Ltac2 rec enumST_fp (ih : constr) (hnin: constr) (cnt : int) (typ : constr) (eqs : constr list) (binds : constr list) :=
  first
    [ (* ret *)
      reflexivity
    | (* dec matching *)
      match! goal with
      | [ |- semEnumSize (match @decOpt ?p ?i ?s1 with _ => _ end) _ <-->
             semEnumSize (match @decOpt _ _ ?s2 with _ => _ end) _ ] =>
        let hdec := Fresh.in_goal (id_of_string "Hdec") in
        (* destruct decOpt *)
        destruct (@decOpt $p $i $s1) eqn:$hdec (* ; simpl_minus_methods () *) >
        [ (* is Some *)
          (erewrite (@CheckerProofs.mon $p $i _ $s1 $s2) > [ | | first [ eassumption | ssromega ] ]) >
          [ let hdec := Control.hyp hdec in enumST_fp ih hnin cnt typ (hdec :: eqs) binds | ssromega ]
        | (* is None *)
          let hdec := Control.hyp hdec in
          exfalso; eapply $hnin;
          match! goal with
          | [ |- semEnumSize (enumerate ?lst) ?s _ ] =>
            eapply (@enumerate_correct_size' _ $lst $s); pick_enum cnt; find_none (hdec :: eqs) (List.rev binds)
          end        
        ]
      end
    | (* input matching *)
      match! goal with
      | [ |-  semEnumSize (match ?p with _ => _ end) _ <--> _ ] =>
        destruct $p; simpl_minus_methods (); enumST_fp ih hnin cnt typ eqs binds
      end
    | (* bindOpt *)
       (eapply semBindOptSize_subset_compat_eq; simpl_minus_methods ()) >
       [ first [ eapply $ih > [ lia |  lia | solve_ih_hyp hnin cnt typ eqs (List.rev binds) ]
               | reflexivity ]
       | let x := Fresh.in_goal (id_of_string "x") in
         let hin := Fresh.in_goal (id_of_string "Hin") in intros $x $hin;
         let hin := Control.hyp hin in
         enumST_fp ih hnin cnt typ eqs (hin :: binds)
       ]  
    | ()
    ].

Ltac2 rec ind_case_fp (ih : constr) (hnin : constr) (cnt : int) (typ : constr) :=
  match! goal with
  | [|- (@bigcup ?t ?u (seq_In (cons _ _)) ?g) <--> _] =>
    eapply incl_bigcup_compat_list_eq >
    [ simpl_minus_methods (); enumST_fp ih hnin cnt typ [] [] | ind_case_fp ih hnin (Int.add cnt 1) typ ]
  | [|- (@bigcup ?t ?u (seq_In nil)) _ <--> _ ] =>
    reflexivity
  end.

Ltac2 derive_enumST_SizedMonotonicFP (_ : unit) :=
  match! goal with
  | [ |- SizedMonotonicOptFP (@enumSizeST ?typ ?pred ?inst) ] => 
    eapply SizeMonotonicOptFP_proof;
    let s := Fresh.in_goal (id_of_string "s") in
    let s1 := Fresh.in_goal (id_of_string "s1") in
    let s2 := Fresh.in_goal (id_of_string "s2") in
    let s1i := Fresh.in_goal (id_of_string "s1i") in
    let s2i := Fresh.in_goal (id_of_string "s2i") in
    let hleq := Fresh.in_goal (id_of_string "Hleq") in
    let hleqi := Fresh.in_goal (id_of_string "Hleqi") in
    let ihs1 := Fresh.in_goal (id_of_string "ihs1") in
    intros $s $s1 $s2 $hleq; simpl_enumSizeST (); 
    let hleq' := Control.hyp hleq in
    let s1' := Control.hyp s1 in
    let s2' := Control.hyp s2 in 
    assert ($hleqi := $hleq');
    revert $hleqi $hleq;
    generalize $s2' at 1 3 5 7; generalize $s1' at 1 3 5 7 9;
    revert $s $s2; revert_params pred;

    (induction $s1' as [| $s1 $ihs1 ]; intro_params pred; intros $s $s2 $s1i $s2i $hleqi $hleq) >
                      [ (* base cases *)
                        split >
                        [ | split ] >
                          [ (* mon *)
                            now base_case_st_size_mon s2'
                          | (* fp *)
                            let hnin := Fresh.in_goal (id_of_string "hnin") in
                            intros $hnin;
                            first [ destruct $s2'; reflexivity
                                  | exfalso;
                                    let hnin' := Control.hyp hnin in eapply $hnin';
                                    eapply (@enumerate_correct_size' $typ); base_case_fp ()
                                  | let hnin' := Control.hyp hnin in
                                    let dummy := Control.hyp hnin in
                                    (* XXX says not focused when using ; after destruct *)
                                    destruct $s2'>  [ rewrite !enumerate_correct_size';
                                                      ind_case_fp dummy hnin' 0 typ
                                                    | rewrite !enumerate_correct_size';
                                                      ind_case_fp dummy hnin' 0 typ ] ]
                                  (* | () ] *)
                          | (* antimon *)
                            first [ destruct $s2'; now eapply subset_refl
                                  | rewrite !enumerate_correct_size'; now base_case_antimon ()
                                  | destruct $s2' >
                                    [ rewrite !enumerate_correct_size'; ind_case_antimon @dummy | rewrite !enumerate_correct_size'; ind_case_antimon @dummy ]
]
                          ]
                      | (* inuctive cases *)
                        split >
                        [ | split ] >
                          [ (* mon *)
                            ind_case_st_sized_mon s2' ihs1
                          | (* fp *)
                            let hnin := Fresh.in_goal (id_of_string "hnin") in
                            intros $hnin;
                            destruct $s2' >
                            [ lia | let hnin' := Control.hyp hnin in
                                    let ihs1' := Control.hyp ihs1 in
                                    rewrite !enumerate_correct_size'; now ind_case_fp ihs1' hnin' 0 typ ]
                          | (* antimon *)
                            destruct $s2' >
                            [ lia | rewrite !enumerate_correct_size'; ind_case_antimon ihs1 ]
                          ]
                      ]
end.

(* Size Monotonicity *) 
 
Ltac2 rec enumST_size_mon (ih : ident) :=
  first
    [ (* fail *)
      eapply SizeMonotonicOpt_failEnum; tci
    | (* ret *)
      eapply returnGenSizeMonotonicOpt; tci
    | (* bindOpt *)
      eapply bindOptMonotonicOpt >
      [ tci
      | first
          [ (* for calls to enum in params *)
            tci
          | (* for call to existing enum instances. XXX not sure why typeclass resulotion doesn't work *)
            eapply sizedSizeMonotonicOpt; tci 
          | (* for recursive calls *)
             let ih' := Control.hyp ih in 
            eapply $ih' ]
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; enumST_size_mon ih
      ]
    | (* bind *)
      eapply bindMonotonicOpt >
      [ tci
      | first
          [ (* for calls to enum in params *)
            tci 
          | (* for call to existing enum instances. XXX not sure why typeclass resulotion doesn't work *)
            eapply sizedSizeMonotonic; tci 
          | (* for recursive calls *)
             let ih' := Control.hyp ih in 
            eapply $ih' ]
      | let x := Fresh.in_goal (id_of_string "x") in
        intros $x; enumST_size_mon ih
      ]
    | (* input/dec matching *)
      match! goal with
      | [ |- SizeMonotonicOpt (match ?p with _ => _ end) ] =>
        destruct $p; enumST_size_mon ih
      end
    | ()
    ].

Ltac2 rec enumsST_size_mon (ih : ident) (t : constr) :=
  first
    [ now eapply (@list_subset_nil (E (option $t)))
    | eapply (@list_subset_cons (E (option $t))) > 
      [ enumST_size_mon ih
      | enumsST_size_mon ih t ] ]. 


Ltac2 derive_enumST_SizeMonotonic (_ : unit) :=
  let s := Fresh.in_goal (id_of_string "s") in
  let ihs := Fresh.in_goal (id_of_string "Ihs") in
  let si := Fresh.in_goal (id_of_string "si") in
  intro $s;
  let s' := Control.hyp s in 

  match! goal with
  | [ |- SizeMonotonicOpt (@enumSizeST ?typ ?pred ?inst _) ] =>   
    simpl_enumSizeST (); generalize $s' at 1; revert_params pred;
    induction $s' as [ | $s $ihs ]; intro_params pred; intros $si;
    eapply enumerate_SizeMonotonicOpt; enumsST_size_mon @IHs typ
  end.


(* Size Monotonicity + FP *) 

                                                           
Ltac2 rec enumST_size_fp (ih : ident) (typ : constr) :=
  first
    [ (* ret *)
      eapply returnGenSizeFP; tci
    | (* fail *)
      eapply (@SizeFP_failEnum $typ)
    | (* bindOpt.  *)
      match! goal with
       |[|- SizeFP (@bindOpt _ _ ?a ?b _ _) ] =>
        eapply (@bindOptSizeFP $a $b) >
        [ first
            [ tci
            | eapply sizedSizeFP; tci
            | let ih' := Control.hyp ih in
              eapply $ih' ]
        | let x := Fresh.in_goal (id_of_string "x") in
          intros $x; enumST_size_fp ih typ ]
      end
    | (* input/dec matching *)
      match! goal with
      | [ |- SizeFP (match ?p with _ => _ end) ] =>
        destruct $p; enumST_size_fp ih typ
      end
    | ()
    ].

Ltac2 rec enumsST_size_fp (ih : ident) (t : constr) :=
  first
    [ now eapply (@list_subset_nil (E (option $t)))
    | eapply (@list_subset_cons (E (option $t))) > 
      [ enumST_size_fp ih t
      | enumsST_size_fp ih t ] ]. 

Ltac2 derive_enumST_SizeMonotonicFP (_ : unit) :=
  let s := Fresh.in_goal (id_of_string "s") in
  let ihs := Fresh.in_goal (id_of_string "Ihs") in
  let si := Fresh.in_goal (id_of_string "si") in
  intro $s;
  let s' := Control.hyp s in 

  match! goal with
  | [ |- SizeMonotonicOptFP (@enumSizeST ?typ ?pred ?inst _) ] =>   
    simpl_enumSizeST (); generalize $s' at 1; revert_params pred;
    (induction $s' as [ | $s $ihs ]; intro_params pred; intros $si;
    eapply enumerate_SizeMonFP) >
    [ enumsST_size_fp ihs typ | enumsST_size_mon ihs typ
    | enumsST_size_fp ihs typ  | enumsST_size_mon ihs typ ]
  end.

(** Correctness *)


(* TODO duplicate *)

Ltac2 make_prod (bs : constr array) (c : constr) :=
  let bs := Array.map (fun b => let t := Constr.type b in
                                Constr.Binder.make (Some (constr_to_ident b)) t) bs in
  
  Array.fold_left (fun t b => Constr.Unsafe.make (Constr.Unsafe.Prod b t)) c bs.


(* To derive monotonicity inside the correctness proof *)



Ltac2 rec enumST_sound (ty : constr) (ih : ident) :=
  match! goal with
  (* match decOpt pos *)
  | [ h : semProdOpt (match @decOpt ?p ?i ?s with _ => _ end) ?x |- _ ] =>
    let hdec := Fresh.in_goal (id_of_string "Hdec") in
    let b := Fresh.in_goal (id_of_string "b") in
    destruct (@decOpt $p $i $s) as [ $b | ] eqn:$hdec > [ | now enumST_sound ty ih (* return None *) ];
    let b' := Control.hyp b in
    destruct $b' > [ | now eapply semProdOpt_failEnum in $h; inv $h ];
    eapply (@CheckerProofs.sound $p) in $hdec > [ | tci ]; enumST_sound ty ih
  (* match decOpt neg *)
  | [ h : semProdOpt (match @decOpt ?p ?i ?s with _ => _ end) ?x |- _ ] =>
    let hdec := Fresh.in_goal (id_of_string "Hdec") in
    let b := Fresh.in_goal (id_of_string "b") in
    destruct (@decOpt $p $i $s) as [ $b | ] eqn:$hdec > [ | now enumST_sound ty ih (* return None *) ];
    let b' := Control.hyp b in
    destruct $b' > [ now eapply semProdOpt_failEnum in $h; inv $h | ];
    eapply (@CheckerProofs.sound_neg $p) in $hdec > [ | tci ]; enumST_sound ty ih
  (* match input *)
  | [ h : semProdOpt (match ?n with _ => _ end) ?x |- _ ] =>
    destruct $n; try (now eapply semProdOpt_failEnum in $h; inv $h); enumST_sound ty ih
  (* return Some *)   
  | [ h : semProdOpt (returnEnum (Some _)) _ |- _ ] =>
    eapply (@semReturnOpt E _ _) in $h; inv $h; first [ now eauto using $ty | now eauto 20 using $ty ]
  (* return None*)   
  | [ h : semProdOpt (returnEnum (@None ?a)) _ |- _ ] =>
    eapply (@semProdOpt_return_None $a) in $h; inv $h
  (* fail *)    
  | [ h : semProdOpt failEnum _ |- _ ] =>
    eapply semProdOpt_failEnum in $h; inv $h 
  (* bindOpt *)    
  | [ h : semProdOpt (bindOpt _ _) _ |- _ ] =>
    eapply (@semOptBindOpt E _ _) in $h >
                                     [ let h' := Control.hyp h in
                                       destruct $h' as [? [$h ?]];
                                       first [ let ih' := Control.hyp ih in eapply $ih' in $h
                                             | match! goal with
                                               | [h : semProdOpt (sizedEnum (@enumSizeST ?t ?pred ?inst)) _ |- _ ] =>
                                                 eapply (@SuchThatCorrectOfBoundedEnum $t $pred $inst) in $h > [ | tci | tci | tci ]
                                               end                     
                                             | match! goal with
                                               | [h : semProdOpt enum _ |- _ ] => clear $h
                                               end ]; enumST_sound ty ih
                                     | find_size_mon_inst ()
                                     | intro; now enumST_size_mon @Hmon ]
  (* bind *)  
  | [ h : semProdOpt (bindEnum _ _) _ |- _ ] =>
    eapply (@semOptBind E _ _) in $h >
                                  [ let h' := Control.hyp h in
                                    destruct $h' as [? [? ?]]; enumST_sound ty ih
                                  | find_size_mon_inst ()
                                  | intro; now enumST_size_mon @Hmon ]

  | [ |- _ ] => ()
  end.

Ltac2 rec sound_enums (ty : constr) (ih : ident) :=
  match! goal with
  | [ h : (\bigcup_(x in (seq_In (_ :: _))) _) _ |- _ ] =>
    eapply in_bigcup_list_cons in $h;
    let h' := Control.hyp h in
    destruct $h' as [ | ] > [ enumST_sound ty ih | sound_enums ty ih  ]
  | [ h : (\bigcup_(x in seq_In Datatypes.nil) _) _ |- _ ] =>
    apply bigcup_nil_set0 in $h; inv $h
  end. 

Ltac2 derive_sound_enumST (ty : constr) (pred : constr) :=
  let s := Fresh.in_goal (id_of_string "s") in
  let si := Fresh.in_goal (id_of_string "si") in
  let ihs := Fresh.in_goal (id_of_string "ihs") in
  let hgen := Fresh.in_goal (id_of_string "Hgen") in
  intros [$s $hgen]; revert $hgen;

  let s' := Control.hyp s in

  match! goal with
    [ |- semProdOpt _ ?x -> _ ] => 
    (generalize $s' at 1; revert_params pred; generalize $x; induction $s' as [ | $s $ihs]; intro;
     intro_params pred;
     intros $si $hgen;
     eapply &Henum in $hgen) > [ sound_enums ty ihs | sound_enums ty ihs  ]
  end.

Definition empty_enum {A} : E (option A) := MkEnum (fun _ => LazyList.lnil).

Ltac2 make_semEnum (t : constr) (enum : constr) (s : constr) :=
  let c := constr:(@semProdSizeOpt E _ ltac2:(exact $t) empty_enum ltac2:(exact $s)) in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App sem sargs => 
    let sargs' := Array.copy sargs in
    let _ := Array.set sargs' 3 enum in
    Constr.Unsafe.make (Constr.Unsafe.App sem sargs')
  | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
  end.


Ltac2 mon_expr (tapp : constr) (inst : constr) :=
  match! goal with
  | [ |- CorrectSizedST _ ?f ] =>
    match Constr.Unsafe.kind f with
    | Constr.Unsafe.Lambda b app =>
      match Constr.Unsafe.kind app with
      | Constr.Unsafe.App aux args =>

        let len := Int.sub (Array.length args) 2 in
        let inps := Array.sub args 2 len in

        let args' (s1 : constr) (s2 : constr) (offs : int) :=
            let ind := Array.mapi (fun i _ => Constr.Unsafe.make (Constr.Unsafe.Rel (Int.add i offs))) inps in
            let a := Array.make 2 s1 in
            Array.set a 1 s2; Array.append a ind
        in

        let aux_app s1 s2 offs := Constr.Unsafe.make (Constr.Unsafe.App aux (args' s1 s2 offs)) in


        (* SizeMonotonic *) 
        let dummy_app s1 s2 :=
            let args' := Array.copy args in
            let _ := Array.set args' 0 s1 in
            let _ := Array.set args' 1 s1 in
            Constr.Unsafe.make (Constr.Unsafe.App aux args')
        in

        let dummy_term := constr:(SizeMonotonicOpt (ltac2:(let t := dummy_app '0 '0 in exact $t))) in

        let make_term s1 s2 :=
            match Constr.Unsafe.kind dummy_term with
            | Constr.Unsafe.App mon margs =>
              let margs' := Array.copy margs in
              Array.set margs' 3 (aux_app s1 s2 1);
              make_prod inps (Constr.Unsafe.make (Constr.Unsafe.App mon margs'))
            | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
            end
        in 
        
        assert (_Hmon : forall (_s1 _s2 : nat), ltac2:(let s1 := Control.hyp @_s1 in
                                                      let s2 := Control.hyp @_s2 in
                                                      let t := make_term s1 s2  in exact $t)) >
        [  let s := Fresh.in_goal (id_of_string "s") in 
           let si := Fresh.in_goal (id_of_string "si") in 
           let ihs := Fresh.in_goal (id_of_string "IHs") in 
           intros $si $s;
           let s' := Control.hyp s in revert $si;
           induction $s' as [ | $s $ihs ]; intros $si;
           Array.iter (fun _ => intro) inps; eapply enumerate_SizeMonotonicOpt; now enumsST_size_mon ihs tapp
        | ];

        (* SizedMonotonic, generalized *)          
        let subset (t1 : constr) (t2 : constr) :=
            let dummy := constr:(set_incl (@set0 (ltac2:(exact $tapp))) set0) in
            match Constr.Unsafe.kind dummy with
            | Constr.Unsafe.App sub sargs =>
              let sargs' := Array.copy sargs in
              let _ := Array.set sargs' 1 t1 in
              let _ := Array.set sargs' 2 t2 in
              Constr.Unsafe.make (Constr.Unsafe.App sub sargs')
            | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
            end
        in
        let mon s1 s2 s1' s2' s :=
            make_prod inps (subset (make_semEnum tapp (aux_app s1' s1 1) s) (make_semEnum tapp (aux_app s2' s2 1) s))
        in
                                                                                             
        assert (_Hmons : forall (s1 s2 s2' s1' s: nat), (s1 <= s2)%coq_nat -> (s1' <= s2')%coq_nat ->
                                                       ltac2:(let s1 := Control.hyp @s1 in
                                                              let s1' := Control.hyp @s1' in
                                                              let s2 := Control.hyp @s2 in
                                                              let s2' := Control.hyp @s2' in
                                                              let s' := Control.hyp @s in
                                                              let t := mon s1 s2 s1' s2' s' in exact $t)) >
        [ let s1 := Fresh.in_goal (id_of_string "s1") in
          let s2 := Fresh.in_goal (id_of_string "s2_") in
          let ihs1 := Fresh.in_goal (id_of_string "ihs1") in
          intros $s1; simpl_enumSizeST ();
          let s1' := Control.hyp s1 in
          (induction $s1' as [| $s1 $ihs1 ]; intros $s2 ? ? ? ? ? ; Array.iter (fun _ => intro) inps) >
          [ let s2' := Control.hyp s2 in EnumProofs.base_case_st_size_mon s2'
          | let s2' := Control.hyp s2 in EnumProofs.ind_case_st_sized_mon s2' ihs1 ]
        | ]
    | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting an application"))))
    end
  | _ => Control.throw (Tactic_failure (Some (Message.of_string ("Expecting a function"))))
  end
end.



Ltac2 destructIH_opt (_ : unit) :=
  match! goal with
  | [ h : (exists s, semProdOpt _ _) |- _ ] =>
    let h' := Control.hyp h in destruct $h' as [ ? $h]; destruct $h' as [? [? $h]]
  end.



(* Ltac2 rec enumST_complete (ty : constr):= *)
(*   let hmons := Control.hyp @_Hmons in *)
(*   first *)
(*     [ (* return *)  *)
(*       now eapply exists_return_Opt *)
(*     | (* match decOpt *) *)
(*       (eapply (@exists_match_DecOpt $ty) > [ | | | | enumST_complete ty ]) >  *)
(*       [ (* decOpt mon *) now eauto with typeclass_instances *)
(*       | (* decOpt complete *) now eauto with typeclass_instances *)
(*       | (* sizedMon *) intros ? ? ? ? ?; now enumST_sized_mon @_Hmons  *)
(*       | (* P *) now eauto ] *)
(*     | (* bindOpt rec call *) *)
(*       (eapply exists_bindOpt_Opt_Sized > [ | | | | | enumST_complete ty ]) > *)
(*       [ (* sizedMon *)  *)
(*         intro; intros; eapply $hmons; ssromega *)
(*       | (* sizeMon *) now find_size_mon_inst () *)
(*       | (* sizedMon *) intros ? ? ? ? ?; now enumST_sized_mon @_Hmons *)
(*       | (* sizeMon *) intros ? ?; now enumST_size_mon @_Hmon *)
(*       | eexists; eexists; split > [ reflexivity *)
(*                                   | eapply $hmons > [ eapply Peano.le_n | | eassumption ]; ssromega ] ] *)
(*     | (* bindOpt sized *) *)
(*       (eapply exists_bindOpt_Opt_Sized > [ | | | | | enumST_complete ty ]) >  *)
(*       [ now eauto with typeclass_instances *)
(*       | intros _; now find_size_mon_inst () *)
(*       | (* sizedMon *) intros ? ? ? ? ?; now enumST_sized_mon @_Hmons *)
(*       | (* sizeMon *) intros ? ?; now enumST_size_mon @_Hmon *)
(*       | match! goal with *)
(*       | [ |- exists _, semProdOpt (sizedEnum (@enumSizeST ?t ?pred ?inst)) _ ] => *)
(*         exists 0; eapply (@size_CorrectST $t $pred E _ _) > [ | | | eassumption ]; *)
(*         now eauto with typeclass_instances *)
(*         end ] *)
(*     | (* bind *) *)
(*       match! goal with *)
(*       |  [ |- exists _ : nat, semProdOpt (bindEnum enum _) _ ] =>  *)
(*          (eapply exists_bind_Opt > [ | | | enumST_complete ty ]) > *)
(*          [ now eauto with typeclass_instances *)
(*          | now find_size_mon_inst () *)
(*          | intros ? ?; now enumST_size_mon @_Hmon ] *)
(*       end *)

(*     | ( ) ].  *)

Ltac2 rec enumST_complete (ty : constr):=
  let hmons := Control.hyp @_Hmons in simpl_minus_methods ();
  first
    [ (* return *)
      subst; now eapply exists_return_Opt
    | (* match decOpt for eq *)
      (eapply (@exists_match_DecOpt $ty) > [ | | | ltac1:(now eapply Logic.eq_refl) | enumST_complete ty ]) >
      [ (* decOpt mon *) tci
      | (* decOpt complete *) tci
      | (* sizedMon *) intros ? ? ? ?; enumST_sized_mon @_Hmons
      | enumST_complete ty ]
    | (* match decOpt *)
      (eapply (@exists_match_DecOpt $ty) > [ | | | | enumST_complete ty ]) >
      [ (* decOpt mon *) tci
      | (* decOpt complete *) tci
      | (* sizedMon *) intros ? ? ? ?; enumST_sized_mon @_Hmons
      | (* P *) now eauto ]
    | (* match decOpt neg *)
      (eapply (@exists_match_DecOpt_neg $ty) > [ | | | | enumST_complete ty ]) >
      [ (* decOpt mon *) tci
      | (* decOpt complete *) tci
      | (* sizedMon *) intros ? ? ? ?; enumST_sized_mon @_Hmons
      | (* ~ P *) now eauto ]
    | (* bindOpt rec call *)
      (eapply exists_bindOpt_Opt_Sized > [ | | | | | now enumST_complete ty ]) >
      [ (* sizedMon *)
        intro; intros; eapply $hmons; ssromega
      | (* sizeMon *) now find_size_mon_inst ()
      | (* sizedMon *) intros ? ? ? ? ?; now enumST_sized_mon @_Hmons
      | (* sizeMon *) intros ? ?; enumST_size_mon @_Hmon
      | eexists; eexists; split > [ reflexivity
                                  | eapply $hmons > [ eapply Peano.le_n | | eassumption ]; ssromega ]
      ]
    | (* bindOpt rec call alt *)
      eapply exists_bindOpt_Opt_Sized >
      [ (* sizedMon *)
        intro; intros; eapply $hmons; ssromega
      | (* sizeMon *) now find_size_mon_inst ()
      | (* sizedMon *) intros ? ? ? ? ?; now enumST_sized_mon @_Hmons
      | (* sizeMon *) intros ? ?; enumST_size_mon @_Hmon
      | eexists; eexists; split > [ reflexivity
                                  | eapply $hmons > [ eapply Peano.le_n | | eassumption ]; ssromega ]
      | now enumST_complete ty ]
    | (* bindOpt sized eq *)
      eapply exists_bindOpt_Opt_Sized >
      [ tci
      | intros _; now find_size_mon_inst ()
      | (* sizedMon *) intros ? ? ? ? ?; now enumST_sized_mon @_Hmons
      | (* sizeMon *) intros ? ?; enumST_size_mon @_Hmon
      | match! goal with
      | [ |- exists _, semProdOpt (sizedEnum (@enumSizeST ?t ?pred ?inst)) _ ] =>
        exists 0; eapply (@size_CorrectST $t $pred E _ _) > [ | | | ltac1:(now eapply Logic.eq_refl) ]; tci
        end
      | now enumST_complete ty
      ]
    | (* bindOpt sized *)
      (eapply exists_bindOpt_Opt_Sized > [ | | | | | now enumST_complete ty ]) >
      [ tci
      | intros _; now find_size_mon_inst ()
      | (* sizedMon *) intros ? ? ? ? ?; now enumST_sized_mon @_Hmons
      | (* sizeMon *) intros ? ?; enumST_size_mon @_Hmon
      | match! goal with
        | [ |- exists _, semProdOpt (sizedEnum (@enumSizeST ?t ?pred ?inst)) _ ] =>
           exists 0; eapply (@size_CorrectST $t $pred E _ _) > [ | | | first [ eassumption | reflexivity ] ]; tci
        end
      ]
    | (* bindOpt sized simple *)
      (eapply exists_bindOpt_Opt_Sized > [ | | | | | now enumST_complete ty ]) >
      [ tci
      | intros _; now find_size_mon_inst ()
      | (* sizedMon *) intros ? ? ? ? ?; now enumST_sized_mon @_Hmons
      | (* sizeMon *) intros ? ?; enumST_size_mon @_Hmon
      | match! goal with
        | [ |- exists _, semProdOpt enum _ ] =>
          exists 0; eapply enumOptCorrect > [ tci | reflexivity ]
        end
      ]
    | (* bindOpt sized alt *)
      eapply exists_bindOpt_Opt_Sized >
      [ tci
      | intros _; now find_size_mon_inst ()
      | (* sizedMon *) intros ? ? ? ? ?; now enumST_sized_mon @_Hmons
      | (* sizeMon *) intros ? ?; enumST_size_mon @_Hmon
      | match! goal with
      | [ |- exists _, semProdOpt (sizedEnum (@enumSizeST ?t ?pred ?inst)) _ ] =>
        exists 0; eapply (@size_CorrectST $t $pred E _ _) > [ | | | first [ eassumption | reflexivity ] ]; tci
        end
      | now enumST_complete ty
      ]
    | (* bind *)
      match! goal with
      | [ |- exists _ : nat, semProdOpt (bindEnum enum _) _ ] =>
         eapply exists_bind_Opt >
         [ tci
         | now find_size_mon_inst ()
         | intros ? ?; enumST_size_mon @_Hmon | now enumST_complete ty ]
           (* LTAC2 feature request branch grouping *)
      | [ |- exists _ : nat, semProdOpt (bindEnum (sizedEnum enumSized) _) _ ] =>
         eapply exists_bind_Opt >
         [ tci
         | now find_size_mon_inst ()
         | intros ? ?; enumST_size_mon @_Hmon | now enumST_complete ty ]
      end
    | ( ) ].


Ltac2 rec try_solve_complete (ty : constr) :=
  first [ eapply exists_enum_hd; now enumST_complete ty 
        | eapply exists_enum_tl; try_solve_complete ty ].

Ltac2 derive_complete_enumST (ty : constr) (inst : constr) := 
  let ind := Fresh.in_goal (id_of_string "ind") in 
  intros $ind; let ind' := Control.hyp ind in induction $ind';
  eapply exists_Sn; repeat (destructIH_opt ()); try_solve_complete ty.


Ltac2 derive_enumST_Correct (_ : unit) := 
  match! goal with
  | [ |- CorrectSizedST _ (@enumSizeST ?tapp ?pred ?inst) ] =>
    assert (Henum := @enumerate_correct_opt $tapp);
      
    simpl_enumSizeST ();

    (* derive monotonicity *) 
    mon_expr tapp inst;

    let ty := get_ty pred in
    let x := Fresh.in_goal (id_of_string "x") in
    split; intros $x; split >
      [ derive_sound_enumST ty pred | derive_complete_enumST tapp inst ]
  end.



(* Ltac tactics *)
Ltac derive_enum_SizeMonotonic := ltac2:(derive_enum_SizeMonotonic ()).
Ltac derive_enum_SizedMonotonic :=  ltac2:(derive_enum_SizedMonotonic ()).
Ltac derive_enum_Correct := ltac2:(derive_enum_Correct ()).


Ltac derive_enumST_SizeMonotonic := ltac2:(derive_enumST_SizeMonotonic ()).
Ltac derive_enumST_SizedMonotonic :=  ltac2:(derive_enumST_SizedMonotonic ()).
Ltac derive_enumST_Correct := ltac2:(derive_enumST_Correct ()).

Ltac derive_enumST_SizeMonotonicFP := ltac2:(derive_enumST_SizeMonotonicFP ()).
Ltac derive_enumST_SizedMonotonicFP :=  ltac2:(derive_enumST_SizedMonotonicFP ()).
