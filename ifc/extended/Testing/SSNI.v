Require Import String.
Require Import Arith.EqNat.
Require Import ZArith.

Require Import QuickChick.

Require Import Common.
Require Import Printing.
Require Import Shrinking.
Require Import Generation.
Require Import Indist.

Open Scope string_scope.

Require Import Show.

Require Import Reachability.


Section Checkers.
  Context {Gen : Type -> Type}
          {H : GenMonad Gen}.

(*  Definition Property := Property Gen. *)


  Definition is_low_state st lab := isLow (pc_lab (st_pc st)) lab.

Set Printing All.

  Definition propSSNI_helper (t : table) (v : Variation) : Property Gen :=
    let '(Var lab st1 st2) := v in
    (*  Property.trace (Show.show lab ++ Show.nl ++
     showStatePair lab frameMap1 frameMap2 st1 st2) *)
    collect (option_bind opcode_of_instr
                         (instr_lookup (st_imem st1) (st_pc st1)))

    (* collect (show lab) *)
            (if indist lab st1 st2 then
               (* XXX Our generator should always give us this by design.
                  If that's not the case the generator is broken. *)
               match fstep t st1 return Gen QProp with
                 | Some (tr1, st1') =>
                   if is_low_state st1 lab then
                     match fstep t st2 with
                       | Some (tr2, st2') =>
                         collect "LOW -> *" (
(*
                                   whenFail
                                     ("LOW -> *" ++ nl ++
                                                 (show_execution lab [st1; st1'] [st2; st2']))
*)
                                     (observe_comp (observe lab tr1) (observe lab tr2)
                                                   && (indist lab st1' st2'))(*:Gen QProp*))
                       | _ => (* 1 took a low step and 2 failed *)
                         collect "Second failed" (property true : Gen QProp)
                     (*
                ((Property.trace (show_pair lab st1 st1'))
                (property false))
                      *)
                     (* XXX This used to fail the property in ICFP paper.
                  But here it does happen for Alloc, Store and BRet *)
                     end
                   else (* is_high st1 *)
                     if is_low_state st1' lab then
                       match fstep t st2 with
                         | Some (tr2, st2') =>
                           if is_low_state st2' lab then
                             collect "HIGH -> LOW" (
(*
                                       whenFail ("HIGH -> LOW" ++ Show.nl ++
                                                                (show_execution lab [st1; st1'] [st2; st2']))
*)
                                                 (observe_comp (observe lab tr1) (observe lab tr2)
                                                               && (indist lab st1' st2')) (* : Gen QProp *)
                                     )
                           else collect "Second not low" (property true : Gen QProp)
                         (* This can happen; it's just a discard *)
                         (* TODO: could check that st2' `indist` st1 *)
                         | _ => collect "Second failed H" (property true : Gen QProp)
                       (* This can happen; it's just a discard *)
                       end
                     else
                       collect "HIGH -> HIGH" (
(*
                                 whenFail ("HIGH -> HIGH" ++ Show.nl ++
                                                          (show_pair lab st1 st1'))
*)
                                          (beq_nat (List.length (observe lab tr1)) 0
                                       && indist lab st1 st1')
                               (*: Gen QProp*))
                 | _ => collect "Failed" (property true : Gen QProp)
               (* This can happen; it's just a discard *)
               (* TODO: could check if st2 does a H -> H step *)
               end
             else collect "Not indist!" (property true : Gen QProp)).
           (* XXX this should never happen with a correct generator;
              and prop_generate_indist already tests this;
              so this should either go away or become (propery false) *)

  Definition propSSNI t : Property Gen :=
    forAllShrink (fun _ => ""%string) gen_variation_state (fun _ => nil)
      (* shrinkVState *)
      (propSSNI_helper t : @Variation State -> Gen QProp).

End Checkers.
