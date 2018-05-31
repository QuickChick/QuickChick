open Ltac_plugin

DECLARE PLUGIN "quickchick_plugin"

open Pp
open Error
open Constrexpr
open Constrexpr_ops

let quickchick_goal =
  Proofview.Goal.enter begin fun gl ->

    (* Convert goal to a constr_expr *)
    let c = Proofview.Goal.concl gl in
    let e = Proofview.Goal.env gl in
    let evd = Evd.from_env e in
    let ct = Constrextern.extern_constr false e evd c in

    (* Admit a constant with that type *)
    let tmpid = QuickChick.fresh_name "temporary_constant" in
    Vernacentries.interp (CAst.make @@ Vernacexpr.VernacExpr ([],
      (* TODO: NoDischarge or DoDischarge? *)
      Vernacexpr.VernacAssumption ((NoDischarge, Decl_kinds.Conjectural),
                        NoInline,
                        [
                          (false,
                           (
                             [CAst.make tmpid, None]
                           ,
                             ct
                           )
                          )
                        ]
                       )));


    let s = QuickChick.runTest
            (CAst.make @@ CApp((None,QuickChick.quickCheck), [CAst.make @@ CRef (CAst.make @@ Libnames.Ident tmpid,None), None])) in

    match s with
    | Some bytes ->
       Tacticals.New.tclZEROMSG (str ("\n" ^ bytes) ++ fnl ())
    | None -> Tacticals.New.tclZEROMSG (str "Something went wrong. Report." ++ fnl ())

(*

    (* Refactor - needs to see internals... *)
    let base = Names.id_of_string "x" in
    let is_visible_name id =
      try
        ignore (Nametab.locate (Libnames.qualid_of_ident id));
        true
      with Not_found -> false
    in
    (** Safe fresh name generation. *)
    let xid = Namegen.next_ident_away_from base is_visible_name in

    let bind_list = [LocalRawAssum ([(Loc.dummy_loc, Name xid)], Default Explicit, CHole (Loc.dummy_loc, None, Misctypes.IntroAnonymous, None))] in
    let f_body = mkAppC (QuickChick.show, [mkAppC (QuickChick.quickCheck, [mkAppC (QuickChick.mk_ref "checker", [ CRef (Ident ((Loc.dummy_loc, xid)),None) ])])]) in
    let f = mkCLambdaN Loc.dummy_loc bind_list f_body in

    let env = Global.env () in
    let evd = Evd.from_env env in
    let (cf,evd) = Constrintern.interp_constr env evd f in

    let actual_term = Constr.mkApp (cf, Array.of_list [c]) in
 *)


  end

(*
    let concl = Proofview.Goal.concl gl in
    let sigma = Tacmach.New.project gl in
    let hyps = named_context_val (Proofview.Goal.env gl) in
    let store = Proofview.Goal.extra gl in
    let env = Proofview.Goal.env gl in
    let () = if check && mem_named_context_val id hyps then
      errorlabstrm "Tactics.introduction"
        (str "Variable " ++ pr_id id ++ str " is already declared.")
    in
    match kind_of_term (whd_evar sigma concl) with
    | Prod (_, t, b) -> unsafe_intro env store (LocalAssum (id, t)) b
    | LetIn (_, c, t, b) -> unsafe_intro env store (LocalDef (id, c, t)) b
    | _ -> raise (RefinerError IntroNeedsProduct)
  end }
 *)

TACTIC EXTEND quickchick
  | ["quickchick"] -> [ quickchick_goal ]
END;;
