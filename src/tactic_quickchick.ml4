DECLARE PLUGIN "quickchick_plugin"

open Pp

let quickchick_current = 
  Proofview.Goal.enter { enter = begin fun gl ->
    let gl = Proofview.Goal.assume gl in
    Feedback.msg_debug (str "Ran this!" ++ fnl ());
    Tacticals.New.tclIDTAC
  end }

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
  | ["quickchick"] -> [ quickchick_current ]
END;;

