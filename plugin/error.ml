open Pp

(* Debug output is off until the plugin registers its QuickChickDebug flag. *)
let get_flag_debug = ref (fun _ -> false)

let qcfail s = failwith (Printf.sprintf "Internal QuickChick Error : %s" s)

let msg_debug   s = if !get_flag_debug () then Feedback.msg_debug s else ()
let msg_error s = CErrors.user_err (str "QuickChick Error:" ++ fnl () ++ s ++ fnl ())
