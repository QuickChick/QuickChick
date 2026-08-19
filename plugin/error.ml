let get_flag_debug = ref (fun _ -> assert false)

let qcfail s = failwith (Printf.sprintf "Internal QuickChick Error : %s" s)

let msg_debug   s = if !get_flag_debug () then Feedback.msg_debug s else ()
