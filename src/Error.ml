let flag_debug = ref false
let flag_warn  = ref true
let flag_error = ref true

let qcfail s = failwith (Printf.sprintf "Internal QuickChick Error : %s" s)

let msg_debug   s = if !flag_debug then Feedback.msg_debug   s else ()
let msg_warning s = if !flag_warn  then Feedback.msg_warning s else ()
let msg_error   s = if !flag_error then Feedback.msg_error   s else ()

