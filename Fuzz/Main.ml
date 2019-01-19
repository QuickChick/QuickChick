external setup_shm : unit -> unit = "setup_shm_prim"                

let main =
  setup_shm ();
  Printf.printf "Calling %s...\n" Sys.argv.(1);
  Sys.command Sys.argv.(1);
