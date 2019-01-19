external setup_shm : unit -> unit = "setup_shm_prim"                

let main =
  setup_shm ();
  Printf.printf "Returning from setup_shm\n";
  Sys.command "./foo"
