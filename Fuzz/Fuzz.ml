let map_size_pow2 = 16
let map_size = 1 lsl map_size_pow2

let target_path = ref ""

external setup_shm : unit -> int array = "setup_shm_prim"                

let count_ones arr =
  Array.iteri (fun i n ->
      if n == 0 then
        Printf.printf "%d: %d\n" i n
      else ()
    ) arr

let trace_bytes = setup_shm ()
  
let main =
  (*   let setup_shm = foreign "setup_shm" (void @-> Array.t unit8_t) in *)
  count_ones trace_bytes

