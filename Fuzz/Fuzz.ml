let map_size_pow2 = 16
let map_size = 1 lsl map_size_pow2

let target_path = ref ""

external setup_shm : unit -> unit = "setup_shm_prim"                
external copy_trace_bits : int array -> unit = "copy_trace_bits"
       
let count_ones arr =
  Array.iteri (fun i n ->
      if n != 0 then
        Printf.printf "%d: %d\n" i n
      else ()
    ) arr

  
let main =
  (*   let setup_shm = foreign "setup_shm" (void @-> Array.t unit8_t) in *)
  setup_shm ();
  let trace_bits = Array.make map_size 0 in
  count_ones trace_bits;
  copy_trace_bits trace_bits;
  count_ones trace_bits;

