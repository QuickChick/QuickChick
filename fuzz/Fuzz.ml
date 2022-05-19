let map_size_pow2 = 16
let map_size = 1 lsl map_size_pow2

let trace_bits = Array.make map_size 0

external setup_shm_aux : unit -> unit = "setup_shm_prim_aux"
external copy_trace_bits : int array -> unit = "copy_trace_bits"
       
let count_ones arr =
  Array.iteri (fun i n ->
      if n != 0 then
        Printf.printf "%d: %d %b %b\n" i n (n != 0) (n == 0)
      else ()
    ) arr

let main =
  Printf.printf "Entering main\n";
  setup_shm_aux ();

  Printf.printf "Aux setup complete\n";
  count_ones trace_bits;

  let n = C.unlikely_branch 42 in
  Printf.printf "%d\n" n;
  
  copy_trace_bits trace_bits;
  count_ones trace_bits;

