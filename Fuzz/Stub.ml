let map_size_pow2 = 16
let map_size = 1 lsl map_size_pow2

let trace_bits = Array.make map_size 0
             
external setup_shm_aux : unit -> unit = "setup_shm_prim_aux"
external copy_trace_bits : int array -> unit = "copy_trace_bits"
external reset_trace_bits : unit -> unit = "reset_trace_bits"

let count_ones arr =
  Array.iteri (fun i n ->
      if n != 0 then
        Printf.printf "%d: %d %b %b\n" i n (n != 0) (n == 0)
      else ()
    ) arr
                                         
let withInstrumentation f cont =
  reset_trace_bits ();
  print_endline "Executing...";
  count_ones trace_bits;
  let b = f () in
  print_endline "After calling property...";
  copy_trace_bits trace_bits;
  count_ones trace_bits;
  let is_interesting = true in
  cont b is_interesting
