let map_size_pow2 = 16
let map_size = 1 lsl map_size_pow2

let target_path = ref ""

external setup_shm : unit -> unit = "setup_shm_prim"                
external copy_trace_bits : int array -> unit = "copy_trace_bits"
       
let count_ones arr =
  Array.iteri (fun i n ->
      if n != 0 then
        Printf.printf "%d: %d %b %b\n" i n (n != 0) (n == 0)
      else ()
    ) arr

let main =
  let trace_bits = Array.make map_size 0 in
  setup_shm ();
  count_ones trace_bits;

  Sys.command "echo 42 | ./Cout";
  
  copy_trace_bits trace_bits;
  count_ones trace_bits;

