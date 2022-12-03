let map_size_pow2 = 16
let map_size = 1 lsl map_size_pow2

let havoc_max_mult = 16.0
let havoc_min = 5.0                   
             
let trace_bits = Array.make map_size 0

let total_bitmap_size = ref 0
let total_bitmap_cnt = ref 0                      
let total_time = ref 0
let total_time_cnt  = ref 0               
               
external setup_shm_aux : unit -> unit = "setup_shm_prim_aux"
external copy_trace_bits : int array -> unit = "copy_trace_bits"
external reset_trace_bits : unit -> unit = "reset_trace_bits"
external has_new_bits : unit -> bool = "has_new_bits_aux"
external count_bytes : unit -> int = "count_bytes_aux"
external count_non_virgin_bytes : unit -> int = "count_non_virgin_bytes"

let count_ones arr =
  Array.iteri (fun i n ->
      if n != 0 then
        Printf.printf "%d: %d %b %b\n" i n (n != 0) (n == 0)
      else ()
    ) arr

(* TODO: Measure time from beginning of generation. *)

let calc_energy time size result =
  let energy0 = 100.0 in
  let avg_time = !total_time / !total_time_cnt in
  let avg_size = !total_bitmap_size / !total_bitmap_cnt in
  
  (* Adjust score based on execution speed of this path, compared to the
     global average. Multiplier ranges from 0.1x to 3x. Fast inputs are
     less expensive to fuzz, so we're giving them more air time. *)

  let op b = if b then (>) else (<) in
  let rec update_energy input average energy params =
    match params with
    | [] -> energy
    | ((im, am, b, mult) :: params') ->
       if (op b) (input * im) (average * am) then energy *. mult
       else update_energy input average energy params'
  in
  
  (* Taken from AFL's ideas *)

  let time_params =
    (* (input multiplier, average multiplied, (>) or (<), output multiplier) *)
    [ (1, 10, true, 0.1) 
    ; (1, 4,  true, 0.25 )
    ; (1, 2,  true, 0.5 )
    ; (3, 4,  true, 0.75 )
    ; (4, 1,  false, 3.0)
    ; (3, 1,  false, 2.0)
    ; (2, 1,  false, 1.5) ] in
  let energy1 = update_energy time avg_time energy0 time_params in
    
  (* Adjust score based on bitmap size. The working theory is that better
     coverage translates to better targets. Multiplier from 0.25x to 3x. *)
  let size_params =
    (* (input multiplier, average multiplied, (>) or (<), output multiplier) *)
    [ (3, 10, true, 3.0)
    ; (1, 2,  true, 2.0)
    ; (3, 4,  true, 1.5)
    ; (3, 1,  false, 0.25)
    ; (2, 1,  false, 0.5)
    ; (3, 2,  false, 0.75) ] in
  let energy2 = update_energy size avg_size energy1 size_params in
  
  (* TODO: 
  /* Adjust score based on handicap. Handicap is proportional to how late
     in the game we learned about this path. Latecomers are allowed to run
     for a bit longer until they catch up with the rest. */

  if (q->handicap >= 4) {

    perf_score *= 4;
    q->handicap -= 4;

  } else if (q->handicap) {

    perf_score *= 2;
    q->handicap--;

  }
   *)
  (* TODO:
  /* Final adjustment based on input depth, under the assumption that fuzzing
     deeper test cases is more likely to reveal stuff that can't be
     discovered with traditional fuzzers. */

  switch (q->depth) {

    case 0 ... 3:   break;
    case 4 ... 7:   perf_score *= 2; break;
    case 8 ... 13:  perf_score *= 3; break;
    case 14 ... 25: perf_score *= 4; break;
    default:        perf_score *= 5;

  }
   *)

  (* If the result is discarded, fuzz less. *)
  let energy3 =
    match result with
    | Some _ -> energy2
    | None -> energy2 *. 0.33
  in 
  
  (* Make sure that we don't go over limit. *)

  let energy_pre_cap = energy3 in
  let energy_capped_top =
    if energy_pre_cap > havoc_max_mult *. 100.0 then
      havoc_max_mult *. 100.0 else energy_pre_cap 
  in
  let energy_capped_bot =
    if energy_capped_top < havoc_min then havoc_min
    else energy_capped_top in

  let multiplier = 100 in
  10 * (Float.to_int energy_capped_bot)
    
let withInstrumentation f =
  (* Reset the C-array bitmap. *)
  reset_trace_bits ();

  (* TODO: Convert to DEBUG *)
  (*   print_endline "Executing...";  *)
  
  let cur_time = Sys.time () in
  let result = f () in
  let stop_time = Sys.time () in

  (*
  (match result with
  | Some b -> Printf.printf "%b\n" b; flush stdout
  | None -> Printf.printf "Discard\n"; flush stdout
  );
   *)
  
  (* Update total time (in us) *)
  let time = Float.to_int ((stop_time -. cur_time) *. 1000000.0) in
  total_time := !total_time + time;
  incr total_time_cnt;

  (* Printf.printf "%d\n" (count_non_virgin_bytes ()); *)
  
  (* Check for new paths *)
  let new_paths = has_new_bits () in

  if new_paths then begin
    (* If new paths exist, update the bitmap size (for score) *)
    let size = count_bytes () in
    total_bitmap_size := !total_bitmap_size + size;
    incr total_bitmap_cnt;
    (* Calculate the energy for the new path *)
    let energy = calc_energy time size result in
    (result, (true, energy))
  end
  else
    (result, (false, 0))

(*
result: result of property check (None means discard)
is_interesting: afl decides whether or not interesting
energy: how long to fuzz (number of iters)
*)