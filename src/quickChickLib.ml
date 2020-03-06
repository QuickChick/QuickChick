(* Convert a list of characters (coq representation) to a string
   (ocaml representation), in order to use the OCaml printing stdlib
   functions. *)
let string_of_coqstring (l : char list) : string =
  let s = Bytes.create (List.length l) in
  let rec copy i = function
  | [] -> s
  | c :: l -> Bytes.set s i c; copy (i+1) l
  in Bytes.to_string (copy 0 l)

(* Randomness for both random + fuzz testing:

   NOTE: This *heavily* relies on the fact that we implement
   splittable pseudorandomness through mutable seed at the OCaml
   level.  If we ever fix that, this will need to be rethinked.  
*)


(* Some of the following functionality is inspired from crowbar. *)
(* A source of randomness is either a random seed or a binary file. *)
type random_src = Random of Random.State.t | Fd of Unix.file_descr

(* A random seed is a source of randomness, a sequence of Bytes
   and an index into that sequence. We will use the randomness
   source to refill the bytes buffer whenever we need more bits,
   if possible. *)
type randomSeed =
  {
    chan : random_src;
    buf : Bytes.t;
    mutable offset : int;
    mutable len : int;
    mutable total : int
  }


(* HACK: For now, whether we are in random test mode or in 
   fuzz test mode is identified by whether or not the executable
   is called with an additional argument. For now, that is sufficient
   but if we ever add additional arguments to our extracted random
   tests, this will need to be rethinked. 

   Random: Random.self_init
   Fuzz  : Open the file and pass the file descriptor

   NOTE: The file is never actually closed...
   TODO: Think about buffer size. 
 *)
let newRandomSeed =
  if Array.length Sys.argv = 1 then
    { chan = Random (Random.State.make_self_init ());
      buf = Bytes.make 256 '0';
      offset = 0;
      len = 0;
      total = 0
    }
  else
    let fd = Unix.openfile Sys.argv.(1) [Unix.O_RDONLY] 0o000 in
    let state = { chan = Fd fd;
                  buf = Bytes.make 256 '0';
                  offset = 0;
                  len = 0;
                  total = 0
                } in
    state

(* mkRandomSeed is used by QuickChick to replay tests.
   Only random testing mode can be used this way.

   TODO: Figure out if there is anything sensible to do 
   for fuzzing here.
 *)    
let mkRandomSeed =
  (fun x ->
    Random.init x;
    { chan = Random (Random.get_state ());
      buf = Bytes.make 256 '0';
      offset = 0;
      len = 0;
      total = 0
    }
  )

let copySeed =
  (fun r ->
    match r.chan with
    | Random r' ->
       { chan = Random (Random.State.copy r')
       ; buf  = Bytes.copy r.buf
       ; offset = r.offset
       ; len    = r.len
       ; total  = r.total
       }
    | Fd fd ->
       (* Not sure what to do here... *)
       r
  )

let registerSeed =
  (fun r_orig r_cur ->
    match r_orig.chan with
    | Random rnd ->
       
       (* Create the seed directory if it doesn't exist *)
       Sys.command "mkdir -p _seeds";
       (* Open a new file to write *)
       let f = Filename.temp_file ~temp_dir:"_seeds" "seed" ".qc" in
       print_endline f;
       let fd = Unix.openfile f [Unix.O_WRONLY] 0o600 in
       
       (* Calculate how many bytes were extracted from the seed *)
       let remaining = r_orig.len - r_orig.offset in
       let total = r_cur.total - r_orig.total + remaining + 1 in

       Printf.printf "Debugging:\nCur:\nTotal: %d.\nOld:\nTotal: %d\nLen: %d\nOffset: %d\n" r_cur.total r_orig.total r_orig.len r_orig.offset; 
       
       (* Create new buffer big enough *)
       let bits = Bytes.make total '0' in

       (* Copy whatever was left from the original buffer to the beginning of the result *)
       Bytes.blit r_orig.buf r_orig.offset bits 0 remaining;

       (* Simulate the bytes taken from the random seed *)
       for i = remaining to total - 1 do
         let thirty_bits = Random.State.bits rnd in
         let random_byte = thirty_bits land 0xff in
         Bytes.set bits i (Char.chr random_byte)
       done;

       (* Write the bits *)
       Unix.write fd bits 0 total;
       
       0
    | _ -> 0
  ) 

(* HACK: We ignore splittalbe randomness by allowing the seed to 
   be mutable. 
   PRO: we can actually fuzz the input randomness.
   CONS: CoArbitrary doesn't work.
 *)  
let randomSplit = (fun x -> (x,x))

exception InsufficientRandomness

(* Fill the buffer from OFFset to LENgth using 
   the src of randomness. *)        
let fill_rnd_buffer src buf off len r =
  match src with
  | Random rand ->
     for i = off to off + len - 1 do
       (* Set each byte of the array using Randomness.
          This wastes a TON of randomness...
        *)
       let thirty_bits = Random.State.bits rand in
       let random_byte = thirty_bits land 0xff in
       r.total <- r.total + 1;
       Bytes.set buf i (Char.chr random_byte)
     done;
     len - off
  | Fd ch ->
     (* Just read of the input binary *)
     Unix.read ch buf off len

let refill src =
  assert (src.offset <= src.len);
  let remaining = src.len - src.offset in
  (* move remaining data to start of buffer *)
  Bytes.blit src.buf src.offset src.buf 0 remaining;
  src.len <- remaining;
  src.offset <- 0;
  let read = fill_rnd_buffer src.chan src.buf remaining (Bytes.length src.buf - remaining) src in
  if read = 0 then
    raise InsufficientRandomness
  else
    src.len <- remaining + read

let rec getbytes src n =
  assert (src.offset <= src.len);
  if n > Bytes.length src.buf then failwith "request too big";
  if src.len - src.offset >= n then
    let off = src.offset in
    (src.offset <- src.offset + n; off)
  else
    (refill src; getbytes src n)

let read_char src =
  let off = getbytes src 1 in
  Bytes.get src.buf off

let read_byte src =
  Char.code (read_char src)

let choose_int n state =
  assert (n > 0);
  if n = 1 then
    0
  else if n < 100 then
    read_byte state mod n
  else
    let n1 = read_byte state in
    let n2 = read_byte state in
    let n3 = read_byte state in
    let n4 = read_byte state in
    (n1 lsl 12 + n2 lsl 8 + n3 lsl 4 + n4) mod n

let choose_float d state =
  assert (d > 0.0);
  let ip = float_of_int (choose_int (truncate d) state) in
  let rp = (float_of_int (choose_int 1000 state)) /. 1000.0 in
  ip +. rp
      
let randomNext =
  (fun r -> choose_int 128 r, r)
    
let randomRNat =
  (fun (x,y) r ->
    let min = x in
    let n = y - x + 1 in
    if n <= 0 then
      raise (Invalid_argument "QuickChick.randomR: range is empty");
    min + choose_int n r, r
  )

let randomRBool =
  (fun (x,y) r ->
    let flip = choose_int 2 r in
    (if flip = 0 then true else false)
    , r)

let randomRInt = randomRNat
let randomRN   = randomRNat                   
let randomRFloat =
  (fun (x,y) r ->
    let min = x in
    let n = y -. x in
    if n <= 0.0 then
      raise (Invalid_argument ("QuickChick.randomR: range is empty " ^ string_of_float x ^ " " ^ string_of_float y));
    min +. choose_float n r, r
  )
      

                   
