(* Helper functions for extraction *)
let string_of_coqstring (l : char list) : string =
  let s = Bytes.create (List.length l) in
  let rec copy i = function
  | [] -> s
  | c :: l -> Bytes.set s i c; copy (i+1) l
  in Bytes.to_string (copy 0 l)

type random_src = Random of Random.State.t | Fd of Unix.file_descr

type randomSeed =
  {
    chan : random_src;
    buf : Bytes.t;
    mutable offset : int;
    mutable len : int
  }

let newRandomSeed =
  if Array.length Sys.argv = 1 then
    { chan = Random (Random.State.make_self_init ());
      buf = Bytes.make 256 '0';
      offset = 0;
      len = 0 }
  else
    let fd = Unix.openfile Sys.argv.(1) [Unix.O_RDONLY] 0o000 in
    let state = { chan = Fd fd;
                  buf = Bytes.make 256 '0';
                  offset = 0;
                  len = 0 } in
    state

let mkRandomSeed =
  (fun x ->
    Random.init x;
    { chan = Random (Random.get_state ());
      buf = Bytes.make 256 '0';
      offset = 0;
      len = 0 }
  )
    
let randomSplit = (fun x -> (x,x))

let get_data chan buf off len =
  match chan with
  | Random rand ->
     for i = off to off + len - 1 do
       Bytes.set buf i (Char.chr (Random.State.bits rand land 0xff))
     done;
     len - off
  | Fd ch ->
     Unix.read ch buf off len

exception BadTest of string
    
let refill src =
  assert (src.offset <= src.len);
  let remaining = src.len - src.offset in
  (* move remaining data to start of buffer *)
  Bytes.blit src.buf src.offset src.buf 0 remaining;
  src.len <- remaining;
  src.offset <- 0;
  let read = get_data src.chan src.buf remaining (Bytes.length src.buf - remaining) in
  if read = 0 then
    raise (BadTest "premature end of file")
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
