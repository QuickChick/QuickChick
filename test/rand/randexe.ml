open Rand

let len = 32

let b = Bytes.create len

let rec go x s =
  let ((s, i), j) = next s in
  Bytes.set_int32_ne b x (Int32.of_int (snd (Uint63.to_int2 i)));
  Bytes.set_int32_ne b (x + 4) (Int32.of_int (snd (Uint63.to_int2 j)));
  if x + 8 = len then (print_bytes b; go 0 s) else go (x + 8) s

let _ = go 0 state0
