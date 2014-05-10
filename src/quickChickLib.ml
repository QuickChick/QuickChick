(* Helper functions for extraction *)
let string_of_coqstring (l : char list) =
  let s = String.create (List.length l) in
  let rec copy i = function
  | [] -> s
  | c :: l -> s.[i] <- c; copy (i+1) l
  in copy 0 l

let coqstring_of_string s =
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1)
