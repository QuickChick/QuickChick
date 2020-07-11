type foo = A of int
         (*         | B of string *)
         | C of foo * foo

let rec good_foo (x : foo) : bool =
  match x with
  | A n -> n > 0
  (*   | B _ -> true *)
  | C (x1,x2) -> good_foo x1 && good_foo x2
