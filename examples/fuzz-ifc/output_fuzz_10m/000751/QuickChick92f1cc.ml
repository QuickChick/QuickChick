
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Pervasives.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

(** val revapp : uint -> uint -> uint **)

let rec revapp d d' =
  match d with
  | Nil -> d'
  | D0 d0 -> revapp d0 (D0 d')
  | D1 d0 -> revapp d0 (D1 d')
  | D2 d0 -> revapp d0 (D2 d')
  | D3 d0 -> revapp d0 (D3 d')
  | D4 d0 -> revapp d0 (D4 d')
  | D5 d0 -> revapp d0 (D5 d')
  | D6 d0 -> revapp d0 (D6 d')
  | D7 d0 -> revapp d0 (D7 d')
  | D8 d0 -> revapp d0 (D8 d')
  | D9 d0 -> revapp d0 (D9 d')

(** val rev : uint -> uint **)

let rev d =
  revapp d Nil

module Little =
 struct
  (** val succ : uint -> uint **)

  let rec succ = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 d0
  | D1 d0 -> D2 d0
  | D2 d0 -> D3 d0
  | D3 d0 -> D4 d0
  | D4 d0 -> D5 d0
  | D5 d0 -> D6 d0
  | D6 d0 -> D7 d0
  | D7 d0 -> D8 d0
  | D8 d0 -> D9 d0
  | D9 d0 -> D0 (succ d0)

  (** val double : uint -> uint **)

  let rec double = function
  | Nil -> Nil
  | D0 d0 -> D0 (double d0)
  | D1 d0 -> D2 (double d0)
  | D2 d0 -> D4 (double d0)
  | D3 d0 -> D6 (double d0)
  | D4 d0 -> D8 (double d0)
  | D5 d0 -> D0 (succ_double d0)
  | D6 d0 -> D2 (succ_double d0)
  | D7 d0 -> D4 (succ_double d0)
  | D8 d0 -> D6 (succ_double d0)
  | D9 d0 -> D8 (succ_double d0)

  (** val succ_double : uint -> uint **)

  and succ_double = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 (double d0)
  | D1 d0 -> D3 (double d0)
  | D2 d0 -> D5 (double d0)
  | D3 d0 -> D7 (double d0)
  | D4 d0 -> D9 (double d0)
  | D5 d0 -> D1 (succ_double d0)
  | D6 d0 -> D3 (succ_double d0)
  | D7 d0 -> D5 (succ_double d0)
  | D8 d0 -> D7 (succ_double d0)
  | D9 d0 -> D9 (succ_double d0)
 end

module Coq__1 = struct
 (** val add : int -> int -> int **)let rec add = (+)
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Pervasives.max 0 (n-m)



type reflect =
| ReflectT
| ReflectF

(** val internal_eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let internal_eq_rew_r_dep _ _ hC =
  hC

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module Nat =
 struct
  (** val sub : int -> int -> int **)

  let rec sub n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun l -> sub k l)
        m)
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Pervasives.succ n) m

  (** val to_little_uint : int -> uint -> uint **)

  let rec to_little_uint n acc =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> acc)
      (fun n0 -> to_little_uint n0 (Little.succ acc))
      n

  (** val to_uint : int -> uint **)

  let to_uint n =
    rev (to_little_uint n (D0 Nil))

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (Pervasives.succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div = (/)

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y
 end

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Pervasives.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op0 p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op0 a (iter_op op0 p0 (op0 a a)))
      (fun p0 -> iter_op op0 p0 (op0 a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Pervasives.succ 0)

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n

  (** val to_little_uint : int -> uint **)

  let rec to_little_uint p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> Little.succ_double (to_little_uint p0))
      (fun p0 -> Little.double (to_little_uint p0))
      (fun _ -> D1 Nil)
      p

  (** val to_uint : int -> uint **)

  let to_uint p =
    rev (to_little_uint p)

  (** val eq_dec : int -> int -> bool **)

  let rec eq_dec p x0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p
 end

module N =
 struct
  (** val add : int -> int -> int **)

  let add = (+)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val to_nat : int -> int **)

  let to_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      a

  (** val of_nat : int -> int **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' -> (Pos.of_succ_nat n'))
      n
 end

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : int -> char **)

let ascii_of_pos =
  let rec loop n p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> zero)
      (fun n' ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p' -> shift true (loop n' p'))
        (fun p' -> shift false (loop n' p'))
        (fun _ -> one)
        p)
      n
  in loop (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       0))))))))

(** val ascii_of_N : int -> char **)

let ascii_of_N n =
  (fun f0 fp n -> if n=0 then f0 () else fp n)
    (fun _ -> zero)
    (fun p -> ascii_of_pos p)
    n

(** val ascii_of_nat : int -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val n_of_digits : bool list -> int **)

let rec n_of_digits = function
| [] -> 0
| b :: l' ->
  N.add (if b then 1 else 0) (N.mul ((fun p->2*p) 1) (n_of_digits l'))

(** val n_of_ascii : char -> int **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> int **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> default
              | x :: _ -> x)
    (fun m -> match l with
              | [] -> default
              | _ :: t2 -> nth m t2 default)
    n

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> None
              | x :: _ -> Some x)
    (fun n0 -> match l with
               | [] -> None
               | _ :: l0 -> nth_error l0 n0)
    n

(** val rev0 : 'a1 list -> 'a1 list **)

let rec rev0 = function
| [] -> []
| x :: l' -> app (rev0 l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t2 -> (f a) :: (map f t2)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t2 -> fold_left f t2 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t2 -> f b (fold_right f a0 t2)

(** val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x :: tl ->
    (match l' with
     | [] -> []
     | y :: tl' -> (x, y) :: (combine tl tl'))

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : int -> int -> bool **)

  let rec eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        y)
      x

  (** val max : int -> int -> int **)

  let max = Pervasives.max

  (** val to_nat : int -> int **)

  let to_nat z =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      (fun _ -> 0)
      z

  (** val of_nat : int -> int **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n0 -> (Pos.of_succ_nat n0))
      n

  (** val to_int : int -> unit **)

  let to_int n =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (fun _ -> ()) (D0 Nil))
      (fun p -> (fun _ -> ()) (Pos.to_uint p))
      (fun p -> (fun _ -> ()) (Pos.to_uint p))
      n

  (** val eq_dec : int -> int -> bool **)

  let eq_dec x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun x0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun p0 -> Pos.eq_dec x0 p0)
        (fun _ -> false)
        y)
      (fun x0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun p0 -> Pos.eq_dec x0 p0)
        y)
      x
 end

(** val z_lt_dec : int -> int -> bool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> true
  | _ -> false

(** val string_dec : char list -> char list -> bool **)

let rec string_dec s x =
  match s with
  | [] -> (match x with
           | [] -> true
           | _::_ -> false)
  | a::s0 ->
    (match x with
     | [] -> false
     | a0::s1 -> if (=) a a0 then string_dec s0 s1 else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val newline : char list **)

let newline =
  '\n'::[]

type 'a show =
  'a -> char list
  (* singleton inductive, whose constructor was Build_Show *)

(** val show0 : 'a1 show -> 'a1 -> char list **)

let show0 show1 =
  show1

(** val show_nat : int -> char list **)

let show_nat = (fun i ->
  let s = string_of_int i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))

(** val show_bool : bool -> char list **)

let show_bool = (fun i ->
  let s = string_of_bool i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))

(** val show_Z : int -> char list **)

let show_Z = (fun i ->
  let s = string_of_int i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))

(** val showNat : int show **)

let showNat =
  show_nat

(** val showBool : bool show **)

let showBool =
  show_bool

(** val showZ : int show **)

let showZ =
  show_Z

(** val from_list : char list -> char list **)

let rec from_list = function
| [] -> []
| c :: s' -> c::(from_list s')

(** val unit_digit : int -> char **)

let unit_digit n =
  ascii_of_nat
    (add
      (Nat.modulo n (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))

(** val three_digit : int -> char list **)

let three_digit n =
  let n0 = unit_digit n in
  let n1 =
    unit_digit
      (Nat.div n (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))
  in
  let n2 =
    unit_digit
      (Nat.div n (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  in
  from_list (n2 :: (n1 :: (n0 :: [])))

(** val show_quoted_string : char list -> char list **)

let rec show_quoted_string = function
| [] -> '"'::[]
| c::s' ->
  let quoted_s' = show_quoted_string s' in
  let n = nat_of_ascii c in
  if (=) c '\t'
  then append ('\\'::('t'::[])) quoted_s'
  else if (=) c '\n'
       then append ('\\'::('n'::[])) quoted_s'
       else if (=) c '\r'
            then append ('\\'::('r'::[])) quoted_s'
            else if (=) c '"'
                 then append ('\\'::('"'::[])) quoted_s'
                 else if (=) c '\\'
                      then append ('\\'::('\\'::[])) quoted_s'
                      else if (||)
                                (Nat.ltb n (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  0)))))))))))))))))))))))))))))))))
                                (Nat.ltb (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  n)
                           then append ('\\'::[])
                                  (append (three_digit n) quoted_s')
                           else c::quoted_s'

(** val showString : char list show **)

let showString s =
  '"'::(show_quoted_string s)

(** val showOpt : 'a1 show -> 'a1 option show **)

let showOpt h = function
| Some x0 -> append ('S'::('o'::('m'::('e'::(' '::[]))))) (show0 h x0)
| None -> 'N'::('o'::('n'::('e'::[])))

(** val nl : char list **)

let nl =
  '\n'::[]

module ShowFunctions =
 struct
  (** val prepend : 'a1 -> 'a1 list -> 'a1 list **)

  let rec prepend a = function
  | [] -> []
  | h :: t2 -> a :: (h :: (prepend a t2))

  (** val intersperse : 'a1 -> 'a1 list -> 'a1 list **)

  let intersperse a = function
  | [] -> []
  | h :: t2 -> h :: (prepend a t2)

  (** val string_concat : char list list -> char list **)

  let string_concat l =
    fold_left append l []
 end

(** val trace : char list -> 'a1 -> 'a1 **)

let trace = (fun l -> print_string (
   let s = Bytes.create (List.length l) in
   let rec copy i = function
    | [] -> s
    | c :: l -> s.[i] <- c; copy (i+1) l
   in Bytes.to_string (copy 0 l)); flush stdout; fun y -> y)

(** val deprecate : char list -> char list -> 'a1 -> 'a1 **)

let deprecate old new0 a =
  trace
    (append
      ('D'::('e'::('p'::('r'::('e'::('c'::('a'::('t'::('e'::('d'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(':'::(' '::[])))))))))))))))))))))
      (append old
        (append ('.'::(' '::('U'::('s'::('e'::(' '::[]))))))
          (append new0
            (append
              (' '::('i'::('n'::('s'::('t'::('e'::('a'::('d'::('.'::[])))))))))
              nl))))) a

(** val is_left : bool -> bool **)

let is_left = function
| true -> true
| false -> false

type decidable = bool

(** val iffP : bool -> reflect -> reflect **)

let iffP _ pb =
  let _evar_0_ = fun _ _ _ -> ReflectT in
  let _evar_0_0 = fun _ _ _ -> ReflectF in
  (match pb with
   | ReflectT -> _evar_0_ __ __ __
   | ReflectF -> _evar_0_0 __ __ __)

(** val idP : bool -> reflect **)

let idP = function
| true -> ReflectT
| false -> ReflectF

type 't pred = 't -> bool

type 't rel = 't -> 't pred

module Equality =
 struct
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  (** val op : 'a1 mixin_of -> 'a1 rel **)

  let op x = x.op

  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort mixin_of **)

  let coq_class cT =
    cT
 end

(** val eq_op : Equality.coq_type -> Equality.sort rel **)

let eq_op t2 =
  (Equality.coq_class t2).Equality.op

type t0 =
| F1 of int
| FS of int * t0

(** val of_nat_lt : int -> int -> t0 **)

let rec of_nat_lt p n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> assert false (* absurd case *))
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> F1 n')
      (fun p' -> FS (n', (of_nat_lt p' n')))
      p)
    n

type 'a t1 =
| Nil0
| Cons of 'a * int * 'a t1

(** val caseS : ('a1 -> int -> 'a1 t1 -> 'a2) -> int -> 'a1 t1 -> 'a2 **)

let caseS h _ = function
| Nil0 -> Obj.magic __
| Cons (h0, n, t2) -> h h0 n t2

(** val nth0 : int -> 'a1 t1 -> t0 -> 'a1 **)

let rec nth0 _ v' = function
| F1 n -> caseS (fun h _ _ -> h) n v'
| FS (n, p') -> caseS (fun _ -> nth0) n v' p'

(** val nth_order : int -> 'a1 t1 -> int -> 'a1 **)

let nth_order n v p =
  nth0 n v (of_nat_lt p n)

(** val eqn : int -> int -> bool **)

let rec eqn = (==)

(** val eqnP : int Equality.axiom **)

let eqnP n m =
  iffP (eqn n m) (idP (eqn n m))

(** val nat_eqMixin : int Equality.mixin_of **)

let nat_eqMixin =
  { Equality.op = eqn; Equality.mixin_of__1 = eqnP }

(** val nat_eqType : Equality.coq_type **)

let nat_eqType =
  Obj.magic nat_eqMixin

(** val addn_rec : int -> int -> int **)

let addn_rec =
  add

(** val addn : int -> int -> int **)

let addn =
  addn_rec

(** val subn_rec : int -> int -> int **)

let subn_rec =
  sub

(** val subn : int -> int -> int **)

let subn =
  subn_rec

(** val leq : int -> int -> bool **)

let leq m n =
  eq_op nat_eqType (Obj.magic subn m n) (Obj.magic 0)

(** val minn : int -> int -> int **)

let minn m n =
  if leq (Pervasives.succ m) n then m else n

(** val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter n f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> x)
    (fun i -> f (iter i f x))
    n

(** val muln_rec : int -> int -> int **)

let muln_rec =
  mul

(** val muln : int -> int -> int **)

let muln =
  muln_rec

type randomSeed = QuickChickLib.randomSeed

(** val newRandomSeed : randomSeed **)

let newRandomSeed = QuickChickLib.newRandomSeed

(** val copySeed : randomSeed -> randomSeed **)

let copySeed = QuickChickLib.copySeed

(** val randomSplit : randomSeed -> randomSeed * randomSeed **)

let randomSplit = QuickChickLib.randomSplit

type randomSeedTree = __randomSeedTree Lazy.t
and __randomSeedTree =
| RstNode of randomSeed * randomSeedTree * randomSeedTree

(** val mkSeedTree : randomSeed -> randomSeedTree **)

let rec mkSeedTree s =
  let (s1, s2) = randomSplit s in
  lazy (RstNode (s, (mkSeedTree s1), (mkSeedTree s2)))

type splitDirection =
| Left
| Right

type splitPath = splitDirection list

(** val varySeedAux : splitPath -> randomSeedTree -> randomSeed **)

let rec varySeedAux p rst =
  let RstNode (s, t2, t3) = Lazy.force rst in
  (match p with
   | [] -> s
   | s0 :: p' ->
     (match s0 with
      | Left -> varySeedAux p' t2
      | Right -> varySeedAux p' t3))

(** val varySeed : splitPath -> randomSeed -> randomSeed **)

let varySeed p s =
  varySeedAux p (mkSeedTree s)

(** val randomRNat : (int * int) -> randomSeed -> int * randomSeed **)

let randomRNat = QuickChickLib.randomRNat

(** val randomRInt : (int * int) -> randomSeed -> int * randomSeed **)

let randomRInt = QuickChickLib.randomRInt

type 'a ordType =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_OrdType *)

(** val ordNat : int ordType **)

let ordNat =
  leq

(** val ordZ : int ordType **)

let ordZ =
  Z.leb

type 'a choosableFromInterval = { super : 'a ordType;
                                  randomR : (('a * 'a) -> randomSeed ->
                                            'a * randomSeed) }

(** val randomR :
    'a1 choosableFromInterval -> ('a1 * 'a1) -> randomSeed -> 'a1 * randomSeed **)

let randomR x = x.randomR

(** val chooseNat : int choosableFromInterval **)

let chooseNat =
  { super = ordNat; randomR = randomRNat }

(** val chooseZ : int choosableFromInterval **)

let chooseZ =
  { super = ordZ; randomR = randomRInt }

(** val ncons : int -> 'a1 -> 'a1 list -> 'a1 list **)

let ncons n x =
  iter n (fun x0 -> x :: x0)

(** val nseq : int -> 'a1 -> 'a1 list **)

let nseq n x =
  ncons n x []

(** val nth1 : 'a1 -> 'a1 list -> int -> 'a1 **)

let rec nth1 x0 s n =
  match s with
  | [] -> x0
  | x :: s' ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> x)
       (fun n' -> nth1 x0 s' n')
       n)

(** val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldr f z0 = function
| [] -> z0
| x :: s' -> f x (foldr f z0 s')

(** val foldl : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldl f z = function
| [] -> z
| x :: s' -> foldl f (f z x) s'

type 'f functor0 =
  __ -> __ -> (__ -> __) -> 'f -> 'f
  (* singleton inductive, whose constructor was Build_Functor *)

type 't applicative = { pure : (__ -> __ -> 't);
                        ap : (__ -> __ -> 't -> 't -> 't) }

type 'm monad = { ret : (__ -> __ -> 'm);
                  bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

(** val ret : 'a1 monad -> 'a2 -> 'a1 **)

let ret monad0 x =
  let { ret = ret0; bind = _ } = monad0 in Obj.magic ret0 __ x

(** val bind : 'a1 monad -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let bind monad0 x x0 =
  let { ret = _; bind = bind1 } = monad0 in Obj.magic bind1 __ __ x x0

type 'm pMonad = { pret : (__ -> __ -> __ -> 'm);
                   pbind : (__ -> __ -> __ -> 'm -> (__ -> 'm) -> 'm) }

type ('m, 'x) monP = __

(** val pbind :
    'a1 pMonad -> ('a1, 'a3) monP -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let pbind pMonad0 pu x x0 =
  let { pret = _; pbind = pbind0 } = pMonad0 in Obj.magic pbind0 __ __ pu x x0

(** val pMonad_Monad : 'a1 monad -> 'a1 pMonad **)

let pMonad_Monad m =
  { pret = (fun _ -> Obj.magic (fun _ x -> ret m x)); pbind = (fun _ _ ->
    Obj.magic (fun _ c f -> bind m c f)) }

(** val force : 'a1 Lazy.t -> 'a1 **)

let force = Lazy.force

type 'a rose =
| MkRose of 'a * 'a rose list Lazy.t

(** val returnRose : 'a1 -> 'a1 rose **)

let returnRose x =
  MkRose (x, (lazy []))

(** val joinRose : 'a1 rose rose -> 'a1 rose **)

let rec joinRose = function
| MkRose (r0, tts) ->
  let MkRose (a, ts) = r0 in
  MkRose (a, (lazy (app (map joinRose (force tts)) (force ts))))

(** val fmapRose : ('a1 -> 'a2) -> 'a1 rose -> 'a2 rose **)

let rec fmapRose f = function
| MkRose (x, rs) -> MkRose ((f x), (lazy (map (fmapRose f) (force rs))))

module type Sig =
 sig
  type 'x coq_G

  val returnGen : 'a1 -> 'a1 coq_G

  val bindGen : 'a1 coq_G -> ('a1 -> 'a2 coq_G) -> 'a2 coq_G

  val bindGenOpt :
    'a1 option coq_G -> ('a1 -> 'a2 option coq_G) -> 'a2 option coq_G

  val run : 'a1 coq_G -> int -> randomSeed -> 'a1

  val fmap : ('a1 -> 'a2) -> 'a1 coq_G -> 'a2 coq_G

  val apGen : ('a1 -> 'a2) coq_G -> 'a1 coq_G -> 'a2 coq_G

  val sized : (int -> 'a1 coq_G) -> 'a1 coq_G

  val resize : int -> 'a1 coq_G -> 'a1 coq_G

  val promote : 'a1 coq_G rose -> 'a1 rose coq_G

  val suchThatMaybe : 'a1 coq_G -> ('a1 -> bool) -> 'a1 option coq_G

  val suchThatMaybeOpt : 'a1 option coq_G -> ('a1 -> bool) -> 'a1 option coq_G

  val choose : 'a1 choosableFromInterval -> ('a1 * 'a1) -> 'a1 coq_G

  val sample : 'a1 coq_G -> 'a1 list

  val variant : splitPath -> 'a1 coq_G -> 'a1 coq_G

  val reallyUnsafePromote : ('a1 -> 'a2 coq_G) -> ('a1 -> 'a2) coq_G

  val bindGen' : 'a1 coq_G -> ('a1 -> __ -> 'a2 coq_G) -> 'a2 coq_G

  val coq_Functor_G : __ coq_G functor0

  val coq_Applicative_G : __ coq_G applicative

  val coq_Monad_G : __ coq_G monad

  type 'a coq_GOpt = 'a option coq_G

  val coq_Monad_GOpt : __ coq_GOpt monad

  val thunkGen : (unit -> 'a1 coq_G) -> 'a1 coq_G
 end

module GenLow =
 struct
  type 'a coq_GenType =
    int -> randomSeed -> 'a
    (* singleton inductive, whose constructor was MkGen *)

  type 'a coq_G = 'a coq_GenType

  (** val run : 'a1 coq_G -> int -> randomSeed -> 'a1 **)

  let run g =
    g

  (** val returnGen : 'a1 -> 'a1 coq_G **)

  let returnGen x _ _ =
    x

  (** val bindGen : 'a1 coq_G -> ('a1 -> 'a2 coq_G) -> 'a2 coq_G **)

  let bindGen g k n r =
    let (r1, r2) = randomSplit r in run (k (run g n r1)) n r2

  (** val bindGenOpt :
      'a1 option coq_G -> ('a1 -> 'a2 option coq_G) -> 'a2 option coq_G **)

  let bindGenOpt g f =
    bindGen g (fun ma -> match ma with
                         | Some a -> f a
                         | None -> returnGen None)

  (** val fmap : ('a1 -> 'a2) -> 'a1 coq_G -> 'a2 coq_G **)

  let fmap f g n r =
    f (run g n r)

  (** val apGen : ('a1 -> 'a2) coq_G -> 'a1 coq_G -> 'a2 coq_G **)

  let apGen gf gg =
    bindGen gf (fun f -> fmap f gg)

  (** val sized : (int -> 'a1 coq_G) -> 'a1 coq_G **)

  let sized f n r =
    run (f n) n r

  (** val resize : int -> 'a1 coq_G -> 'a1 coq_G **)

  let resize n g _ =
    g n

  (** val promote : 'a1 coq_G rose -> 'a1 rose coq_G **)

  let promote m n r =
    fmapRose (fun g -> run g n r) m

  (** val suchThatMaybeAux :
      'a1 coq_G -> ('a1 -> bool) -> int -> int -> 'a1 option coq_G **)

  let rec suchThatMaybeAux g p k n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> returnGen None)
      (fun n' ->
      bindGen
        (resize (addn (muln (Pervasives.succ (Pervasives.succ 0)) k) n) g)
        (fun x ->
        if p x
        then returnGen (Some x)
        else suchThatMaybeAux g p (Pervasives.succ k) n'))
      n

  (** val suchThatMaybe : 'a1 coq_G -> ('a1 -> bool) -> 'a1 option coq_G **)

  let suchThatMaybe g p =
    sized (fun x ->
      suchThatMaybeAux g p 0 (Pervasives.max (Pervasives.succ 0) x))

  (** val suchThatMaybeOptAux :
      'a1 option coq_G -> ('a1 -> bool) -> int -> int -> 'a1 option coq_G **)

  let rec suchThatMaybeOptAux g p k n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> returnGen None)
      (fun n' ->
      bindGen
        (resize (addn (muln (Pervasives.succ (Pervasives.succ 0)) k) n) g)
        (fun mx ->
        match mx with
        | Some x ->
          if p x
          then returnGen (Some x)
          else suchThatMaybeOptAux g p (Pervasives.succ k) n'
        | None -> suchThatMaybeOptAux g p (Pervasives.succ k) n'))
      n

  (** val suchThatMaybeOpt :
      'a1 option coq_G -> ('a1 -> bool) -> 'a1 option coq_G **)

  let suchThatMaybeOpt g p =
    sized (fun x ->
      suchThatMaybeOptAux g p 0 (Pervasives.max (Pervasives.succ 0) x))

  (** val rnds : randomSeed -> int -> randomSeed list **)

  let rec rnds rnd n' =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> [])
      (fun n'' ->
      let (rnd1, rnd2) = randomSplit rnd in rnd1 :: (rnds rnd2 n''))
      n'

  (** val createRange : int -> int list -> int list **)

  let rec createRange n acc =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> rev0 (0 :: acc))
      (fun n' -> createRange n' (n :: acc))
      n

  (** val choose : 'a1 choosableFromInterval -> ('a1 * 'a1) -> 'a1 coq_G **)

  let choose h range _ r =
    fst (h.randomR range r)

  (** val sample : 'a1 coq_G -> 'a1 list **)

  let sample g =
    let l =
      combine
        (rnds newRandomSeed (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))
        (createRange (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) [])
    in
    map (fun p -> let (r, n) = p in g n r) l

  (** val variant : splitPath -> 'a1 coq_G -> 'a1 coq_G **)

  let variant p g n r =
    g n (varySeed p r)

  (** val reallyUnsafeDelay : ('a1 coq_G -> 'a1) coq_G **)

  let reallyUnsafeDelay r n g =
    g r n

  (** val reallyUnsafePromote : ('a1 -> 'a2 coq_G) -> ('a1 -> 'a2) coq_G **)

  let reallyUnsafePromote m =
    bindGen reallyUnsafeDelay (fun eval -> returnGen (fun r -> eval (m r)))

  type semGenSize = __

  type semGen = __

  (** val bindGen' : 'a1 coq_G -> ('a1 -> __ -> 'a2 coq_G) -> 'a2 coq_G **)

  let bindGen' g k n r =
    let (r1, r2) = randomSplit r in run (k (run g n r1) __) n r2

  (* Unsized : logical inductive *)
  (* with constructors : Build_Unsized *)
  

  (** val unsized : __ **)

  let unsized =
    __

  (* SizedMonotonic : logical inductive *)
  (* with constructors : Build_SizedMonotonic *)
  

  (** val sizeMonotonic : __ **)

  let sizeMonotonic =
    __

  (* SizedMonotonicOpt : logical inductive *)
  (* with constructors : Build_SizedMonotonicOpt *)
  

  (** val sizeMonotonicOpt : __ **)

  let sizeMonotonicOpt =
    __

  (* SizeMonotonic : logical inductive *)
  (* with constructors : Build_SizeMonotonic *)
  

  (** val monotonic : __ **)

  let monotonic =
    __

  (* SizeMonotonicOpt : logical inductive *)
  (* with constructors : Build_SizeMonotonicOpt *)
  

  (** val monotonic_opt : __ **)

  let monotonic_opt =
    __

  (* SizeAntiMonotonicNone : logical inductive *)
  (* with constructors : Build_SizeAntiMonotonicNone *)
  

  (** val monotonic_none : __ **)

  let monotonic_none =
    __

  (** val unsizedMonotonic : __ **)

  let unsizedMonotonic =
    __

  (** val unsized_alt_def : __ **)

  let unsized_alt_def =
    __

  (** val semReturn : __ **)

  let semReturn =
    __

  (** val semReturnSize : __ **)

  let semReturnSize =
    __

  (** val unsizedReturn : __ **)

  let unsizedReturn =
    __

  (** val returnGenSizeMonotonic : __ **)

  let returnGenSizeMonotonic =
    __

  (** val returnGenSizeMonotonicOpt : __ **)

  let returnGenSizeMonotonicOpt =
    __

  (** val semBindSize : __ **)

  let semBindSize =
    __

  (** val semBindSize_subset_compat : __ **)

  let semBindSize_subset_compat =
    __

  (** val semBindSizeOpt_subset_compat : __ **)

  let semBindSizeOpt_subset_compat =
    __

  (** val monad_leftid : __ **)

  let monad_leftid =
    __

  (** val monad_rightid : __ **)

  let monad_rightid =
    __

  (** val monad_assoc : __ **)

  let monad_assoc =
    __

  (** val bindUnsized : __ **)

  let bindUnsized =
    __

  (** val bindMonotonic : __ **)

  let bindMonotonic =
    __

  (** val bindMonotonicOpt : __ **)

  let bindMonotonicOpt =
    __

  (** val bindOptMonotonicOpt : __ **)

  let bindOptMonotonicOpt =
    __

  (** val bindMonotonicStrong : __ **)

  let bindMonotonicStrong =
    __

  (** val bindMonotonicOptStrong : __ **)

  let bindMonotonicOptStrong =
    __

  (** val bindOptMonotonic : __ **)

  let bindOptMonotonic =
    __

  (** val semBindUnsized1 : __ **)

  let semBindUnsized1 =
    __

  (** val semBindUnsized2 : __ **)

  let semBindUnsized2 =
    __

  (** val semBindSizeMonotonic : __ **)

  let semBindSizeMonotonic =
    __

  (** val semBindOptSizeMonotonicIncl_r : __ **)

  let semBindOptSizeMonotonicIncl_r =
    __

  (** val semBindSizeMonotonicIncl_r : __ **)

  let semBindSizeMonotonicIncl_r =
    __

  (** val semBindOptSizeMonotonicIncl_l : __ **)

  let semBindOptSizeMonotonicIncl_l =
    __

  (** val semBindSizeMonotonicIncl_l : __ **)

  let semBindSizeMonotonicIncl_l =
    __

  (** val semBindOptSizeOpt_subset_compat : __ **)

  let semBindOptSizeOpt_subset_compat =
    __

  (** val semFmapSize : __ **)

  let semFmapSize =
    __

  (** val semFmap : __ **)

  let semFmap =
    __

  (** val fmapUnsized : __ **)

  let fmapUnsized =
    __

  (** val fmapMonotonic : __ **)

  let fmapMonotonic =
    __

  (** val semChooseSize : __ **)

  let semChooseSize =
    __

  (** val chooseUnsized : __ **)

  let chooseUnsized =
    __

  (** val semChoose : __ **)

  let semChoose =
    __

  (** val semSized : __ **)

  let semSized =
    __

  (** val semSizedSize : __ **)

  let semSizedSize =
    __

  (** val semSized_opt : __ **)

  let semSized_opt =
    __

  (** val semSized_alt : __ **)

  let semSized_alt =
    __

  (** val sizedSizeMonotonic : __ **)

  let sizedSizeMonotonic =
    __

  (** val sizedSizeMonotonicOpt : __ **)

  let sizedSizeMonotonicOpt =
    __

  (** val semResize : __ **)

  let semResize =
    __

  (** val semSizeResize : __ **)

  let semSizeResize =
    __

  (** val unsizedResize : __ **)

  let unsizedResize =
    __

  (** val semSuchThatMaybe_sound' : __ **)

  let semSuchThatMaybe_sound' =
    __

  (** val semSuchThatMaybe_complete : __ **)

  let semSuchThatMaybe_complete =
    __

  (** val promoteVariant : __ **)

  let promoteVariant =
    __

  (** val semPromote : __ **)

  let semPromote =
    __

  (** val semPromoteSize : __ **)

  let semPromoteSize =
    __

  (** val runFmap : __ **)

  let runFmap =
    __

  (** val runPromote : __ **)

  let runPromote =
    __

  (** val semFmapBind : __ **)

  let semFmapBind =
    __

  (** val suchThatMaybeMonotonicOpt : __ **)

  let suchThatMaybeMonotonicOpt =
    __

  (** val semSuchThatMaybe_sound : __ **)

  let semSuchThatMaybe_sound =
    __

  (** val suchThatMaybe_subset_compat : __ **)

  let suchThatMaybe_subset_compat =
    __

  (** val semSuchThatMaybeOpt_sound : __ **)

  let semSuchThatMaybeOpt_sound =
    __

  (** val suchThatMaybeOptMonotonicOpt : __ **)

  let suchThatMaybeOptMonotonicOpt =
    __

  (** val suchThatMaybeOpt_subset_compat : __ **)

  let suchThatMaybeOpt_subset_compat =
    __

  (** val semSuchThatMaybeOpt_complete : __ **)

  let semSuchThatMaybeOpt_complete =
    __

  (** val coq_Functor_G : __ coq_G functor0 **)

  let coq_Functor_G _ _ =
    fmap

  (** val coq_Applicative_G : __ coq_G applicative **)

  let coq_Applicative_G =
    { pure = (fun _ -> returnGen); ap = (fun _ _ -> Obj.magic apGen) }

  (** val coq_Monad_G : __ coq_G monad **)

  let coq_Monad_G =
    { ret = (fun _ -> returnGen); bind = (fun _ _ -> bindGen) }

  type 'a coq_GOpt = 'a option coq_G

  (** val coq_Monad_GOpt : __ coq_GOpt monad **)

  let coq_Monad_GOpt =
    { ret = (fun _ x -> returnGen (Some x)); bind = (fun _ _ -> bindGenOpt) }

  (** val thunkGen : (unit -> 'a1 coq_G) -> 'a1 coq_G **)

  let thunkGen f n r =
    run (f ()) n r

  (** val semThunkGenSize : __ **)

  let semThunkGenSize =
    __

  (** val semThunkGen : __ **)

  let semThunkGen =
    __

  (** val thunkGenUnsized : __ **)

  let thunkGenUnsized =
    __

  (** val thunkGenSizeMonotonic : __ **)

  let thunkGenSizeMonotonic =
    __

  (** val thunkGenSizeMonotonicOpt : __ **)

  let thunkGenSizeMonotonicOpt =
    __

  (** val thunkGenSizeAntiMonotonicNone : __ **)

  let thunkGenSizeAntiMonotonicNone =
    __
 end

module Impl =
 functor (GenLow__0:Sig) ->
 struct
  (** val liftGen :
      ('a1 -> 'a2) -> 'a1 GenLow__0.coq_G -> 'a2 GenLow__0.coq_G **)

  let liftGen f a =
    GenLow__0.bindGen a (fun x -> GenLow__0.returnGen (f x))

  (** val liftGen2 :
      ('a1 -> 'a2 -> 'a3) -> 'a1 GenLow__0.coq_G -> 'a2 GenLow__0.coq_G ->
      'a3 GenLow__0.coq_G **)

  let liftGen2 c m1 m2 =
    GenLow__0.bindGen m1 (fun x1 ->
      GenLow__0.bindGen m2 (fun x2 -> GenLow__0.returnGen (c x1 x2)))

  (** val liftGen3 :
      ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 GenLow__0.coq_G -> 'a2
      GenLow__0.coq_G -> 'a3 GenLow__0.coq_G -> 'a4 GenLow__0.coq_G **)

  let liftGen3 f m1 m2 m3 =
    GenLow__0.bindGen m1 (fun x1 ->
      GenLow__0.bindGen m2 (fun x2 ->
        GenLow__0.bindGen m3 (fun x3 -> GenLow__0.returnGen (f x1 x2 x3))))

  (** val liftGen4 :
      ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5) -> 'a1 GenLow__0.coq_G -> 'a2
      GenLow__0.coq_G -> 'a3 GenLow__0.coq_G -> 'a4 GenLow__0.coq_G -> 'a5
      GenLow__0.coq_G **)

  let liftGen4 f m1 m2 m3 m4 =
    GenLow__0.bindGen m1 (fun x1 ->
      GenLow__0.bindGen m2 (fun x2 ->
        GenLow__0.bindGen m3 (fun x3 ->
          GenLow__0.bindGen m4 (fun x4 -> GenLow__0.returnGen (f x1 x2 x3 x4)))))

  (** val liftGen5 :
      ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 -> 'a6) -> 'a1 GenLow__0.coq_G -> 'a2
      GenLow__0.coq_G -> 'a3 GenLow__0.coq_G -> 'a4 GenLow__0.coq_G -> 'a5
      GenLow__0.coq_G -> 'a6 GenLow__0.coq_G **)

  let liftGen5 f m1 m2 m3 m4 m5 =
    GenLow__0.bindGen m1 (fun x1 ->
      GenLow__0.bindGen m2 (fun x2 ->
        GenLow__0.bindGen m3 (fun x3 ->
          GenLow__0.bindGen m4 (fun x4 ->
            GenLow__0.bindGen m5 (fun x5 ->
              GenLow__0.returnGen (f x1 x2 x3 x4 x5))))))

  (** val sequenceGen :
      'a1 GenLow__0.coq_G list -> 'a1 list GenLow__0.coq_G **)

  let sequenceGen ms =
    foldr (fun m m' ->
      GenLow__0.bindGen m (fun x ->
        GenLow__0.bindGen m' (fun xs -> GenLow__0.returnGen (x :: xs))))
      (GenLow__0.returnGen []) ms

  (** val foldGen :
      ('a1 -> 'a2 -> 'a1 GenLow__0.coq_G) -> 'a2 list -> 'a1 -> 'a1
      GenLow__0.coq_G **)

  let rec foldGen f l a =
    match l with
    | [] -> GenLow__0.returnGen a
    | x :: xs -> GenLow__0.bindGen (f a x) (foldGen f xs)

  (** val oneOf_ :
      'a1 GenLow__0.coq_G -> 'a1 GenLow__0.coq_G list -> 'a1 GenLow__0.coq_G **)

  let oneOf_ def gs =
    GenLow__0.bindGen
      (GenLow__0.choose chooseNat (0, (subn (length gs) (Pervasives.succ 0))))
      (nth1 def gs)

  (** val oneof :
      'a1 GenLow__0.coq_G -> 'a1 GenLow__0.coq_G list -> 'a1 GenLow__0.coq_G **)

  let oneof x =
    deprecate ('o'::('n'::('e'::('o'::('f'::[])))))
      ('o'::('n'::('e'::('O'::('f'::('_'::[])))))) oneOf_ x

  (** val pick :
      'a1 GenLow__0.coq_G -> (int * 'a1 GenLow__0.coq_G) list -> int ->
      int * 'a1 GenLow__0.coq_G **)

  let rec pick def xs n =
    match xs with
    | [] -> (0, def)
    | p :: xs0 ->
      let (k, x) = p in
      if leq (Pervasives.succ n) k then (k, x) else pick def xs0 (subn n k)

  (** val pickDrop :
      (int * 'a1 option GenLow__0.coq_G) list -> int -> (int * 'a1 option
      GenLow__0.coq_G) * (int * 'a1 option GenLow__0.coq_G) list **)

  let rec pickDrop xs n =
    match xs with
    | [] -> ((0, (GenLow__0.returnGen None)), [])
    | p :: xs0 ->
      let (k, x) = p in
      if leq (Pervasives.succ n) k
      then ((k, x), xs0)
      else let (p0, xs') = pickDrop xs0 (subn n k) in (p0, ((k, x) :: xs'))

  (** val sum_fst : (int * 'a1) list -> int **)

  let sum_fst gs =
    foldl (fun t2 p -> addn t2 (fst p)) 0 gs

  (** val freq_ :
      'a1 GenLow__0.coq_G -> (int * 'a1 GenLow__0.coq_G) list -> 'a1
      GenLow__0.coq_G **)

  let freq_ def gs =
    let tot = sum_fst gs in
    GenLow__0.bindGen
      (GenLow__0.choose chooseNat (0, (subn tot (Pervasives.succ 0))))
      (fun n -> snd (pick def gs n))

  (** val frequency :
      'a1 GenLow__0.coq_G -> (int * 'a1 GenLow__0.coq_G) list -> 'a1
      GenLow__0.coq_G **)

  let frequency x =
    deprecate
      ('f'::('r'::('e'::('q'::('u'::('e'::('n'::('c'::('y'::[])))))))))
      ('f'::('r'::('e'::('q'::('_'::[]))))) freq_ x

  (** val backtrackFuel :
      int -> int -> (int * 'a1 option GenLow__0.coq_G) list -> 'a1 option
      GenLow__0.coq_G **)

  let rec backtrackFuel fuel tot gs =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> GenLow__0.returnGen None)
      (fun fuel' ->
      GenLow__0.bindGen
        (GenLow__0.choose chooseNat (0, (subn tot (Pervasives.succ 0))))
        (fun n ->
        let (p, gs') = pickDrop gs n in
        let (k, g) = p in
        GenLow__0.bindGen g (fun ma ->
          match ma with
          | Some a -> GenLow__0.returnGen (Some a)
          | None -> backtrackFuel fuel' (subn tot k) gs')))
      fuel

  (** val backtrack :
      (int * 'a1 option GenLow__0.coq_G) list -> 'a1 option GenLow__0.coq_G **)

  let backtrack gs =
    backtrackFuel (length gs) (sum_fst gs) gs

  (** val vectorOf :
      int -> 'a1 GenLow__0.coq_G -> 'a1 list GenLow__0.coq_G **)

  let vectorOf k g =
    foldr (fun m m' ->
      GenLow__0.bindGen m (fun x ->
        GenLow__0.bindGen m' (fun xs -> GenLow__0.returnGen (x :: xs))))
      (GenLow__0.returnGen []) (nseq k g)

  (** val listOf : 'a1 GenLow__0.coq_G -> 'a1 list GenLow__0.coq_G **)

  let listOf g =
    GenLow__0.sized (fun n ->
      GenLow__0.bindGen (GenLow__0.choose chooseNat (0, n)) (fun k ->
        vectorOf k g))

  (** val elems_ : 'a1 -> 'a1 list -> 'a1 GenLow__0.coq_G **)

  let elems_ def l =
    let n = length l in
    GenLow__0.bindGen
      (GenLow__0.choose chooseNat (0, (subn n (Pervasives.succ 0))))
      (fun n' -> GenLow__0.returnGen (nth n' l def))

  (** val elements : 'a1 -> 'a1 list -> 'a1 GenLow__0.coq_G **)

  let elements x =
    deprecate ('e'::('l'::('e'::('m'::('e'::('n'::('t'::('s'::[]))))))))
      ('e'::('l'::('e'::('m'::('s'::('_'::[])))))) elems_ x

  (** val semLiftGen : __ **)

  let semLiftGen =
    __

  (** val semLiftGenSize : __ **)

  let semLiftGenSize =
    __

  (** val liftGenUnsized : __ **)

  let liftGenUnsized =
    __

  (** val semLiftGen2Size : __ **)

  let semLiftGen2Size =
    __

  (** val semLiftGen2SizeMonotonic : __ **)

  let semLiftGen2SizeMonotonic =
    __

  (** val semLiftGen2Unsized1 : __ **)

  let semLiftGen2Unsized1 =
    __

  (** val semLiftGen2Unsized2 : __ **)

  let semLiftGen2Unsized2 =
    __

  (** val semLiftGen3Size : __ **)

  let semLiftGen3Size =
    __

  (** val liftGen2Unsized : __ **)

  let liftGen2Unsized =
    __

  (** val liftGen2Monotonic : __ **)

  let liftGen2Monotonic =
    __

  (** val semLiftGen4Size : __ **)

  let semLiftGen4Size =
    __

  (** val semLiftGen4SizeMonotonic : __ **)

  let semLiftGen4SizeMonotonic =
    __

  (** val liftGen4Monotonic : __ **)

  let liftGen4Monotonic =
    __

  (** val semLiftGen5Size : __ **)

  let semLiftGen5Size =
    __

  (** val semSequenceGenSize : __ **)

  let semSequenceGenSize =
    __

  (** val semSequenceGenSizeMonotonic : __ **)

  let semSequenceGenSizeMonotonic =
    __

  (** val semVectorOfSize : __ **)

  let semVectorOfSize =
    __

  (** val semVectorOfUnsized : __ **)

  let semVectorOfUnsized =
    __

  (** val vectorOfUnsized : __ **)

  let vectorOfUnsized =
    __

  (** val vectorOfMonotonic : __ **)

  let vectorOfMonotonic =
    __

  (** val semListOfSize : __ **)

  let semListOfSize =
    __

  (** val semListOfUnsized : __ **)

  let semListOfUnsized =
    __

  (** val listOfMonotonic : __ **)

  let listOfMonotonic =
    __

  (** val semOneofSize : __ **)

  let semOneofSize =
    __

  (** val semOneof : __ **)

  let semOneof =
    __

  (** val oneofMonotonic : __ **)

  let oneofMonotonic =
    __

  (** val semElementsSize : __ **)

  let semElementsSize =
    __

  (** val semElements : __ **)

  let semElements =
    __

  (** val elementsUnsized : __ **)

  let elementsUnsized =
    __

  (** val semFrequencySize : __ **)

  let semFrequencySize =
    __

  (** val semFrequency : __ **)

  let semFrequency =
    __

  (** val frequencySizeMonotonic : __ **)

  let frequencySizeMonotonic =
    __

  (** val frequencySizeMonotonic_alt : __ **)

  let frequencySizeMonotonic_alt =
    __

  (** val backtrackSizeMonotonic : __ **)

  let backtrackSizeMonotonic =
    __

  (** val backtrackSizeMonotonicOpt : __ **)

  let backtrackSizeMonotonicOpt =
    __

  (** val semBacktrackSize : __ **)

  let semBacktrackSize =
    __

  (** val bigcup_cons_setI_subset_compat_backtrack : __ **)

  let bigcup_cons_setI_subset_compat_backtrack =
    __

  (** val bigcup_cons_setI_subset_pres_backtrack : __ **)

  let bigcup_cons_setI_subset_pres_backtrack =
    __

  (** val semBacktrack_sound : __ **)

  let semBacktrack_sound =
    __

  (** val semBacktrack_complete : __ **)

  let semBacktrack_complete =
    __

  (** val semFoldGen_right : __ **)

  let semFoldGen_right =
    __

  (** val genPair :
      'a1 GenLow__0.coq_G -> 'a2 GenLow__0.coq_G -> ('a1 * 'a2)
      GenLow__0.coq_G **)

  let genPair ga gb =
    liftGen2 (fun x x0 -> (x, x0)) ga gb

  (** val curry : (('a1 * 'a2) -> 'a3) -> 'a1 -> 'a2 -> 'a3 **)

  let curry f a b =
    f (a, b)

  (** val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3 **)

  let uncurry f = function
  | (a, b) -> f a b

  (** val mergeBinds : __ **)

  let mergeBinds =
    __

  module QcDefaultNotation =
   struct
   end

  (** val semElemsSize : __ **)

  let semElemsSize =
    __

  (** val semOneOfSize : __ **)

  let semOneOfSize =
    __

  (** val semElems : __ **)

  let semElems =
    __

  (** val semOneOf : __ **)

  let semOneOf =
    __
 end

module GenHigh = Impl(GenLow)

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> true
    | _ -> false

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module KeyOrderedType =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module AsciiOT =
 struct
  type t = char

  (** val compare : t -> t -> char compare0 **)

  let compare c d =
    let c0 = N.compare (n_of_ascii c) (n_of_ascii d) in
    (match c0 with
     | Eq -> EQ
     | Lt -> LT
     | Gt -> GT)
 end

module StringOT =
 struct
  type t = char list

  (** val eq_dec : char list -> char list -> bool **)

  let eq_dec =
    string_dec

  type coq_SOrdering =
  | SLT
  | SEQ
  | SGT

  (** val coq_SOrdering_rect : 'a1 -> 'a1 -> 'a1 -> coq_SOrdering -> 'a1 **)

  let coq_SOrdering_rect f f0 f1 = function
  | SLT -> f
  | SEQ -> f0
  | SGT -> f1

  (** val coq_SOrdering_rec : 'a1 -> 'a1 -> 'a1 -> coq_SOrdering -> 'a1 **)

  let coq_SOrdering_rec f f0 f1 = function
  | SLT -> f
  | SEQ -> f0
  | SGT -> f1

  (** val strcmp : char list -> char list -> coq_SOrdering **)

  let rec strcmp s1 s2 =
    match s1 with
    | [] -> (match s2 with
             | [] -> SEQ
             | _::_ -> SLT)
    | ch1::s1' ->
      (match s2 with
       | [] -> SGT
       | ch2::s2' ->
         (match AsciiOT.compare ch1 ch2 with
          | LT -> SLT
          | EQ -> strcmp s1' s2'
          | GT -> SGT))

  (** val compare : t -> t -> char list compare0 **)

  let rec compare s s2 =
    match s with
    | [] -> (match s2 with
             | [] -> EQ
             | _::_ -> LT)
    | a::s0 ->
      (match s2 with
       | [] -> GT
       | c2::s2' ->
         let c = AsciiOT.compare a c2 in
         (match c with
          | LT -> LT
          | EQ -> internal_eq_rew_r_dep a c2 (fun _ -> compare s0 s2') __
          | GT -> GT))
 end

module Raw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  (** val empty : 'a1 t **)

  let empty =
    []

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | [] -> false
  | p :: l ->
    let (k', _) = p in
    (match X.compare k k' with
     | LT -> false
     | EQ -> true
     | GT -> mem k l)

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_mem

  (** val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rect k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rec k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rec k f f0 f1 f2 l _res r0)

  (** val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec mem_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t2, e) = p in
       let f7 = f6 t2 e l __ in
       let f8 = fun _ _ -> let hrec = mem_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t2 e l __ in
       let f10 = f4 t2 e l __ in
       (match X.compare k t2 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let mem_rec =
    mem_rect

  (** val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem **)

  let coq_R_mem_correct k s _res =
    Obj.magic mem_rect k (fun y _ _ _ -> R_mem_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_mem_3 (y, y0, y1, y2, (mem k y2),
      (y6 (mem k y2) __))) s _res __

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | [] -> None
  | p :: s' ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find k s')

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
     * 'elt coq_R_find

  (** val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rect k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rect k f f0 f1 f2 s' _res r0)

  (** val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rec k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rec k f f0 f1 f2 s' _res r0)

  (** val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec find_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t2, e) = p in
       let f7 = f6 t2 e l __ in
       let f8 = fun _ _ ->
         let hrec = find_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t2 e l __ in
       let f10 = f4 t2 e l __ in
       (match X.compare k t2 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let find_rec =
    find_rect

  (** val coq_R_find_correct :
      key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find **)

  let coq_R_find_correct k s _res =
    Obj.magic find_rect k (fun y _ _ _ -> R_find_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_find_3 (y, y0, y1, y2, (find k y2),
      (y6 (find k y2) __))) s _res __

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | [] -> (k, x) :: []
  | p :: l ->
    let (k', y) = p in
    (match X.compare k k' with
     | LT -> (k, x) :: s
     | EQ -> (k, x) :: l
     | GT -> (k', y) :: (add k x l))

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_add

  (** val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rect k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rect k x f f0 f1 f2 l _res r0)

  (** val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rec k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rec k x f f0 f1 f2 l _res r0)

  (** val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec add_rect k x f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t2, e) = p in
       let f7 = f6 t2 e l __ in
       let f8 = fun _ _ ->
         let hrec = add_rect k x f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t2 e l __ in
       let f10 = f4 t2 e l __ in
       (match X.compare k t2 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let add_rec =
    add_rect

  (** val coq_R_add_correct :
      key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add **)

  let coq_R_add_correct k x s _res =
    add_rect k x (fun y _ _ _ -> R_add_0 y) (fun y y0 y1 y2 _ _ _ _ _ ->
      R_add_1 (y, y0, y1, y2)) (fun y y0 y1 y2 _ _ _ _ _ -> R_add_2 (y, y0,
      y1, y2)) (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_add_3 (y, y0, y1, y2,
      (add k x y2), (y6 (add k x y2) __))) s _res __

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | [] -> []
  | p :: l ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> (k', x) :: (remove k l))

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_remove

  (** val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rect k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rec k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rec k f f0 f1 f2 l _res r0)

  (** val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec remove_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t2, e) = p in
       let f7 = f6 t2 e l __ in
       let f8 = fun _ _ ->
         let hrec = remove_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t2 e l __ in
       let f10 = f4 t2 e l __ in
       (match X.compare k t2 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let remove_rec =
    remove_rect

  (** val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove **)

  let coq_R_remove_correct k s _res =
    Obj.magic remove_rect k (fun y _ _ _ -> R_remove_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_remove_3 (y, y0, y1, y2,
      (remove k y2), (y6 (remove k y2) __))) s _res __

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | [] -> acc
    | p :: m' -> let (k, e) = p in fold f m' (f k e acc)

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
     * ('elt, 'a) coq_R_fold

  (** val coq_R_fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rect f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0
      (coq_R_fold_rect f f0 f1 m' (f k e acc) _res r0)

  (** val coq_R_fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rec f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0 (coq_R_fold_rec f f0 f1 m' (f k e acc) _res r0)

  (** val fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let rec fold_rect f1 f0 f m acc =
    let f2 = f0 m acc in
    let f3 = f m acc in
    (match m with
     | [] -> f2 __
     | p :: l ->
       let (t2, e) = p in
       let f4 = f3 t2 e l __ in
       let hrec = fold_rect f1 f0 f l (f1 t2 e acc) in f4 hrec)

  (** val fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let fold_rec =
    fold_rect

  (** val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold **)

  let coq_R_fold_correct f m acc _res =
    fold_rect f (fun y y0 _ _ _ -> R_fold_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 _ _ -> R_fold_1 (y, y0, y1, y2, y3,
      (fold f y3 (f y1 y2 y0)), (y5 (fold f y3 (f y1 y2 y0)) __))) m acc _res
      __

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | [] -> (match m' with
             | [] -> true
             | _ :: _ -> false)
    | p :: l ->
      let (x, e) = p in
      (match m' with
       | [] -> false
       | p0 :: l' ->
         let (x', e') = p0 in
         (match X.compare x x' with
          | EQ -> (&&) (cmp e e') (equal cmp l l')
          | _ -> false))

  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * X.t compare0
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

  (** val coq_R_equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rect cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e, l, x', e', l', _res, r0) ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rect cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e, l, x', e', l', _x) ->
    f1 m m' x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val coq_R_equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rec cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e, l, x', e', l', _res, r0) ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rec cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e, l, x', e', l', _x) ->
    f1 m m' x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let rec equal_rect cmp f2 f1 f0 f m m' =
    let f3 = f2 m m' in
    let f4 = f1 m m' in
    let f5 = f0 m m' in
    let f6 = f m m' in
    let f7 = f6 m __ in
    let f8 = f7 m' __ in
    (match m with
     | [] -> let f9 = f3 __ in (match m' with
                                | [] -> f9 __
                                | _ :: _ -> f8 __)
     | p :: l ->
       let (t2, e) = p in
       let f9 = f5 t2 e l __ in
       let f10 = f4 t2 e l __ in
       (match m' with
        | [] -> f8 __
        | p0 :: l0 ->
          let (t3, e0) = p0 in
          let f11 = f9 t3 e0 l0 __ in
          let f12 = let _x = X.compare t2 t3 in f11 _x __ in
          let f13 = f10 t3 e0 l0 __ in
          let f14 = fun _ _ ->
            let hrec = equal_rect cmp f2 f1 f0 f l l0 in f13 __ __ hrec
          in
          (match X.compare t2 t3 with
           | EQ -> f14 __ __
           | _ -> f12 __)))

  (** val equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let equal_rec =
    equal_rect

  (** val coq_R_equal_correct :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal **)

  let coq_R_equal_correct cmp m m' _res =
    equal_rect cmp (fun y y0 _ _ _ _ -> R_equal_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 _ _ -> R_equal_1 (y, y0, y1,
      y2, y3, y5, y6, y7, (equal cmp y3 y7), (y11 (equal cmp y3 y7) __)))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ _ _ -> R_equal_2 (y, y0, y1, y2,
      y3, y5, y6, y7, y9)) (fun y y0 y1 _ y3 _ _ _ _ -> R_equal_3 (y, y0, y1,
      y3)) m m' _res __

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f e)) :: (map f m')

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f k e)) :: (mapi f m')

  (** val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list **)

  let option_cons k o l =
    match o with
    | Some e -> (k, e) :: l
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | [] -> []
  | p :: l -> let (k, e) = p in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | [] -> []
  | p :: l' ->
    let (k, e') = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | [] -> map2_r f
  | p :: l ->
    let (k, e) = p in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let rec combine m = match m with
  | [] -> map (fun e' -> (None, (Some e')))
  | p :: l ->
    let (k, e) = p in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e0 -> ((Some e0), None)) m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> (k, ((Some e), None)) :: (combine l m')
       | EQ -> (k, ((Some e), (Some e'))) :: (combine l l')
       | GT -> (k', (None, (Some e'))) :: (combine_aux l'))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
      (key * 'a3) list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 []

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> (match o' with
               | Some _ -> Some (o, o')
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module type Int =
 sig
  type t

  val i2z : t -> int

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int =
 struct
  type t = int

  (** val _0 : int **)

  let _0 =
    0

  (** val _1 : int **)

  let _1 =
    1

  (** val _2 : int **)

  let _2 =
    ((fun p->2*p) 1)

  (** val _3 : int **)

  let _3 =
    ((fun p->1+2*p) 1)

  (** val add : int -> int -> int **)

  let add =
    Z.add

  (** val opp : int -> int **)

  let opp =
    Z.opp

  (** val sub : int -> int -> int **)

  let sub =
    Z.sub

  (** val mul : int -> int -> int **)

  let mul =
    Z.mul

  (** val max : int -> int -> int **)

  let max =
    Z.max

  (** val eqb : int -> int -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : int -> int -> bool **)

  let ltb =
    Z.ltb

  (** val leb : int -> int -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : int -> int -> bool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then true else false

  (** val ge_lt_dec : int -> int -> bool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then false else true

  (** val i2z : t -> int **)

  let i2z n =
    n
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t3, k, e, t4, t5) ->
    f0 t3 (tree_rect f f0 t3) k e t4 (tree_rect f f0 t4) t5

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t3, k, e, t4, t5) ->
    f0 t3 (tree_rec f f0 t3) k e t4 (tree_rec f f0 t4) t5

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> int **)

  let rec cardinal = function
  | Leaf -> 0
  | Node (l, _, _, r, _) -> Pervasives.succ (add (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _, _) -> false

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (l, y, _, r, _) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ -> true
     | GT -> mem x r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x = function
  | Leaf -> None
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ -> Some d
     | GT -> find x r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x e r =
    Node (l, x, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x d r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.add hr I._2)
    then (match l with
          | Leaf -> assert_false l x d r
          | Node (ll, lx, ld, lr, _) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx ld (create lr x d r)
            else (match lr with
                  | Leaf -> assert_false l x d r
                  | Node (lrl, lrx, lrd, lrr, _) ->
                    create (create ll lx ld lrl) lrx lrd (create lrr x d r)))
    else if I.gt_le_dec hr (I.add hl I._2)
         then (match r with
               | Leaf -> assert_false l x d r
               | Node (rl, rx, rd, rr, _) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x d rl) rx rd rr
                 else (match rl with
                       | Leaf -> assert_false l x d r
                       | Node (rll, rlx, rld, rlr, _) ->
                         create (create l x d rll) rlx rld
                           (create rlr rx rd rr)))
         else create l x d r

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x d = function
  | Leaf -> Node (Leaf, x, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d l) y d' r
     | EQ -> Node (l, y, d, r, h)
     | GT -> bal l y d' (add x d r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1) **)

  let rec remove_min l x d r =
    match l with
    | Leaf -> (r, (x, d))
    | Node (ll, lx, ld, lr, _) ->
      let (l', m) = remove_min ll lx ld lr in ((bal l' x d r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let (s2', p) = remove_min l2 x2 d2 r2 in
         let (x, d) = p in bal s1 x d s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d r
     | EQ -> merge l r
     | GT -> bal l y d (remove x r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d ->
      let rec join_aux r = match r with
      | Leaf -> add x d l
      | Node (rl, rx, rd, rr, rh) ->
        if I.gt_le_dec lh (I.add rh I._2)
        then bal ll lx ld (join lr x d r)
        else if I.gt_le_dec rh (I.add lh I._2)
             then bal (join_aux rl) rx rd rr
             else create l x d r
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t2 =
    t2.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t2 =
    t2.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t2 =
    t2.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d, r, _) -> elements_aux ((x, d) :: (elements_aux acc r)) l

  (** val elements : 'a1 tree -> (key * 'a1) list **)

  let elements m =
    elements_aux [] m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d, r, _) -> fold f r (f x d (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e0, t2, e1) -> f0 k e0 t2 e1 (enumeration_rect f f0 e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e0, t2, e1) -> f0 k e0 t2 e1 (enumeration_rec f f0 e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x, d, r, _) -> cons l (More (x, d, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d1 cont = function
  | End -> false
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> if cmp d1 d2 then cont (cons r2 e3) else false
     | _ -> false)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> true
  | More (_, _, _, _) -> false

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((map f l), x, (f d), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((mapi f l), x, (f x d), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, _) ->
    (match f x d with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d o -> f (Some d) o)
      (map_option (fun _ d -> f (Some d) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem

    (** val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rect x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rec x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    (** val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rect x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rec x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

    (** val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (x, x0, x1, x2) -> f x x0 x1 x2 __ __ __
    | R_bal_1 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_2 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_4 (x, x0, x1, x2) -> f3 x x0 x1 x2 __ __ __ __ __
    | R_bal_5 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_6 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_7 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_8 (x, x0, x1, x2) -> f7 x x0 x1 x2 __ __ __ __

    (** val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rec f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (x, x0, x1, x2) -> f x x0 x1 x2 __ __ __
    | R_bal_1 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_2 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_4 (x, x0, x1, x2) -> f3 x x0 x1 x2 __ __ __ __ __
    | R_bal_5 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_6 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_7 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_8 (x, x0, x1, x2) -> f7 x x0 x1 x2 __ __ __ __

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    (** val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rect x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 r0 _res r1)

    (** val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rec x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree * (key * 'elt))
       * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

    (** val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rect f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r0) -> f l x d r0 __
    | R_remove_min_1 (l, x, d, r0, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r0 ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rect f f0 ll lx ld lr _res r1) l' m __

    (** val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rec f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r0) -> f l x d r0 __
    | R_remove_min_1 (l, x, d, r0, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r0 ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rec f f0 ll lx ld lr _res r1) l' m __

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key * 'elt) * key * 'elt

    (** val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rect f f0 f1 _ _ _ = function
    | R_merge_0 (x, x0) -> f x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
                 x13, x14) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __

    (** val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rec f f0 f1 _ _ _ = function
    | R_merge_0 (x, x0) -> f x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
                 x13, x14) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove

    (** val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rect x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rec x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key * 'elt)

    (** val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rect f f0 f1 _ _ _ = function
    | R_concat_0 (x, x0) -> f x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __

    (** val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rec f f0 f1 _ _ _ = function
    | R_concat_0 (x, x0) -> f x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    (** val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rect x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 r0 _res r1) rl o rr __

    (** val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rec x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 r0 _res r1) rl o rr __

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    (** val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rect f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)

    (** val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rec f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)

    type ('elt, 'x0, 'x) coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'x0 tree
    | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
       * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt

    (** val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key * 'a1) list **)

    let rec flatten_e = function
    | End -> []
    | More (x, e0, t2, r) -> (x, e0) :: (app (elements t2) (flatten_e r))
   end
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty m =
    Raw.is_empty (this m)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add x e m =
    Raw.add x e (this m)

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove x m =
    Raw.remove x (this m)

  (** val mem : key -> 'a1 t -> bool **)

  let mem x m =
    Raw.mem x (this m)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find x m =
    Raw.find x (this m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Raw.map f (this m)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    Raw.mapi f (this m)

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 f m m' =
    Raw.map2 f (this m) (this m')

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements m =
    Raw.elements (this m)

  (** val cardinal : 'a1 t -> int **)

  let cardinal m =
    Raw.cardinal (this m)

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    Raw.fold f (this m) i

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    Raw.equal cmp (this m) (this m')
 end

module Make =
 functor (X:OrderedType) ->
 IntMake(Z_as_Int)(X)

module Map = Make(StringOT)

type state = { maxSuccessTests : int; maxDiscardedTests : int;
               maxShrinkNo : int; computeSize : (int -> int -> int);
               numSuccessTests : int; numDiscardedTests : int;
               labels : int Map.t; expectedFailure : bool;
               randomSeed0 : randomSeed; numSuccessShrinks : int;
               numTryShrinks : int }

(** val maxSuccessTests : state -> int **)

let maxSuccessTests x = x.maxSuccessTests

(** val maxDiscardedTests : state -> int **)

let maxDiscardedTests x = x.maxDiscardedTests

(** val computeSize : state -> int -> int -> int **)

let computeSize x = x.computeSize

(** val numSuccessTests : state -> int **)

let numSuccessTests x = x.numSuccessTests

(** val numDiscardedTests : state -> int **)

let numDiscardedTests x = x.numDiscardedTests

(** val labels : state -> int Map.t **)

let labels x = x.labels

(** val expectedFailure : state -> bool **)

let expectedFailure x = x.expectedFailure

(** val randomSeed0 : state -> randomSeed **)

let randomSeed0 x = x.randomSeed0

(** val numSuccessShrinks : state -> int **)

let numSuccessShrinks x = x.numSuccessShrinks

(** val updTryShrinks : state -> (int -> int) -> state **)

let updTryShrinks st f =
  let { maxSuccessTests = mst; maxDiscardedTests = mdt; maxShrinkNo = ms;
    computeSize = cs; numSuccessTests = nst; numDiscardedTests = ndt;
    labels = ls; expectedFailure = e; randomSeed0 = r; numSuccessShrinks =
    nss; numTryShrinks = nts } = st
  in
  { maxSuccessTests = mst; maxDiscardedTests = mdt; maxShrinkNo = ms;
  computeSize = cs; numSuccessTests = nst; numDiscardedTests = ndt; labels =
  ls; expectedFailure = e; randomSeed0 = r; numSuccessShrinks = nss;
  numTryShrinks = (f nts) }

(** val updSuccessShrinks : state -> (int -> int) -> state **)

let updSuccessShrinks st f =
  let { maxSuccessTests = mst; maxDiscardedTests = mdt; maxShrinkNo = ms;
    computeSize = cs; numSuccessTests = nst; numDiscardedTests = ndt;
    labels = ls; expectedFailure = e; randomSeed0 = r; numSuccessShrinks =
    nss; numTryShrinks = nts } = st
  in
  { maxSuccessTests = mst; maxDiscardedTests = mdt; maxShrinkNo = ms;
  computeSize = cs; numSuccessTests = nst; numDiscardedTests = ndt; labels =
  ls; expectedFailure = e; randomSeed0 = r; numSuccessShrinks = (f nss);
  numTryShrinks = nts }

type callbackKind =
| Counterexample
| NotCounterexample

type smallResult =
| MkSmallResult of bool option * bool * char list * bool * char list list
   * char list option

type callback =
| PostTest of callbackKind * (state -> randomSeed -> smallResult -> int)
| PostFinalFailure of callbackKind
   * (state -> randomSeed -> smallResult -> int)

type result = { ok : bool option; expect : bool; reason : char list;
                interrupted : bool; stamp : char list list;
                callbacks : callback list; result_tag : char list option }

(** val ok : result -> bool option **)

let ok x = x.ok

(** val expect : result -> bool **)

let expect x = x.expect

(** val result_tag : result -> char list option **)

let result_tag x = x.result_tag

(** val succeeded : result **)

let succeeded =
  { ok = (Some true); expect = true; reason = []; interrupted = false;
    stamp = []; callbacks = []; result_tag = None }

(** val failed : result **)

let failed =
  { ok = (Some false); expect = true; reason = []; interrupted = false;
    stamp = []; callbacks = []; result_tag = None }

(** val rejected : result **)

let rejected =
  { ok = None; expect = true; reason = []; interrupted = false; stamp = [];
    callbacks = []; result_tag = None }

(** val updReason : result -> char list -> result **)

let updReason r s' =
  let { ok = o; expect = e; reason = _; interrupted = i; stamp = s;
    callbacks = c; result_tag = t2 } = r
  in
  { ok = o; expect = e; reason = s'; interrupted = i; stamp = s; callbacks =
  c; result_tag = t2 }

(** val addCallback : result -> callback -> result **)

let addCallback res c =
  let { ok = o; expect = e; reason = r; interrupted = i; stamp = s;
    callbacks = cs; result_tag = t2 } = res
  in
  { ok = o; expect = e; reason = r; interrupted = i; stamp = s; callbacks =
  (c :: cs); result_tag = t2 }

type qProp =
  result rose
  (* singleton inductive, whose constructor was MkProp *)

(** val unProp : qProp -> result rose **)

let unProp q =
  q

type checker = qProp GenLow.coq_G

type 'a checkable =
  'a -> checker
  (* singleton inductive, whose constructor was Build_Checkable *)

(** val checker0 : 'a1 checkable -> 'a1 -> checker **)

let checker0 checkable0 =
  checkable0

(** val liftBool : bool -> result **)

let liftBool = function
| true -> succeeded
| false ->
  updReason failed
    ('F'::('a'::('l'::('s'::('i'::('f'::('i'::('a'::('b'::('l'::('e'::[])))))))))))

(** val mapProp : 'a1 checkable -> (qProp -> qProp) -> 'a1 -> checker **)

let mapProp x f prop0 =
  GenLow.fmap f (checker0 x prop0)

(** val mapRoseResult :
    'a1 checkable -> (result rose -> result rose) -> 'a1 -> checker **)

let mapRoseResult =
  mapProp

(** val mapTotalResult :
    'a1 checkable -> (result -> result) -> 'a1 -> checker **)

let mapTotalResult x f =
  mapRoseResult x (fmapRose f)

(** val testResult : result checkable **)

let testResult r =
  GenLow.returnGen (returnRose r)

(** val testBool : bool checkable **)

let testBool b =
  checker0 testResult (liftBool b)

(** val testUnit : unit checkable **)

let testUnit _ =
  checker0 testResult rejected

(** val testChecker : checker checkable **)

let testChecker x =
  x

(** val props' :
    'a1 checkable -> int -> ('a2 -> 'a1) -> ('a2 -> 'a2 list) -> 'a2 ->
    checker rose **)

let rec props' t2 n pf shrinker x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> MkRose ((checker0 t2 (pf x)), (lazy [])))
    (fun n' -> MkRose ((checker0 t2 (pf x)), (lazy
    (map (props' t2 n' pf shrinker) (shrinker x)))))
    n

(** val props :
    'a1 checkable -> ('a2 -> 'a1) -> ('a2 -> 'a2 list) -> 'a2 -> checker rose **)

let props h pf shrinker x =
  props' h (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    pf shrinker x

(** val shrinking :
    'a1 checkable -> ('a2 -> 'a2 list) -> 'a2 -> ('a2 -> 'a1) -> checker **)

let shrinking h shrinker x0 pf =
  GenLow.fmap (fun x -> joinRose (fmapRose unProp x))
    (GenLow.promote (props h pf shrinker x0))

(** val callback0 : 'a1 checkable -> callback -> 'a1 -> checker **)

let callback0 h cb =
  mapTotalResult h (fun r -> addCallback r cb)

(** val printTestCase : 'a1 checkable -> char list -> 'a1 -> checker **)

let printTestCase h s p =
  callback0 h (PostFinalFailure (Counterexample, (fun _ _ _ -> trace s 0))) p

(** val cover :
    'a1 checkable -> bool -> int -> char list -> 'a1 -> checker **)

let cover x b _ s =
  if b
  then mapTotalResult x (fun res ->
         let { ok = o; expect = e; reason = r; interrupted = i; stamp = st;
           callbacks = c; result_tag = t2 } = res
         in
         { ok = o; expect = e; reason = r; interrupted = i; stamp =
         (s :: st); callbacks = c; result_tag = t2 })
  else checker0 x

(** val classify : 'a1 checkable -> bool -> char list -> 'a1 -> checker **)

let classify x b s =
  cover x b 0 s

(** val label : 'a1 checkable -> char list -> 'a1 -> checker **)

let label x s =
  classify x true s

(** val collect : 'a1 show -> 'a2 checkable -> 'a1 -> 'a2 -> checker **)

let collect h x x0 =
  label x (show0 h x0)

(** val forAllShrink :
    'a2 checkable -> 'a1 show -> 'a1 GenLow.coq_G -> ('a1 -> 'a1 list) ->
    ('a1 -> 'a2) -> checker **)

let forAllShrink x h gen shrinker pf =
  GenLow.bindGen gen (fun x0 ->
    shrinking testChecker shrinker x0 (fun x' ->
      printTestCase x (append (show0 h x') newline) (pf x')))

(** val divn : int -> int -> int **)

let divn = (/)

(** val modn : int -> int -> int **)

let modn = (fun x y -> x mod y)

(** val dvdn : int -> int -> bool **)

let dvdn d m =
  eq_op nat_eqType (Obj.magic modn m d) (Obj.magic 0)

(** val gte : int -> int -> bool **)

let gte = (>=)

type args = { replay : (randomSeed * int) option; maxSuccess : int;
              maxDiscard : int; maxShrinks : int; maxSize : int;
              chatty : bool; compFun : (int -> int -> int -> int -> int) }

(** val replay : args -> (randomSeed * int) option **)

let replay x = x.replay

(** val maxSuccess : args -> int **)

let maxSuccess x = x.maxSuccess

(** val maxDiscard : args -> int **)

let maxDiscard x = x.maxDiscard

(** val maxShrinks : args -> int **)

let maxShrinks x = x.maxShrinks

(** val maxSize : args -> int **)

let maxSize x = x.maxSize

(** val compFun : args -> int -> int -> int -> int -> int **)

let compFun x = x.compFun

type result0 =
| Success of int * int * (char list * int) list * char list
| GaveUp of int * (char list * int) list * char list
| Failure of int * int * int * randomSeed * int * char list
   * (char list * int) list * char list
| NoExpectedFailure of int * (char list * int) list * char list

(** val defSize : int **)

let defSize = 7

(** val roundTo : int -> int -> int **)

let roundTo n m =
  mul (Nat.div n m) m

(** val computeSizeFun : int -> int -> int -> int -> int **)

let computeSizeFun maxSize0 maxSuccess0 n d =
  if (||) ((||) (leq (roundTo n maxSize0) maxSuccess0) (leq maxSuccess0 n))
       (dvdn maxSuccess0 maxSize0)
  then minn
         (addn (modn n maxSize0)
           (divn d (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ 0)))))))))))) maxSize0
  else minn
         (divn (muln (modn n maxSize0) maxSize0)
           (addn (modn maxSuccess0 maxSize0)
             (divn d (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ 0))))))))))))) maxSize0

(** val computeSize' : args -> int -> int -> int **)

let computeSize' a n d =
  computeSizeFun a.maxSize a.maxSuccess n d

(** val at0 : (int -> int -> int) -> int -> int -> int -> int **)

let at0 f s n d =
  if (&&) ((=) n 0) ((=) d 0) then s else f n d

(** val insertBy : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec insertBy compare1 x l = match l with
| [] -> x :: []
| h :: t2 -> if compare1 x h then x :: l else h :: (insertBy compare1 x t2)

(** val insSortBy : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec insSortBy compare1 = function
| [] -> []
| h :: t2 -> insertBy compare1 h (insSortBy compare1 t2)

(** val summary : state -> (char list * int) list **)

let summary st =
  let res = Map.fold (fun key0 elem acc -> (key0, elem) :: acc) st.labels []
  in
  insSortBy (fun x y -> leq (snd y) (snd x)) res

(** val doneTesting : state -> (int -> randomSeed -> qProp) -> result0 **)

let doneTesting st _ =
  if st.expectedFailure
  then Success ((addn st.numSuccessTests (Pervasives.succ 0)),
         st.numDiscardedTests, (summary st),
         (append
           ('+'::('+'::('+'::(' '::('P'::('a'::('s'::('s'::('e'::('d'::(' '::[])))))))))))
           (append (show0 showNat st.numSuccessTests)
             (append
               (' '::('t'::('e'::('s'::('t'::('s'::(' '::('('::[]))))))))
               (append (show0 showNat st.numDiscardedTests)
                 (' '::('d'::('i'::('s'::('c'::('a'::('r'::('d'::('s'::(')'::[])))))))))))))))
  else NoExpectedFailure (st.numSuccessTests, (summary st),
         (append
           ('*'::('*'::('*'::(' '::('F'::('a'::('i'::('l'::('e'::('d'::('!'::(' '::('P'::('a'::('s'::('s'::('e'::('d'::(' '::[])))))))))))))))))))
           (append (show0 showNat st.numSuccessTests)
             (' '::('t'::('e'::('s'::('t'::('s'::(' '::('('::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('F'::('a'::('i'::('l'::('u'::('r'::('e'::(')'::[]))))))))))))))))))))))))))))

(** val giveUp : state -> (int -> randomSeed -> qProp) -> result0 **)

let giveUp st _ =
  GaveUp (st.numSuccessTests, (summary st),
    (append
      ('*'::('*'::('*'::(' '::('G'::('a'::('v'::('e'::(' '::('u'::('p'::('!'::(' '::('P'::('a'::('s'::('s'::('e'::('d'::(' '::('o'::('n'::('l'::('y'::(' '::[])))))))))))))))))))))))))
      (append (show0 showNat st.numSuccessTests)
        (append (' '::('t'::('e'::('s'::('t'::('s'::[]))))))
          (append newline
            (append
              ('D'::('i'::('s'::('c'::('a'::('r'::('d'::('e'::('d'::(':'::(' '::[])))))))))))
              (show0 showNat st.numDiscardedTests)))))))

(** val callbackPostTest : randomSeed -> state -> result -> int **)

let callbackPostTest rs st res =
  let { ok = o; expect = e; reason = r; interrupted = i; stamp = s;
    callbacks = c; result_tag = t2 } = res
  in
  fold_left (fun acc callback1 ->
    match callback1 with
    | PostTest (_, call) ->
      addn (call st rs (MkSmallResult (o, e, r, i, s, t2))) acc
    | PostFinalFailure (_, _) -> acc) c 0

(** val callbackPostFinalFailure : randomSeed -> state -> result -> int **)

let callbackPostFinalFailure rs st res =
  let { ok = o; expect = e; reason = r; interrupted = i; stamp = s;
    callbacks = c; result_tag = t2 } = res
  in
  fold_left (fun acc callback1 ->
    match callback1 with
    | PostTest (_, _) -> acc
    | PostFinalFailure (_, call) ->
      addn (call st rs (MkSmallResult (o, e, r, i, s, t2))) acc) c 0

(** val localMin : randomSeed -> state -> result rose -> int * result **)

let rec localMin rs st = function
| MkRose (res, ts) ->
  let rec localMin' st0 = function
  | [] ->
    let zero0 = callbackPostFinalFailure rs st0 res in
    ((addn st0.numSuccessShrinks zero0), res)
  | r' :: ts' ->
    let MkRose (res', _) = r' in
    let zero0 = callbackPostTest rs st0 res in
    (match res'.ok with
     | Some x ->
       let consistent_tags =
         match res.result_tag with
         | Some t2 ->
           (match res'.result_tag with
            | Some t3 -> is_left (string_dec t2 t3)
            | None -> false)
         | None -> (match res'.result_tag with
                    | Some _ -> false
                    | None -> true)
       in
       if (&&) (negb x) consistent_tags
       then localMin rs
              (updSuccessShrinks st0 (fun x0 ->
                addn (addn x0 (Pervasives.succ 0)) zero0)) r'
       else localMin'
              (updTryShrinks st0 (fun x0 -> addn x0 (Pervasives.succ 0))) ts'
     | None ->
       localMin' (updTryShrinks st0 (fun x -> addn x (Pervasives.succ 0))) ts')
  in localMin' st (force ts)

(** val runATest : state -> (int -> randomSeed -> qProp) -> int -> result0 **)

let rec runATest st f maxSteps =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> giveUp st f)
    (fun maxSteps' ->
    let size = st.computeSize st.numSuccessTests st.numDiscardedTests in
    let (rnd1, rnd2) = randomSplit st.randomSeed0 in
    let test0 = fun st0 ->
      if gte st0.numSuccessTests st0.maxSuccessTests
      then doneTesting st0 f
      else if gte st0.numDiscardedTests st0.maxDiscardedTests
           then giveUp st0 f
           else runATest st0 f maxSteps'
    in
    let { maxSuccessTests = mst; maxDiscardedTests = mdt; maxShrinkNo = ms;
      computeSize = cs; numSuccessTests = nst; numDiscardedTests = ndt;
      labels = ls; expectedFailure = _; randomSeed0 = r; numSuccessShrinks =
      nss; numTryShrinks = nts } = st
    in
    let rnd1_copy = copySeed rnd1 in
    let MkRose (res, ts) = f size rnd1 in
    let res_cb = callbackPostTest rnd1_copy st res in
    let { ok = ok0; expect = e; reason = reas; interrupted = _; stamp = s;
      callbacks = _; result_tag = t2 } = res
    in
    (match ok0 with
     | Some x ->
       if x
       then let ls' =
              match s with
              | [] -> ls
              | _ :: _ ->
                let s_to_add =
                  ShowFunctions.string_concat
                    (ShowFunctions.intersperse (' '::(','::(' '::[]))) s)
                in
                (match Map.find s_to_add ls with
                 | Some k -> Map.add s_to_add (addn k (Pervasives.succ 0)) ls
                 | None ->
                   Map.add s_to_add (addn res_cb (Pervasives.succ 0)) ls)
            in
            test0 { maxSuccessTests = mst; maxDiscardedTests = mdt;
              maxShrinkNo = ms; computeSize = cs; numSuccessTests =
              (addn nst (Pervasives.succ 0)); numDiscardedTests = ndt;
              labels = ls'; expectedFailure = e; randomSeed0 = rnd2;
              numSuccessShrinks = nss; numTryShrinks = nts }
       else let tag_text =
              match t2 with
              | Some s0 ->
                append ('T'::('a'::('g'::(':'::(' '::[]))))) (append s0 nl)
              | None -> []
            in
            let pre =
              if res.expect
              then '*'::('*'::('*'::(' '::('F'::('a'::('i'::('l'::('e'::('d'::(' '::[]))))))))))
              else '+'::('+'::('+'::(' '::('F'::('a'::('i'::('l'::('e'::('d'::(' '::('('::('a'::('s'::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(')'::(' '::[]))))))))))))))))))))))))
            in
            let (numShrinks, _) = localMin rnd1_copy st (MkRose (res, ts)) in
            let suf =
              append ('a'::('f'::('t'::('e'::('r'::(' '::[]))))))
                (append (show0 showNat (Pervasives.succ nst))
                  (append
                    (' '::('t'::('e'::('s'::('t'::('s'::(' '::('a'::('n'::('d'::(' '::[])))))))))))
                    (append (show0 showNat numShrinks)
                      (append
                        (' '::('s'::('h'::('r'::('i'::('n'::('k'::('s'::('.'::(' '::('('::[])))))))))))
                        (append (show0 showNat ndt)
                          (' '::('d'::('i'::('s'::('c'::('a'::('r'::('d'::('s'::(')'::[])))))))))))))))
            in
            if negb res.expect
            then Success ((addn nst (Pervasives.succ 0)), ndt, (summary st),
                   (append tag_text (append pre suf)))
            else Failure ((addn nst (Pervasives.succ 0)), numShrinks, ndt, r,
                   size, (append tag_text (append pre suf)), (summary st),
                   reas)
     | None ->
       let ls' =
         match s with
         | [] -> ls
         | _ :: _ ->
           let s_to_add =
             append
               ('('::('D'::('i'::('s'::('c'::('a'::('r'::('d'::('e'::('d'::(')'::(' '::[]))))))))))))
               (ShowFunctions.string_concat
                 (ShowFunctions.intersperse (' '::(','::(' '::[]))) s))
           in
           (match Map.find s_to_add ls with
            | Some k -> Map.add s_to_add (addn k (Pervasives.succ 0)) ls
            | None -> Map.add s_to_add (addn res_cb (Pervasives.succ 0)) ls)
       in
       test0 { maxSuccessTests = mst; maxDiscardedTests = mdt; maxShrinkNo =
         ms; computeSize = cs; numSuccessTests = nst; numDiscardedTests =
         (Pervasives.succ ndt); labels = ls'; expectedFailure = e;
         randomSeed0 = rnd2; numSuccessShrinks = nss; numTryShrinks = nts }))
    maxSteps

(** val test : state -> (int -> randomSeed -> qProp) -> result0 **)

let test st f =
  if gte st.numSuccessTests st.maxSuccessTests
  then doneTesting st f
  else if gte st.numDiscardedTests st.maxDiscardedTests
       then giveUp st f
       else let maxSteps = addn st.maxSuccessTests st.maxDiscardedTests in
            runATest st f maxSteps

(** val quickCheckWith : 'a1 checkable -> args -> 'a1 -> result0 **)

let quickCheckWith x a p =
  match a.replay with
  | Some p0 ->
    let (rnd, s) = p0 in
    let computeFun = at0 (computeSize' a) s in
    test { maxSuccessTests = a.maxSuccess; maxDiscardedTests = a.maxDiscard;
      maxShrinkNo = a.maxShrinks; computeSize = computeFun; numSuccessTests =
      0; numDiscardedTests = 0; labels = Map.empty; expectedFailure = false;
      randomSeed0 = rnd; numSuccessShrinks = 0; numTryShrinks = 0 }
      (GenLow.run (checker0 x p))
  | None ->
    let computeFun = a.compFun a.maxSize a.maxSuccess in
    test { maxSuccessTests = a.maxSuccess; maxDiscardedTests = a.maxDiscard;
      maxShrinkNo = a.maxShrinks; computeSize = computeFun; numSuccessTests =
      0; numDiscardedTests = 0; labels = Map.empty; expectedFailure = false;
      randomSeed0 = newRandomSeed; numSuccessShrinks = 0; numTryShrinks = 0 }
      (GenLow.run (checker0 x p))

(** val showCollectStatistics : (char list * int) list -> char list **)

let rec showCollectStatistics = function
| [] -> []
| p :: l' ->
  let (s, n) = p in
  append (show0 showNat n)
    (append (' '::(':'::(' '::[])))
      (append s (append newline (showCollectStatistics l'))))

(** val showResult : result0 show **)

let showResult r =
  append
    (match r with
     | Success (_, _, l, s) -> append (showCollectStatistics l) s
     | GaveUp (_, l, s) -> append (showCollectStatistics l) s
     | Failure (_, _, _, _, _, s, l, _) -> append (showCollectStatistics l) s
     | NoExpectedFailure (_, l, s) -> append (showCollectStatistics l) s)
    newline

(** val computeSizeFuzz : int -> int -> int -> int -> int **)

let computeSizeFuzz maxSize0 _ _ _ =
  maxSize0

(** val fuzzCheck : 'a1 checkable -> 'a1 -> result0 **)

let fuzzCheck x p =
  quickCheckWith x { replay = None; maxSuccess = (Pervasives.succ 0);
    maxDiscard = (Pervasives.succ 0); maxShrinks = 0; maxSize = defSize;
    chatty = true; compFun = computeSizeFuzz } p

type decidable0 =
  bool
  (* singleton inductive, whose constructor was Build_Decidable *)

(** val decidable_le_nat : int -> int -> decidable0 **)

let decidable_le_nat =
  (<=)

type dec = decidable
  (* singleton inductive, whose constructor was Build_Dec *)

(** val dec0 : dec -> decidable **)

let dec0 dec1 =
  dec1

(** val dec_if_dec_eq : 'a1 -> 'a1 -> dec -> bool **)

let dec_if_dec_eq _ _ h =
  h

(** val dec_eq_Z : int -> int -> dec **)

let dec_eq_Z m n =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ ->
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> true)
      (fun _ -> false)
      (fun _ -> false)
      n)
    (fun x ->
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> false)
      (fun p0 ->
      let rec f p x0 =
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p1 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p2 -> f p1 p2)
            (fun _ -> false)
            (fun _ -> false)
            x0)
          (fun p1 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun _ -> false)
            (fun p2 -> f p1 p2)
            (fun _ -> false)
            x0)
          (fun _ ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun _ -> false)
            (fun _ -> false)
            (fun _ -> true)
            x0)
          p
      in f x p0)
      (fun _ -> false)
      n)
    (fun x ->
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> false)
      (fun _ -> false)
      (fun p0 ->
      let rec f p x0 =
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun p1 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun p2 -> f p1 p2)
            (fun _ -> false)
            (fun _ -> false)
            x0)
          (fun p1 ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun _ -> false)
            (fun p2 -> f p1 p2)
            (fun _ -> false)
            x0)
          (fun _ ->
          (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
            (fun _ -> false)
            (fun _ -> false)
            (fun _ -> true)
            x0)
          p
      in f x p0)
      n)
    m

(** val dec_eq_list : 'a1 list -> 'a1 list -> ('a1 -> 'a1 -> dec) -> dec **)

let rec dec_eq_list m n h =
  match m with
  | [] -> (match n with
           | [] -> true
           | _ :: _ -> false)
  | y :: l ->
    (match n with
     | [] -> false
     | a0 :: l0 ->
       if dec_if_dec_eq y a0 (h y a0) then dec_eq_list l l0 h else false)

(** val dec_class_dec : decidable0 -> dec **)

let dec_class_dec = function
| true -> true
| false -> false

type label0 =
| L
| H

(** val label_eq : label0 -> label0 -> bool **)

let label_eq l1 l2 =
  match l1 with
  | L -> (match l2 with
          | L -> true
          | H -> false)
  | H -> (match l2 with
          | L -> false
          | H -> true)

(** val label_join : label0 -> label0 -> label0 **)

let label_join l1 l2 =
  match l1 with
  | L -> l2
  | H -> H

(** val flows_to : label0 -> label0 -> bool **)

let flows_to l1 l2 =
  match l1 with
  | L -> true
  | H -> (match l2 with
          | L -> false
          | H -> true)

type lAB =
| Lab1
| Lab2
| Lab3
| Labpc

type rule_expr =
| L_Bot
| L_Var of lAB
| L_Join of rule_expr * rule_expr

type rule_scond =
| A_True
| A_LE of rule_expr * rule_expr
| A_And of rule_scond * rule_scond
| A_Or of rule_scond * rule_scond

type allowModify = { allow : rule_scond; labRes : rule_expr option;
                     labResPC : rule_expr }

(** val allow : int -> allowModify -> rule_scond **)

let allow _ x = x.allow

(** val labRes : int -> allowModify -> rule_expr option **)

let labRes _ x = x.labRes

(** val labResPC : int -> allowModify -> rule_expr **)

let labResPC _ x = x.labResPC

(** val mk_eval_var : int -> label0 t1 -> label0 -> lAB -> label0 **)

let mk_eval_var n vs pc = function
| Lab1 -> nth_order n vs 0
| Lab2 -> nth_order n vs (Pervasives.succ 0)
| Lab3 -> nth_order n vs (Pervasives.succ (Pervasives.succ 0))
| Labpc -> pc

(** val eval_expr : int -> (lAB -> label0) -> rule_expr -> label0 **)

let rec eval_expr n eval_var = function
| L_Bot -> L
| L_Var labv -> eval_var labv
| L_Join (e1, e2) ->
  label_join (eval_expr n eval_var e1) (eval_expr n eval_var e2)

(** val eval_cond : int -> (lAB -> label0) -> rule_scond -> bool **)

let rec eval_cond n eval_var = function
| A_True -> true
| A_LE (e1, e2) ->
  flows_to (eval_expr n eval_var e1) (eval_expr n eval_var e2)
| A_And (c1, c2) -> (&&) (eval_cond n eval_var c1) (eval_cond n eval_var c2)
| A_Or (c1, c2) -> (||) (eval_cond n eval_var c1) (eval_cond n eval_var c2)

(** val apply_rule :
    int -> allowModify -> label0 t1 -> label0 -> (label0 option * label0)
    option **)

let apply_rule n r vlabs pclab =
  let eval_var = mk_eval_var n vlabs pclab in
  if eval_cond n eval_var r.allow
  then let rpc = eval_expr n eval_var r.labResPC in
       let rres =
         match r.labRes with
         | Some lres -> Some (eval_expr n eval_var lres)
         | None -> None
       in
       Some (rres, rpc)
  else None

type instruction =
| Nop
| Push of int
| BCall of int
| BRet
| Add
| Load
| Store
| Halt

type opCode =
| OpBCall
| OpBRet
| OpNop
| OpPush
| OpAdd
| OpLoad
| OpStore
| OpHalt

(** val opCodes : opCode list **)

let opCodes =
  OpBCall :: (OpBRet :: (OpNop :: (OpPush :: (OpAdd :: (OpLoad :: (OpStore :: (OpHalt :: [])))))))

(** val opCode_eq_dec : opCode -> opCode -> bool **)

let opCode_eq_dec o1 o2 =
  match o1 with
  | OpBCall -> (match o2 with
                | OpBCall -> true
                | _ -> false)
  | OpBRet -> (match o2 with
               | OpBRet -> true
               | _ -> false)
  | OpNop -> (match o2 with
              | OpNop -> true
              | _ -> false)
  | OpPush -> (match o2 with
               | OpPush -> true
               | _ -> false)
  | OpAdd -> (match o2 with
              | OpAdd -> true
              | _ -> false)
  | OpLoad -> (match o2 with
               | OpLoad -> true
               | _ -> false)
  | OpStore -> (match o2 with
                | OpStore -> true
                | _ -> false)
  | OpHalt -> (match o2 with
               | OpHalt -> true
               | _ -> false)

(** val nth2 : 'a1 list -> int -> 'a1 option **)

let nth2 l n =
  if z_lt_dec n 0 then None else nth_error l (Z.to_nat n)

(** val upd_nat : 'a1 list -> int -> 'a1 -> 'a1 list option **)

let rec upd_nat l n a =
  match l with
  | [] -> None
  | x :: q ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> Some (a :: q))
       (fun p ->
       match upd_nat q p a with
       | Some q' -> Some (x :: q')
       | None -> None)
       n)

(** val upd : 'a1 list -> int -> 'a1 -> 'a1 list option **)

let upd l n a =
  if z_lt_dec n 0 then None else upd_nat l (Z.to_nat n) a

(** val replicate : int -> 'a1 -> 'a1 list **)

let rec replicate n a =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' -> a :: (replicate n' a))
    n

type atom =
| Atm of int * label0

(** val pc_lab : atom -> label0 **)

let pc_lab = function
| Atm (_, l) -> l

type stack =
| Mty
| Cons0 of atom * stack
| RetCons of atom * stack

type iMem = instruction list

type mem0 = atom list

type state0 = { st_imem : iMem; st_mem : mem0; st_stack : stack; st_pc : atom }

(** val st_pc : state0 -> atom **)

let st_pc x = x.st_pc

(** val labelCount : opCode -> int **)

let labelCount = function
| OpBCall -> Pervasives.succ 0
| OpBRet -> Pervasives.succ (Pervasives.succ 0)
| OpAdd -> Pervasives.succ (Pervasives.succ 0)
| OpLoad -> Pervasives.succ (Pervasives.succ 0)
| OpStore -> Pervasives.succ (Pervasives.succ (Pervasives.succ 0))
| _ -> 0

type table = opCode -> allowModify

(** val default_table : table **)

let default_table = function
| OpBCall ->
  { allow = A_True; labRes = (Some (L_Var Labpc)); labResPC = (L_Join ((L_Var
    Lab1), (L_Var Labpc))) }
| OpBRet ->
  { allow = A_True; labRes = (Some (L_Join ((L_Var Lab2), (L_Var Labpc))));
    labResPC = (L_Var Lab1) }
| OpNop -> { allow = A_True; labRes = None; labResPC = (L_Var Labpc) }
| OpPush ->
  { allow = A_True; labRes = (Some L_Bot); labResPC = (L_Var Labpc) }
| OpStore ->
  { allow = (A_LE ((L_Join ((L_Var Lab1), (L_Var Labpc))), (L_Var Lab3)));
    labRes = (Some (L_Join ((L_Var Labpc), (L_Join ((L_Var Lab1), (L_Var
    Lab2)))))); labResPC = (L_Var Labpc) }
| OpHalt ->
  { allow = A_True; labRes = (Some L_Bot); labResPC = (L_Var Labpc) }
| _ ->
  { allow = A_True; labRes = (Some (L_Join ((L_Var Lab1), (L_Var Lab2))));
    labResPC = (L_Var Labpc) }

(** val run_tmr :
    table -> opCode -> label0 t1 -> label0 -> (label0 option * label0) option **)

let run_tmr t2 op0 labs pc =
  let r = t2 op0 in apply_rule (labelCount op0) r labs pc

(** val bind0 : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option **)

let bind0 f = function
| Some a0 -> f a0
| None -> None

(** val insert_nat : stack -> int -> atom -> stack option **)

let rec insert_nat s n a =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some (RetCons (a, s)))
    (fun n' ->
    match s with
    | Cons0 (x, xs) ->
      bind0 (fun s' -> Some (Cons0 (x, s'))) (insert_nat xs n' a)
    | _ -> None)
    n

(** val findRet : stack -> (atom * stack) option **)

let rec findRet = function
| Mty -> None
| Cons0 (_, s') -> findRet s'
| RetCons (x, s') -> Some (x, s')

(** val insert : stack -> int -> atom -> stack option **)

let insert s n a =
  if z_lt_dec n 0 then None else insert_nat s (Z.to_nat n) a

(** val lookupInstr : state0 -> instruction option **)

let lookupInstr st =
  let { st_imem = _UU03bc_; st_mem = _; st_stack = _; st_pc = st_pc0 } = st in
  let Atm (pc, _) = st_pc0 in nth2 _UU03bc_ pc

(** val exec : table -> state0 -> state0 option **)

let exec t2 st =
  bind0 (fun instr ->
    match instr with
    | Nop ->
      let { st_imem = _UU03bc_; st_mem = m; st_stack = _UU03c3_; st_pc =
        st_pc0 } = st
      in
      let Atm (xpc, lpc) = st_pc0 in
      (match run_tmr t2 OpNop Nil0 lpc with
       | Some p ->
         let (_, rpcl) = p in
         Some { st_imem = _UU03bc_; st_mem = m; st_stack = _UU03c3_; st_pc =
         (Atm ((Z.add xpc 1), rpcl)) }
       | None -> None)
    | Push r ->
      let { st_imem = _UU03bc_; st_mem = m; st_stack = _UU03c3_; st_pc =
        st_pc0 } = st
      in
      let Atm (xpc, lpc) = st_pc0 in
      (match run_tmr t2 OpPush Nil0 lpc with
       | Some p ->
         let (o, rpcl) = p in
         (match o with
          | Some rl ->
            Some { st_imem = _UU03bc_; st_mem = m; st_stack = (Cons0 ((Atm
              (r, rl)), _UU03c3_)); st_pc = (Atm ((Z.add xpc 1), rpcl)) }
          | None -> None)
       | None -> None)
    | BCall n ->
      let { st_imem = _UU03bc_; st_mem = m; st_stack = st_stack0; st_pc =
        st_pc0 } = st
      in
      (match st_stack0 with
       | Cons0 (a, _UU03c3_) ->
         let Atm (x, l) = a in
         let Atm (xpc, lpc) = st_pc0 in
         (match run_tmr t2 OpBCall (Cons (l, 0, Nil0)) lpc with
          | Some p ->
            let (o, rpcl) = p in
            (match o with
             | Some rl ->
               let pc' = Atm (x, rpcl) in
               let ret_pc = Atm ((Z.add xpc 1), rl) in
               bind0 (fun _UU03c3_' -> Some { st_imem = _UU03bc_; st_mem = m;
                 st_stack = _UU03c3_'; st_pc = pc' })
                 (insert _UU03c3_ n ret_pc)
             | None -> None)
          | None -> None)
       | _ -> None)
    | BRet ->
      let { st_imem = _UU03bc_; st_mem = m; st_stack = st_stack0; st_pc =
        st_pc0 } = st
      in
      (match st_stack0 with
       | Cons0 (a, _UU03c3_) ->
         let Atm (ax, al) = a in
         let Atm (_, lpc) = st_pc0 in
         bind0 (fun tmp ->
           let (y, _UU03c3_') = tmp in
           let Atm (xrpc, lrpc) = y in
           (match run_tmr t2 OpBRet (Cons (lrpc, (Pervasives.succ 0), (Cons
                    (al, 0, Nil0)))) lpc with
            | Some p ->
              let (o, rpcl) = p in
              (match o with
               | Some rl ->
                 let pc' = Atm (xrpc, rpcl) in
                 Some { st_imem = _UU03bc_; st_mem = m; st_stack = (Cons0
                 ((Atm (ax, rl)), _UU03c3_')); st_pc = pc' }
               | None -> None)
            | None -> None)) (findRet _UU03c3_)
       | _ -> None)
    | Add ->
      let { st_imem = _UU03bc_; st_mem = m; st_stack = st_stack0; st_pc =
        st_pc0 } = st
      in
      (match st_stack0 with
       | Cons0 (a, s) ->
         let Atm (x, lx) = a in
         (match s with
          | Cons0 (a0, _UU03c3_) ->
            let Atm (y, ly) = a0 in
            let Atm (xpc, lpc) = st_pc0 in
            (match run_tmr t2 OpAdd (Cons (lx, (Pervasives.succ 0), (Cons
                     (ly, 0, Nil0)))) lpc with
             | Some p ->
               let (o, rpcl) = p in
               (match o with
                | Some rl ->
                  Some { st_imem = _UU03bc_; st_mem = m; st_stack = (Cons0
                    ((Atm ((Z.add x y), rl)), _UU03c3_)); st_pc = (Atm
                    ((Z.add xpc 1), rpcl)) }
                | None -> None)
             | None -> None)
          | _ -> None)
       | _ -> None)
    | Load ->
      let { st_imem = _UU03bc_; st_mem = m; st_stack = st_stack0; st_pc =
        st_pc0 } = st
      in
      (match st_stack0 with
       | Cons0 (a, _UU03c3_) ->
         let Atm (x, l) = a in
         let Atm (xpc, lpc) = st_pc0 in
         bind0 (fun a0 ->
           let Atm (ax, al) = a0 in
           (match run_tmr t2 OpLoad (Cons (al, (Pervasives.succ 0), (Cons (l,
                    0, Nil0)))) lpc with
            | Some p ->
              let (o, rpcl) = p in
              (match o with
               | Some rl ->
                 Some { st_imem = _UU03bc_; st_mem = m; st_stack = (Cons0
                   ((Atm (ax, rl)), _UU03c3_)); st_pc = (Atm ((Z.add xpc 1),
                   rpcl)) }
               | None -> None)
            | None -> None)) (nth2 m x)
       | _ -> None)
    | Store ->
      let { st_imem = _UU03bc_; st_mem = m; st_stack = st_stack0; st_pc =
        st_pc0 } = st
      in
      (match st_stack0 with
       | Cons0 (a0, s) ->
         let Atm (x, lx) = a0 in
         (match s with
          | Cons0 (a1, _UU03c3_) ->
            let Atm (a, la) = a1 in
            let Atm (xpc, lpc) = st_pc0 in
            bind0 (fun inMem ->
              match run_tmr t2 OpStore (Cons (lx, (Pervasives.succ
                      (Pervasives.succ 0)), (Cons (la, (Pervasives.succ 0),
                      (Cons ((pc_lab inMem), 0, Nil0)))))) lpc with
              | Some p ->
                let (o, rpcl) = p in
                (match o with
                 | Some rl ->
                   bind0 (fun m' -> Some { st_imem = _UU03bc_; st_mem = m';
                     st_stack = _UU03c3_; st_pc = (Atm ((Z.add xpc 1),
                     rpcl)) }) (upd m x (Atm (a, rl)))
                 | None -> None)
              | None -> None) (nth2 m x)
          | _ -> None)
       | _ -> None)
    | Halt -> None) (lookupInstr st)

type 'a variation =
| V of 'a * 'a

(** val show_label : label0 show **)

let show_label = function
| L -> 'L'::[]
| H -> 'H'::[]

(** val show_instruction : instruction show **)

let show_instruction = function
| Nop -> 'N'::('o'::('p'::[]))
| Push n -> append ('P'::('u'::('s'::('h'::(' '::[]))))) (show0 showZ n)
| BCall n ->
  append ('B'::('C'::('a'::('l'::('l'::(' '::[])))))) (show0 showZ n)
| BRet -> 'B'::('R'::('e'::('t'::[])))
| Add -> 'A'::('d'::('d'::[]))
| Load -> 'L'::('o'::('a'::('d'::[])))
| Store -> 'S'::('t'::('o'::('r'::('e'::[]))))
| Halt -> 'H'::('a'::('l'::('t'::[])))

(** val numed_contents :
    ('a1 -> char list) -> 'a1 list -> int -> char list **)

let rec numed_contents s l n =
  match l with
  | [] -> []
  | h :: t2 ->
    append (show0 showNat n)
      (append (' '::(':'::(' '::[])))
        (append (s h) (append nl (numed_contents s t2 (Pervasives.succ n)))))

(** val show_atom : atom show **)

let show_atom = function
| Atm (v, l) ->
  append (show0 showZ v) (append (' '::('@'::(' '::[]))) (show0 show_label l))

(** val show_stack : stack show **)

let rec show_stack = function
| Mty -> '['::(']'::[])
| Cons0 (a, s') ->
  append (show0 show_atom a) (append (' '::(':'::(' '::[]))) (show_stack s'))
| RetCons (a, s') ->
  append ('R'::(' '::[]))
    (append (show0 show_atom a)
      (append (' '::(':'::(' '::[]))) (show_stack s')))

type 'a showPair =
  'a -> 'a -> char list
  (* singleton inductive, whose constructor was Build_ShowPair *)

(** val show_pair : 'a1 showPair -> 'a1 -> 'a1 -> char list **)

let show_pair showPair0 =
  showPair0

(** val show_variation : char list -> char list -> char list **)

let show_variation s1 s2 =
  append ('{'::(' '::[]))
    (append s1 (append (' '::('/'::(' '::[]))) (append s2 (' '::('}'::[])))))

(** val show_int_pair : int showPair **)

let show_int_pair v1 v2 =
  if Z.eqb v1 v2
  then show0 showZ v1
  else show_variation (show0 showZ v1) (show0 showZ v2)

(** val decInstrEq : instruction -> instruction -> dec **)

let decInstrEq i1 i2 =
  match i1 with
  | Nop -> (match i2 with
            | Nop -> true
            | _ -> false)
  | Push x ->
    (match i2 with
     | Push n0 -> dec_if_dec_eq x n0 (dec_eq_Z x n0)
     | _ -> false)
  | BCall x ->
    (match i2 with
     | BCall n0 -> dec_if_dec_eq x n0 (dec_eq_Z x n0)
     | _ -> false)
  | BRet -> (match i2 with
             | BRet -> true
             | _ -> false)
  | Add -> (match i2 with
            | Add -> true
            | _ -> false)
  | Load -> (match i2 with
             | Load -> true
             | _ -> false)
  | Store -> (match i2 with
              | Store -> true
              | _ -> false)
  | Halt -> (match i2 with
             | Halt -> true
             | _ -> false)

(** val show_instr_pair : instruction showPair **)

let show_instr_pair i1 i2 =
  if dec0 (decInstrEq i1 i2)
  then show0 show_instruction i1
  else show_variation (show0 show_instruction i1) (show0 show_instruction i2)

(** val show_label_pair : label0 showPair **)

let show_label_pair l1 l2 =
  if label_eq l1 l2
  then show0 show_label l1
  else show_variation (show0 show_label l1) (show0 show_label l2)

(** val show_atom_pair : atom showPair **)

let show_atom_pair a1 a2 =
  let Atm (v1, l1) = a1 in
  let Atm (v2, l2) = a2 in
  append (show_pair show_int_pair v1 v2)
    (append (' '::('@'::(' '::[]))) (show_pair show_label_pair l1 l2))

(** val show_mem_pair : mem0 showPair **)

let show_mem_pair m1 m2 =
  numed_contents (fun xy -> let (x, y) = xy in show_pair show_atom_pair x y)
    (combine m1 m2) 0

(** val show_imem_pair : iMem showPair **)

let show_imem_pair im1 im2 =
  numed_contents (fun xy -> let (x, y) = xy in show_pair show_instr_pair x y)
    (combine im1 im2) 0

(** val total_stack_length : stack -> int **)

let rec total_stack_length = function
| Mty -> 0
| Cons0 (_, s') -> Pervasives.succ (total_stack_length s')
| RetCons (_, s') -> Pervasives.succ (total_stack_length s')

(** val show_stack_pair : stack showPair **)

let show_stack_pair s1 s2 =
  let len1 = total_stack_length s1 in
  let len2 = total_stack_length s2 in
  let show_until =
    let rec show_until s n =
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> ([], s))
        (fun n' ->
        match s with
        | Mty ->
          (('e'::('r'::('r'::('o'::('r'::(':'::(' '::('M'::('t'::('y'::[])))))))))),
            Mty)
        | Cons0 (x, s') ->
          let (str, sf) = show_until s' n' in
          ((append (show0 show_atom x) (append (' '::(':'::(' '::[]))) str)),
          sf)
        | RetCons (x, s') ->
          let (str, sf) = show_until s' n' in
          ((append ('R'::(' '::[]))
             (append (show0 show_atom x) (append (' '::(':'::(' '::[]))) str))),
          sf))
        n
    in show_until
  in
  if Nat.ltb len1 len2
  then let (show_pre, s2') = show_until s2 (sub len2 len1) in
       let prefix =
         append
           ('B'::('i'::('g'::('g'::('e'::('r'::(' '::('p'::('a'::('r'::('t'::(' '::('o'::('f'::(' '::('2'::(':'::(' '::[]))))))))))))))))))
           (append nl (append show_pre nl))
       in
       let p = (s1, s2') in
       let (s3, s4) = p in
       let aux =
         let rec aux s5 s6 =
           match s5 with
           | Mty ->
             (match s6 with
              | Mty -> '['::(']'::[])
              | _ ->
                show_variation (show0 show_stack s5) (show0 show_stack s6))
           | Cons0 (a1, s1') ->
             (match s6 with
              | Cons0 (a2, s2'0) ->
                append (show_pair show_atom_pair a1 a2)
                  (append (' '::(':'::(' '::[]))) (aux s1' s2'0))
              | _ ->
                show_variation (show0 show_stack s5) (show0 show_stack s6))
           | RetCons (a1, s1') ->
             (match s6 with
              | RetCons (a2, s2'0) ->
                append ('R'::(' '::[]))
                  (append (show_pair show_atom_pair a1 a2)
                    (append (' '::(':'::(' '::[]))) (aux s1' s2'0)))
              | _ ->
                show_variation (show0 show_stack s5) (show0 show_stack s6))
         in aux
       in
       append prefix
         (append
           ('C'::('o'::('m'::('m'::('o'::('n'::(' '::('p'::('a'::('r'::('t'::(':'::(' '::[])))))))))))))
           (append nl (aux s3 s4)))
  else if Nat.ltb len2 len1
       then let (show_pre, s1') = show_until s1 (sub len1 len2) in
            let prefix =
              append
                ('B'::('i'::('g'::('g'::('e'::('r'::(' '::('p'::('a'::('r'::('t'::(' '::('o'::('f'::(' '::('1'::(':'::(' '::[]))))))))))))))))))
                (append nl (append show_pre nl))
            in
            let p = (s1', s2) in
            let (s3, s4) = p in
            let aux =
              let rec aux s5 s6 =
                match s5 with
                | Mty ->
                  (match s6 with
                   | Mty -> '['::(']'::[])
                   | _ ->
                     show_variation (show0 show_stack s5)
                       (show0 show_stack s6))
                | Cons0 (a1, s1'0) ->
                  (match s6 with
                   | Cons0 (a2, s2') ->
                     append (show_pair show_atom_pair a1 a2)
                       (append (' '::(':'::(' '::[]))) (aux s1'0 s2'))
                   | _ ->
                     show_variation (show0 show_stack s5)
                       (show0 show_stack s6))
                | RetCons (a1, s1'0) ->
                  (match s6 with
                   | RetCons (a2, s2') ->
                     append ('R'::(' '::[]))
                       (append (show_pair show_atom_pair a1 a2)
                         (append (' '::(':'::(' '::[]))) (aux s1'0 s2')))
                   | _ ->
                     show_variation (show0 show_stack s5)
                       (show0 show_stack s6))
              in aux
            in
            append prefix
              (append
                ('C'::('o'::('m'::('m'::('o'::('n'::(' '::('p'::('a'::('r'::('t'::(':'::(' '::[])))))))))))))
                (append nl (aux s3 s4)))
       else let prefix = [] in
            let p = (s1, s2) in
            let (s3, s4) = p in
            let aux =
              let rec aux s5 s6 =
                match s5 with
                | Mty ->
                  (match s6 with
                   | Mty -> '['::(']'::[])
                   | _ ->
                     show_variation (show0 show_stack s5)
                       (show0 show_stack s6))
                | Cons0 (a1, s1') ->
                  (match s6 with
                   | Cons0 (a2, s2') ->
                     append (show_pair show_atom_pair a1 a2)
                       (append (' '::(':'::(' '::[]))) (aux s1' s2'))
                   | _ ->
                     show_variation (show0 show_stack s5)
                       (show0 show_stack s6))
                | RetCons (a1, s1') ->
                  (match s6 with
                   | RetCons (a2, s2') ->
                     append ('R'::(' '::[]))
                       (append (show_pair show_atom_pair a1 a2)
                         (append (' '::(':'::(' '::[]))) (aux s1' s2')))
                   | _ ->
                     show_variation (show0 show_stack s5)
                       (show0 show_stack s6))
              in aux
            in
            append prefix
              (append
                ('C'::('o'::('m'::('m'::('o'::('n'::(' '::('p'::('a'::('r'::('t'::(':'::(' '::[])))))))))))))
                (append nl (aux s3 s4)))

(** val show_state_pair : state0 showPair **)

let show_state_pair st1 st2 =
  let { st_imem = imem1; st_mem = mem1; st_stack = stk1; st_pc = pc1 } = st1
  in
  let { st_imem = imem2; st_mem = mem2; st_stack = stk2; st_pc = pc2 } = st2
  in
  append
    ('I'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('i'::('o'::('n'::('s'::(':'::(' '::[]))))))))))))))
    (append nl
      (append (show_pair show_imem_pair imem1 imem2)
        (append nl
          (append ('M'::('e'::('m'::('o'::('r'::('y'::(':'::(' '::[]))))))))
            (append nl
              (append (show_pair show_mem_pair mem1 mem2)
                (append nl
                  (append ('S'::('t'::('a'::('c'::('k'::(':'::(' '::[])))))))
                    (append nl
                      (append (show_pair show_stack_pair stk1 stk2)
                        (append nl
                          (append ('P'::('C'::(':'::(' '::[]))))
                            (append (show_pair show_atom_pair pc1 pc2) nl)))))))))))))

(** val show_var : 'a1 showPair -> 'a1 variation show **)

let show_var h0 = function
| V (x1, x2) -> show_pair h0 x1 x2

(** val forallb2 : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec forallb2 f l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _ :: _ -> false)
  | h1 :: t2 ->
    (match l2 with
     | [] -> false
     | h2 :: t3 -> (&&) (f h1 h2) (forallb2 f t2 t3))

type 'a indist =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_Indist *)

(** val indist0 : 'a1 indist -> 'a1 -> 'a1 -> bool **)

let indist0 indist1 =
  indist1

(** val indist_atom : atom indist **)

let indist_atom a1 a2 =
  let Atm (x1, l1) = a1 in
  let Atm (x2, l2) = a2 in
  (match l1 with
   | L -> (match l2 with
           | L -> Z.eqb x1 x2
           | H -> false)
   | H -> (match l2 with
           | L -> false
           | H -> true))

(** val indist_mem : mem0 indist **)

let indist_mem m1 m2 =
  forallb2 (indist0 indist_atom) m1 m2

(** val cropTop : stack -> stack **)

let rec cropTop s = match s with
| Mty -> Mty
| Cons0 (_, s') -> cropTop s'
| RetCons (pc, s') ->
  let Atm (_, l) = pc in (match l with
                          | L -> s
                          | H -> cropTop s')

(** val indist_stack : stack indist **)

let rec indist_stack s1 s2 =
  match s1 with
  | Mty -> (match s2 with
            | Mty -> true
            | _ -> false)
  | Cons0 (a1, s1') ->
    (match s2 with
     | Cons0 (a2, s2') ->
       (&&) (indist0 indist_atom a1 a2) (indist_stack s1' s2')
     | _ -> false)
  | RetCons (a1, s1') ->
    (match s2 with
     | RetCons (a2, s2') ->
       (&&) (indist0 indist_atom a1 a2) (indist_stack s1' s2')
     | _ -> false)

(** val decEq_Imem : instruction -> instruction -> dec **)

let decEq_Imem i1 i2 =
  match i1 with
  | Nop -> (match i2 with
            | Nop -> true
            | _ -> false)
  | Push x ->
    (match i2 with
     | Push n0 -> dec_if_dec_eq x n0 (dec_eq_Z x n0)
     | _ -> false)
  | BCall x ->
    (match i2 with
     | BCall n0 -> dec_if_dec_eq x n0 (dec_eq_Z x n0)
     | _ -> false)
  | BRet -> (match i2 with
             | BRet -> true
             | _ -> false)
  | Add -> (match i2 with
            | Add -> true
            | _ -> false)
  | Load -> (match i2 with
             | Load -> true
             | _ -> false)
  | Store -> (match i2 with
              | Store -> true
              | _ -> false)
  | Halt -> (match i2 with
             | Halt -> true
             | _ -> false)

(** val indist_state : state0 indist **)

let indist_state st1 st2 =
  let { st_imem = imem1; st_mem = mem1; st_stack = stk1; st_pc = pc1 } = st1
  in
  let { st_imem = imem2; st_mem = mem2; st_stack = stk2; st_pc = pc2 } = st2
  in
  if negb (indist0 indist_mem mem1 mem2)
  then false
  else if negb
            (if dec0 (dec_eq_list imem1 imem2 decEq_Imem) then true else false)
       then false
       else if negb (indist0 indist_atom pc1 pc2)
            then false
            else let Atm (_, l) = pc1 in
                 (match l with
                  | L ->
                    if negb (indist0 indist_stack stk1 stk2)
                    then false
                    else true
                  | H ->
                    let stk1' = cropTop stk1 in
                    let stk2' = cropTop stk2 in
                    if negb (indist0 indist_stack stk1' stk2')
                    then false
                    else true)

(** val is_atom_low : atom -> bool **)

let is_atom_low = function
| Atm (_, l) -> (match l with
                 | L -> true
                 | H -> false)

(** val mem_length : int **)

let mem_length =
  ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))

(** val gen_Z : int GenLow.coq_G **)

let gen_Z =
  GenLow.choose chooseZ (0, mem_length)

(** val gen_label : label0 GenLow.coq_G **)

let gen_label =
  GenHigh.elems_ L (L :: (H :: []))

(** val gen_atom : atom GenLow.coq_G **)

let gen_atom =
  GenHigh.liftGen2 (fun x x0 -> Atm (x, x0)) gen_Z gen_label

(** val gen_memory : atom list GenLow.coq_G **)

let gen_memory =
  GenHigh.vectorOf (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) gen_atom

(** val is_atom_low0 : atom -> bool **)

let is_atom_low0 = function
| Atm (_, l) -> (match l with
                 | L -> true
                 | H -> false)

(** val ainstr : state0 -> int -> instruction GenLow.coq_G **)

let ainstr st fuel =
  let { st_imem = _; st_mem = _; st_stack = stk; st_pc = pc } = st in
  let stack_length =
    let rec stack_length = function
    | Cons0 (_, s') -> add (Pervasives.succ 0) (stack_length s')
    | _ -> 0
    in stack_length
  in
  let sl = stack_length stk in
  let containsRet =
    let rec containsRet = function
    | Mty -> false
    | Cons0 (_, s') -> containsRet s'
    | RetCons (_, _) -> true
    in containsRet
  in
  GenHigh.freq_ (GenLow.returnGen Nop) (((Pervasives.succ 0),
    (GenLow.returnGen Nop)) :: (((if is_atom_low0 pc
                                  then mul
                                         (sub (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ
                                           0)))))))))))))))))))) fuel)
                                         (sub (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ
                                           0)))))))))))))))))))) fuel)
                                  else 0),
    (GenLow.returnGen Halt)) :: (((Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))))))))))))))))),
    (GenHigh.liftGen (fun x -> Push x) gen_Z)) :: (((if dec0
                                                          (dec_class_dec
                                                            (decidable_le_nat
                                                              (Pervasives.succ
                                                              sl)
                                                              (Pervasives.succ
                                                              0)))
                                                     then 0
                                                     else Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            0)))))))))))))))))))))))))))))))))))))))),
    (GenHigh.liftGen (fun x -> BCall x)
      (if (=) sl 0
       then GenLow.returnGen 0
       else GenLow.choose chooseZ (0, (Z.of_nat sl))))) :: (((if containsRet
                                                                   stk
                                                              then Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))))))))))))))))))))))))))))))))
                                                              else 0),
    (GenLow.returnGen BRet)) :: (((if dec0
                                        (dec_class_dec
                                          (decidable_le_nat (Pervasives.succ
                                            sl) (Pervasives.succ
                                            (Pervasives.succ 0))))
                                   then 0
                                   else Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          0)))))))))))))))))))))))))))))))))))))))),
    (GenLow.returnGen Add)) :: (((if dec0
                                       (dec_class_dec
                                         (decidable_le_nat (Pervasives.succ
                                           sl) (Pervasives.succ 0)))
                                  then 0
                                  else Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         0)))))))))))))))))))))))))))))))))))))))),
    (GenLow.returnGen Load)) :: (((if dec0
                                        (dec_class_dec
                                          (decidable_le_nat (Pervasives.succ
                                            sl) (Pervasives.succ
                                            (Pervasives.succ 0))))
                                   then 0
                                   else Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (GenLow.returnGen Store)) :: []))))))))

(** val gen_stack : int -> bool -> stack GenLow.coq_G **)

let rec gen_stack n onlyLow =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> GenLow.returnGen Mty)
    (fun n' ->
    GenHigh.freq_ (GenLow.returnGen Mty) (((Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))),
      (GenHigh.liftGen2 (fun x x0 -> Cons0 (x, x0)) gen_atom
        (gen_stack n' onlyLow))) :: (((Pervasives.succ (Pervasives.succ 0)),
      (GenLow.bindGen gen_atom (fun pc ->
        GenHigh.liftGen (fun x -> RetCons (pc, x))
          (gen_stack n' (is_atom_low0 pc))))) :: [])))
    n

(** val gen_by_exec : table -> int -> state0 -> state0 GenLow.coq_G **)

let rec gen_by_exec t2 fuel st =
  let { st_imem = im; st_mem = m; st_stack = stk; st_pc = st_pc0 } = st in
  let Atm (addr, pcl) = st_pc0 in
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> GenLow.returnGen st)
     (fun fuel' ->
     match nth2 im addr with
     | Some i ->
       (match i with
        | Nop ->
          GenLow.bindGen (ainstr st fuel') (fun i0 ->
            match upd im addr i0 with
            | Some im' ->
              let st' = { st_imem = im'; st_mem = m; st_stack = stk; st_pc =
                (Atm (addr, pcl)) }
              in
              gen_by_exec t2 fuel' st'
            | None -> GenLow.returnGen st)
        | _ ->
          (match exec t2 st with
           | Some st' -> gen_by_exec t2 fuel' st'
           | None -> GenLow.returnGen st))
     | None -> GenLow.returnGen st)
     fuel)

(** val gen_state' : state0 GenLow.coq_G **)

let gen_state' =
  let imem0 =
    replicate (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) Nop
  in
  pbind (pMonad_Monad (Obj.magic GenLow.coq_Monad_G)) (Obj.magic __)
    (Obj.magic gen_atom) (fun pc ->
    pbind (pMonad_Monad (Obj.magic GenLow.coq_Monad_G)) (Obj.magic __)
      (Obj.magic gen_memory) (fun mem1 ->
      pbind (pMonad_Monad (Obj.magic GenLow.coq_Monad_G)) (Obj.magic __)
        (Obj.magic gen_stack (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          0)))))))))) (is_atom_low0 pc)) (fun stk ->
        pbind (pMonad_Monad (Obj.magic GenLow.coq_Monad_G)) (Obj.magic __)
          (gen_by_exec default_table (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            0)))))))))))))))))))) { st_imem = imem0; st_mem = mem1;
            st_stack = stk; st_pc = pc }) (fun st' ->
          ret (Obj.magic GenLow.coq_Monad_G) st'))))

(** val break_expr : int -> rule_expr -> rule_expr list **)

let rec break_expr n = function
| L_Bot -> []
| L_Var m -> (L_Var m) :: []
| L_Join (e1, e2) -> app (break_expr n e1) (break_expr n e2)

(** val join_exprs : int -> rule_expr list -> rule_expr **)

let rec join_exprs n = function
| [] -> L_Bot
| e :: es' ->
  (match es' with
   | [] -> e
   | _ :: _ -> L_Join (e, (join_exprs n es')))

(** val break_scond : int -> rule_scond -> rule_scond list **)

let rec break_scond n c = match c with
| A_True -> []
| A_LE (e1, e2) -> map (fun e1' -> A_LE (e1', e2)) (break_expr n e1)
| A_And (c1, c2) -> app (break_scond n c1) (break_scond n c2)
| A_Or (_, _) -> c :: []

(** val and_sconds : int -> rule_scond list -> rule_scond **)

let rec and_sconds n = function
| [] -> A_True
| c :: cs' ->
  (match cs' with
   | [] -> c
   | _ :: _ -> A_And (c, (and_sconds n cs')))

(** val drop_each : 'a1 list -> 'a1 list list **)

let rec drop_each = function
| [] -> []
| x :: xs' -> xs' :: (map (fun xs'' -> x :: xs'') (drop_each xs'))

(** val mutate_expr : int -> rule_expr -> rule_expr list **)

let mutate_expr n e =
  let es = break_expr n e in
  (match es with
   | [] -> []
   | _ :: _ -> map (join_exprs n) (drop_each es))

(** val mutate_scond : int -> rule_scond -> rule_scond list **)

let mutate_scond n c =
  let cs = break_scond n c in
  (match cs with
   | [] -> []
   | _ :: _ -> map (and_sconds n) (drop_each cs))

(** val mutate_rule : int -> allowModify -> allowModify list **)

let mutate_rule n r =
  let a = r.allow in
  let res = r.labRes in
  let pc = r.labResPC in
  app
    (map (fun a' -> { allow = a'; labRes = res; labResPC = pc })
      (mutate_scond n a))
    (app
      (match res with
       | Some lres ->
         map (fun lres' -> { allow = a; labRes = (Some lres'); labResPC =
           pc }) (mutate_expr n lres)
       | None -> [])
      (map (fun pc' -> { allow = a; labRes = res; labResPC = pc' })
        (mutate_expr n pc)))

(** val helper :
    opCode -> allowModify -> opCode -> allowModify -> allowModify **)

let helper o mr o' orig =
  if opCode_eq_dec o o' then mr else orig

(** val mutate_table' : table -> table -> table list **)

let mutate_table' t2 t' =
  fold_left app
    (map (fun o ->
      map (fun mr o' -> helper o mr o' (t' o'))
        (mutate_rule (labelCount o) (t2 o))) opCodes) []

(** val mutate_table : table -> table list **)

let mutate_table t2 =
  mutate_table' t2 t2

type exp_result = { exp_success : checker; exp_fail : checker;
                    exp_reject : checker; exp_check : (bool -> checker) }

(** val exp_reject : exp_result -> checker **)

let exp_reject x = x.exp_reject

(** val exp_check : exp_result -> bool -> checker **)

let exp_check x = x.exp_check

(** val exp_result_fuzz : exp_result **)

let exp_result_fuzz =
  { exp_success = (collect showBool testBool true true); exp_fail =
    (collect showBool testBool false false); exp_reject =
    (collect showString testUnit ('('::(')'::[])) ()); exp_check = (fun b ->
    collect showBool testBool b b) }

(** val sSNI : table -> state0 variation -> exp_result -> checker **)

let sSNI t2 v res =
  let V (st1, st2) = v in
  let { st_imem = _; st_mem = _; st_stack = _; st_pc = st_pc0 } = st1 in
  let Atm (_, l1) = st_pc0 in
  let { st_imem = _; st_mem = _; st_stack = _; st_pc = st_pc1 } = st2 in
  let Atm (_, l2) = st_pc1 in
  (match lookupInstr st1 with
   | Some _ ->
     if indist0 indist_state st1 st2
     then (match l1 with
           | L ->
             (match l2 with
              | L ->
                (match exec t2 st1 with
                 | Some st1' ->
                   (match exec t2 st2 with
                    | Some st2' ->
                      res.exp_check (indist0 indist_state st1' st2')
                    | None -> res.exp_reject)
                 | None -> res.exp_reject)
              | H ->
                (match exec t2 st2 with
                 | Some st2' -> res.exp_check (indist0 indist_state st2 st2')
                 | None -> res.exp_reject))
           | H ->
             (match l2 with
              | L ->
                (match exec t2 st1 with
                 | Some st1' -> res.exp_check (indist0 indist_state st1 st1')
                 | None -> res.exp_reject)
              | H ->
                (match exec t2 st1 with
                 | Some st1' ->
                   (match exec t2 st2 with
                    | Some st2' ->
                      if (&&) (is_atom_low st1'.st_pc)
                           (is_atom_low st2'.st_pc)
                      then res.exp_check (indist0 indist_state st1' st2')
                      else if is_atom_low st1'.st_pc
                           then res.exp_check (indist0 indist_state st2 st2')
                           else res.exp_check (indist0 indist_state st1 st1')
                    | None -> res.exp_reject)
                 | None -> res.exp_reject)))
     else res.exp_reject
   | None -> res.exp_reject)

(** val prop :
    (table -> state0 variation -> exp_result -> checker) -> state0 variation
    option GenLow.coq_G -> table -> exp_result -> checker **)

let prop p gen t2 r =
  forAllShrink testChecker (showOpt (show_var show_state_pair)) gen (fun _ ->
    []) (fun mv -> match mv with
                   | Some v -> p t2 v r
                   | None -> r.exp_reject)

(** val gen_variation_naive : state0 variation option GenLow.coq_G **)

let gen_variation_naive =
  GenLow.bindGen gen_state' (fun st1 ->
    GenLow.bindGen gen_state' (fun st2 ->
      if indist0 indist_state st1 st2
      then GenLow.returnGen (Some (V (st1, st2)))
      else GenLow.returnGen None))

(** val testMutantX :
    (table -> exp_result -> checker) -> exp_result -> int -> checker **)

let testMutantX prop0 r n =
  match nth2 (mutate_table default_table) n with
  | Some t2 -> prop0 t2 r
  | None -> r.exp_reject

(** val prop_SSNI_naive : table -> exp_result -> checker **)

let prop_SSNI_naive t2 r =
  prop sSNI gen_variation_naive t2 r

(** val quickchick : unit -> result0 * char list **)

let quickchick _ =
  let _qc_res =
    fuzzCheck testChecker
      (testMutantX prop_SSNI_naive exp_result_fuzz ((fun p->2*p)
        ((fun p->2*p) ((fun p->1+2*p) 1))))
  in
  (_qc_res, (show0 showResult _qc_res))

let _ = 
  if Array.length Sys.argv = 1 then
    print_string (QuickChickLib.string_of_coqstring (snd (quickchick ())))
  else 
    let quickchick_result =
      try Some ((quickchick) ())
      with _ -> None
    in
    match quickchick_result with
    | Some (Failure _, s) ->
       print_string (QuickChickLib.string_of_coqstring s); flush stdout;
       failwith "Test Failed"
    | Some (_, s) ->
       print_string (QuickChickLib.string_of_coqstring s)
    | _ ->
       print_string "Failed to generate...
"
