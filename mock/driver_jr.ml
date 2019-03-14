(** DEC JR Driver OCaml Implementation *)

open Array
open Big_int
open Char

external monkey_saddle_unsafe : int -> int -> int =
  "stub_monkey_saddle_unsafe"

external monkey_saddle_buffer : char array -> char array -> char array =
  "stub_monkey_saddle"

let quomod_big_int_int x y =
  let (q, m) = quomod_big_int x (big_int_of_int y) in
  (q, int_of_big_int m)
(** Calculate the Euclidean division of a big integer and a small integer. *)

let num_bytes_big_int x =
  let n = num_bits_big_int x in
  if n = 0 then 0 else succ (pred n / 8)
(** Return the number of significant bytes
    in the absolute value of the given big integer. *)

let buffer_of_big_int x =
  let n = num_bytes_big_int x in
  let b = make (succ n) (chr 0) in
  let r = ref (abs_big_int x) in
  set b 0 (if sign_big_int x < 0 then chr 1 else chr 0);
  for i = 1 to n do
    let (q, m) = quomod_big_int_int !r 0x100 in
    set b i (chr m);
    r := q
  done;
  b
(** Convert a big integer into a buffer. *)

let big_int_of_buffer b =
  let n = length b in
  if n = 0 then
    zero_big_int else
    let r = ref zero_big_int in
    for i = pred n downto 1 do
      r := add_int_big_int (code (get b i)) (mult_int_big_int 0x100 !r)
    done;
    if get b 0 = chr 0 then
      !r else
      minus_big_int !r
(** Convert a buffer into a big integer. *)

let monkey_saddle x y =
  big_int_of_buffer
  (monkey_saddle_buffer (buffer_of_big_int x) (buffer_of_big_int y))
