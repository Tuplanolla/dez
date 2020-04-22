(** DEC SR Driver OCaml Implementation *)

open Big_int
open Bytes
open Char
open Unix

let int_buffer_size =
  8
(** The size of small integer buffers in bytes. *)

let quomod_int x y =
  (x / y, x mod y)
(** Calculate the Euclidean division of two small integers. *)

let quomod_big_int_int x y =
  let (q, m) = quomod_big_int x (big_int_of_int y) in
  (q, int_of_big_int m)
(** Calculate the Euclidean division of a big integer and a small integer. *)

let num_bytes_big_int x =
  let n = num_bits_big_int x in
  if n = 0 then 0 else succ (pred n / 8)
(** Return the number of significant bytes
    in the absolute value of the given big integer. *)

let buffer_of_int x =
  let n = int_buffer_size in
  let b = create n in
  let r = ref (abs x) in
  for i = 0 to pred n do
    let (q, m) = quomod_int !r 0x100 in
    set b i (chr m);
    r := q
  done;
  b
(** Convert the absolute value of a small integer
    into a small integer buffer. *)

let int_of_buffer b =
  let n = int_buffer_size in
  if n = 0 then
    0 else
    let r = ref 0 in
    for i = pred n downto 0 do
      r := code (get b i) + 0x100 * !r
    done;
    !r
(** Convert a small integer buffer into a small integer. *)

let buffer_of_big_int x =
  let n = num_bytes_big_int x in
  let b = create (succ n) in
  let r = ref (abs_big_int x) in
  set b 0 (if sign_big_int x < 0 then chr 1 else chr 0);
  for i = 1 to n do
    let (q, m) = quomod_big_int_int !r 0x100 in
    set b i (chr m);
    r := q
  done;
  b
(** Convert a big integer into a big integer buffer. *)

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
(** Convert a big integer buffer into a big integer. *)

let monkey_saddle_buffer xb yb =
  let ic, oc = open_process "python3 srwrap.py" in
  output_bytes oc (buffer_of_int (length xb));
  output_bytes oc xb;
  output_bytes oc (buffer_of_int (length yb));
  output_bytes oc yb;
  flush oc;
  let nzb = create int_buffer_size in
  really_input ic nzb 0 (length nzb);
  let zb = create (int_of_buffer nzb) in
  really_input ic zb 0 (length zb);
  close_in ic;
  close_out oc;
  zb

let monkey_saddle x y =
  big_int_of_buffer
  (monkey_saddle_buffer (buffer_of_big_int x) (buffer_of_big_int y))
