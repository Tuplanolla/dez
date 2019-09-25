(** DEC SR Driver OCaml Interface *)

open Big_int

val monkey_saddle_buffer : bytes -> bytes -> bytes
(** Call the corresponding Python function directly. *)

val monkey_saddle : big_int -> big_int -> big_int
(** Serialize the given big integers into buffers,
    call the corresponding Python function with them and
    deserialize the result back into a big integer. *)
