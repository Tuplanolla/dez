(** DEC JR Driver OCaml Interface *)

open Big_int

val monkey_saddle_unsafe : int -> int -> int
(** Call the corresponding C function directly. *)

val monkey_saddle_buffer : bytes -> bytes -> bytes
(** Conservatively estimate the required memory usage and
    call the corresponding C function with it. *)

val monkey_saddle : big_int -> big_int -> big_int
(** Conservatively estimate the required memory usage,
    serialize the given big integers into buffers,
    call the corresponding C function with them and
    deserialize the result back into a big integer. *)
