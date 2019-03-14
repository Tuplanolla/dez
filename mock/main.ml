(** DEC Executable OCaml Implementation *)

open Big_int
open Obj
open Spec

let () =
  print_endline "main -> dec";
  (** We may need [Obj.magic] to work with generated code. *)
  print_endline (Adapter.string_of_z
      (magic Dec.monkey_saddle (Adapter.z_of_int 42) (Adapter.z_of_int 13)));
  print_endline "main -> jrlib (unsafe)";
  print_endline (string_of_int
      (Driver_jr.monkey_saddle_unsafe 42 13));
  print_endline "main -> jrlib";
  print_endline (string_of_big_int
      (Driver_jr.monkey_saddle (big_int_of_int 42) (big_int_of_int 13)))
