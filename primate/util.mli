(** Manage a resource. *)
val bracket : acquire:(unit -> 'a) -> ('a -> 'b) -> release:('a -> unit) -> 'b
