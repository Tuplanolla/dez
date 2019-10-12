(** TODO This is currently unused,
    but the plan is to use this to generalize some of the predicative classes
    from group inverses to arbitrary functions. *)

Class HasFun (A B : Type) : Type := fun : A -> B.

Typeclasses Transparent HasFun.
