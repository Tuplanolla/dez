(** TODO This is currently unused,
    but the plan is to use this to generalize some of the predicative classes
    from group inverses to arbitrary endomorphisms. *)

Class HasEndo (A : Type) : Type := endo : A -> A.

Typeclasses Transparent HasEndo.
