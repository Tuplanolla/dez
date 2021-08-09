(** * Distance or Metric *)

From DEZ.Has Require Export
  Torsion.

Class HasDist (A B : Type) : Type := dist (x y : B) : A.

Typeclasses Transparent HasDist.

Module Subclass.

Section Context.

Context (A B : Type) (Hd : HasDist A B).

(** Distance is a torsion. *)

#[local] Instance has_tor_l : HasTorL A B := dist.
#[local] Instance has_tor_r : HasTorR A B := dist.

End Context.

#[export] Hint Resolve has_tor_l has_tor_r : typeclass_instances.

End Subclass.
