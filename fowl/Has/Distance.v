(** * Distance or Metric *)

From Maniunfold.Has Require Export
  Torsion.

Class HasDist (A B : Type) : Type := dist (x y : B) : A.

Typeclasses Transparent HasDist.

Module Subclass.

Section Context.

Context (A B : Type) (Hd : HasDist A B).

(** TODO For real? *)

(** Distance is a torsion. *)

#[local] Instance has_tor : HasTor A B := dist.
#[local] Instance has_tor_l : HasTorL A B := dist.
#[local] Instance has_tor_r : HasTorR A B := dist.

End Context.

#[export] Hint Resolve has_tor has_tor_l has_tor_r : typeclass_instances.

End Subclass.
