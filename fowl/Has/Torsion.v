(** * Torsion or Action over a Principal Homogeneous Space *)

From Maniunfold Require Export
  Init.

(** TODO Does the concept of a nonchiral torsion even make sense? *)

Class HasTor (A B : Type) : Type := tor (x y : B) : A.
Class HasTorL (A B : Type) : Type := tor_l (x y : B) : A.
Class HasTorR (A B : Type) : Type := tor_r (x y : B) : A.

Typeclasses Transparent HasTor HasTorL HasTorR.
