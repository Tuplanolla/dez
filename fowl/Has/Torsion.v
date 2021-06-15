(** Torsion or Action over a Principal Homogeneous Space *)

From Maniunfold Require Export
  Init.

(** TODO Does the concept of a nonchiral torsion even make sense? *)

Class HasTor (A B : Type) : Type := tor : B -> B -> A.
Class HasTorL (A B : Type) : Type := tor_l : B -> B -> A.
Class HasTorR (A B : Type) : Type := tor_r : B -> B -> A.

Typeclasses Transparent HasTor HasTorL HasTorR.
