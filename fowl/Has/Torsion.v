(** * Torsion or Action over a Principal Homogeneous Space *)

From Maniunfold.Has Require Export
  BinaryOperation.

(** TODO Does the concept of a nonchiral torsion even make sense? *)

Class HasTor (A B : Type) : Type := tor (x y : B) : A.
Class HasTorL (A B : Type) : Type := tor_l (x y : B) : A.
Class HasTorR (A B : Type) : Type := tor_r (x y : B) : A.

Typeclasses Transparent HasTor HasTorL HasTorR.

Module Subclass.

Section Context.

Context (A : Type).

(** Torsion is a binary operation. *)

#[local] Instance tor_has_bin_op (Hl : HasTor A A) : HasBinOp A := tor.
#[local] Instance tor_l_has_bin_op (Hl : HasTorL A A) : HasBinOp A := tor_l.
#[local] Instance tor_r_has_bin_op (Hr : HasTorR A A) : HasBinOp A := tor_r.

End Context.

#[export] Hint Resolve tor_has_bin_op
  tor_l_has_bin_op tor_r_has_bin_op : typeclass_instances.

End Subclass.
