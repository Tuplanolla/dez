(** * Action or Act *)

From DEZ.Has Require Export
  BinaryOperation.

Class HasActL (A B : Type) : Type := act_l (a : A) (x : B) : B.
Class HasActR (A B : Type) : Type := act_r (x : B) (a : A) : B.

Typeclasses Transparent HasActL HasActR.

Module Subclass.

Section Context.

Context (A : Type).

(** Homogeneous action is a binary operation. *)

#[local] Instance act_l_has_bin_op (Hl : HasActL A A) : HasBinOp A := act_l.
#[local] Instance act_r_has_bin_op (Hr : HasActR A A) : HasBinOp A := act_r.

End Context.

#[export] Hint Resolve act_l_has_bin_op act_r_has_bin_op : typeclass_instances.

End Subclass.
