(** * Binary Operation *)

From Maniunfold.Has Require Export
  Action Action
  TwoSortedLeftTorsion TwoSortedRightTorsion.

Class HasBinOp (A : Type) : Type := bin_op (x y : A) : A.

Typeclasses Transparent HasBinOp.

(** TODO These instances seem useless. Are they? *)

#[deprecated(since="now")]
Section Context.

Context (A : Type) (f : HasBinOp A).

Global Instance has_act_l : HasActL A A := bin_op.
Global Instance has_act_r : HasActR A A := bin_op.
Global Instance has_l_tor : HasLTor A A := bin_op.
Global Instance has_r_tor : HasRTor A A := bin_op.

End Context.
