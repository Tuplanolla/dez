(** * Binary Operation *)

From Maniunfold.Has Require Export
  TwoSortedLeftAction TwoSortedRightAction
  TwoSortedLeftTorsion TwoSortedRightTorsion.

Class HasBinOp (A : Type) : Type := bin_op (x y : A) : A.

Typeclasses Transparent HasBinOp.

Section Context.

Context (A : Type) (f : HasBinOp A).

Global Instance has_l_act : HasLAct A A := bin_op.
Global Instance has_r_act : HasRAct A A := bin_op.
Global Instance has_l_tor : HasLTor A A := bin_op.
Global Instance has_r_tor : HasRTor A A := bin_op.

End Context.
