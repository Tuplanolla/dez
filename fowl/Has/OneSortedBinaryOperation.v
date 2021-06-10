From Maniunfold.Has Require Export
  TwoSortedLeftAction TwoSortedRightAction
  TwoSortedLeftTorsion TwoSortedRightTorsion.

(** Binary operation, dyadic operation.
    Commonly found in semigroups. *)

Class HasBinOp (A : Type) : Type := bin_op : A -> A -> A.

Typeclasses Transparent HasBinOp.

Section Context.

Context (A : Type) `(HasBinOp A).

Global Instance A_A_has_l_act : HasLAct A A := bin_op.
Global Instance A_A_has_r_act : HasRAct A A := bin_op.
Global Instance A_A_has_l_tor : HasLTor A A := bin_op.
Global Instance A_A_has_r_tor : HasRTor A A := bin_op.

End Context.
