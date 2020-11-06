From Maniunfold.Has Require Export
  ThreeSorted.BinaryFunction.

(** Action; right chirality.
    See [Has.TwoSorted.LeftAction]. *)

Class HasRAct (A B : Type) : Type := r_act : B -> A -> B.

Typeclasses Transparent HasRAct.

(** TODO These instances seem useless. Are they? *)

Section Context.

Context (A B : Type) `(HasRAct A B).

Global Instance B_A_B_has_bin_fn : HasBinFn B A B := r_act.

End Context.
