From Maniunfold.Has Require Export
  ThreeSortedBinaryFunction.

(** TODO Does the concept of a nonchiral torsion even make sense? *)

Class HasTor (A B : Type) : Type := tor : B -> B -> A.

Typeclasses Transparent HasTor.

Section Context.

Context (A B : Type) `(HasTor A B).

Global Instance B_B_A_has_bin_fn : HasBinFn B B A := tor.

End Context.
