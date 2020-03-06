From Maniunfold.Has Require Export
  BinaryOperation.

Class HasMeet (A : Type) : Type := meet : A -> A -> A.

Typeclasses Transparent HasMeet.

Section Context.

Context {A : Type} `{has_meet : HasMeet A}.

Global Instance A_has_bin_op : HasBinOp A := meet.

End Context.
