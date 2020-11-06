From Maniunfold.Has Require Export
  ThreeSorted.BinaryFunction.

(** Action, act, transformation; left chirality.
    Commonly found in semigroup actions. *)

Class HasLAct (A B : Type) : Type := l_act : A -> B -> B.

Typeclasses Transparent HasLAct.

(** TODO These instances seem useless. Are they? *)

Section Context.

Context (A B : Type) `(HasLAct A B).

Global Instance A_B_B_has_bin_fn : HasBinFn A B B := l_act.

End Context.
