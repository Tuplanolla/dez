From Maniunfold.Has Require Export
  TwoSorted.Function.

(** Unary operation, endofunction.
    Commonly found in groups. *)

Class HasUnOp (A : Type) : Type := un_op : A -> A.

Typeclasses Transparent HasUnOp.

(** TODO Check these superclasses. *)

Section Context.

Context (A : Type) `(HasUnOp A).

Global Instance A_A_has_fn : HasFn A A := un_op.

End Context.
