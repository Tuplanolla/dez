From Maniunfold.Has Require Export
  Function.

(** Unary operation, endofunction.
    Commonly found in groups. *)

Class HasUnOp (A : Type) : Type := un_op : A -> A.

Typeclasses Transparent HasUnOp.

(** TODO Check these superclasses. *)

Section Context.

Context {A : Type} `{A_has_un_op : HasUnOp A}.

Global Instance A_A_has_fn : HasFn A A := un_op.

End Context.
