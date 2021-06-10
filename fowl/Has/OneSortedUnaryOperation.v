From Maniunfold Require Export
  Init.

(** Unary operation, endofunction.
    Commonly found in groups. *)

Class HasUnOp (A : Type) : Type := un_op : A -> A.

Typeclasses Transparent HasUnOp.
