(** * Actions *)

From DEZ.Has Require Export
  Operations.

(** ** Left Act *)
(** ** Left Action *)

Class HasActL (A B : Type) : Type := act_l (x : A) (a : B) : B.

#[export] Typeclasses Transparent HasActL.

(** ** Right Act *)
(** ** Right Action *)

Class HasActR (A B : Type) : Type := act_r (a : B) (x : A) : B.

#[export] Typeclasses Transparent HasActR.

Module Subclass.

Section Context.

Context (A : Type).

(** A left action of an object on itself is a binary operation. *)

#[export] Instance act_l_has_bin_op {al : HasActL A A} : HasBinOp A := act_l.

(** A right action of an object on itself is a binary operation. *)

#[export] Instance act_r_has_bin_op {ar : HasActR A A} : HasBinOp A := act_r.

End Context.

End Subclass.
