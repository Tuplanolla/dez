(** * Measuring Distances *)

From DEZ.Has Require Export
  Form.

(** ** Distance Function *)
(** ** Metric *)

Class HasDist (A B : Type) : Type := dist (a b : B) : A.

#[export] Typeclasses Transparent HasDist.

Module Subclass.

Section Context.

Context (A B : Type).

(** A distance function is a form. *)

#[export] Instance dist_has_form {d : HasDist A B} : HasForm A B := dist.

End Context.

End Subclass.
