(** * Algebraic Forms *)

(** This concept appears in bilinear forms and metric spaces,
    but does not have a common name, so we call it a form. *)

From DEZ.Has Require Export
  Operation.

(** ** Form *)

Class HasForm (A B : Type) : Type := form (a b : B) : A.

#[export] Typeclasses Transparent HasForm.

Module Subclass.

Section Context.

Context (A : Type).

(** A homogeneous form is a binary operation. *)

#[export] Instance form_has_bin_op {al : HasForm A A} : HasBinOp A := form.

End Context.

End Subclass.
