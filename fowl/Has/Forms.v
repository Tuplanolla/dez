(** * Forms *)

From DEZ.Has Require Export
  Operations.

(** ** Form *)

(** This concept appears in sesquilinear forms and metrics,
    but does not have a common name, so we call it a form. *)

Class HasForm (A B : Type) : Type := form (a b : B) : A.

#[export] Typeclasses Transparent HasForm.

Module Subclass.

Section Context.

Context (A : Type).

(** A homogeneous form is a binary operation. *)

#[export] Instance form_has_bin_op {s : HasForm A A} : HasBinOp A := form.

End Context.

End Subclass.
