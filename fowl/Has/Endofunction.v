(** * Operational class for arbitrary endofunctions. *)

From Maniunfold.Has Require Export
  Function.

Fail Fail Class HasEndo (A : Type) : Type := endo : A -> A.

Notation HasEndo A := (HasFn A A).
Notation endo := (fn : HasEndo _).
