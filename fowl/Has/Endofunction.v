(** * Arbitrary Endofunction *)

From Maniunfold.Has Require Export
  Function.

Fail Fail #[deprecated (since="now")]
Class HasEndo (A : Type) : Type := endo : A -> A.

Notation HasEndo A := (HasFn A A).
Notation endo := (fn : HasEndo _).
