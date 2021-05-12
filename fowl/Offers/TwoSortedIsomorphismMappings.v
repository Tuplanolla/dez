From Maniunfold.Has Require Export
  TwoSortedIsomorphism.

Section Context.

Context (A B : Type) `(HasIso A B).

(** Section, forward mapping. *)

Definition sect : A -> B := fst iso.

(** Retraction, backward mapping. *)

Definition retr : B -> A := snd iso.

End Context.

Arguments sect {_ _ !_} _.
Arguments retr {_ _ !_} _.
