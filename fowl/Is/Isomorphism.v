(* bad *)
From Maniunfold.Has Require Export
  Isomorphism.
From Maniunfold.Offers Require Export
  IsomorphismMappings.

Class IsIso (A B : Type) `(HasIso A B) : Prop := {
  retr_sect (x : A) : retr (sect x) = x;
  sect_retr (x : B) : sect (retr x) = x;
}.

Section Context.

Context (A B : Type) `(IsIso A B).

Local Instance has_iso : HasIso B A := (retr, sect).

Local Instance iso_is_iso : IsIso iso.
Proof.
  split.
  - intros x. apply sect_retr.
  - intros x. apply retr_sect. Defined.

End Context.
