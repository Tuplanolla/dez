(* bad *)
From Maniunfold.Has Require Export
  TwoSorted.Isomorphism.
From Maniunfold.Offers Require Export
  TwoSorted.IsomorphismMappings.

Class IsIso (A B : Type) (A_B_has_iso : HasIso A B) : Prop := {
  retr_sect : forall x : A, retr (sect x) = x;
  sect_retr : forall x : B, sect (retr x) = x;
}.

Section Context.

Context {A B : Type} `{is_iso : IsIso A B}.

Local Instance B_A_has_iso : HasIso B A := (retr, sect).

Local Instance B_A_iso_is_iso : IsIso B A iso.
Proof.
  split.
  - intros x. apply (sect_retr x).
  - intros x. apply (retr_sect x). Defined.

End Context.
