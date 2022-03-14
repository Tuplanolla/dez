From DEZ.Has Require Export
  Operations Actions.
From DEZ.Supports Require Import
  AdditiveNotations.

(** Unital; left chirality.
    See [Is.OneSortedLeftUnital]. *)

Class IsTwoUnlR (A B : Type)
  `(HasActR A B) `(HasNullOp A) : Prop :=
  two_unl_r : forall x : B, x >+ 0 = x.
