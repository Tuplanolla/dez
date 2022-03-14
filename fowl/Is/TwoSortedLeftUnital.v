From DEZ.Has Require Export
  Operations Actions.
From DEZ.Supports Require Import
  AdditiveNotations.

(** Unital; left chirality.
    See [Is.OneSortedLeftUnital]. *)

Class IsTwoUnlL (A B : Type)
  `(HasActL A B) `(HasNullOp A) : Prop :=
  two_unl_l : forall x : B, 0 +< x = x.
