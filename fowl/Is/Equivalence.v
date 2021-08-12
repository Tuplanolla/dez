(** * Equivalence *)

From DEZ.Is Require Export
  Reflexive Symmetric Transitive.

Fail Fail Class IsEq (A : Type) (R : A -> A -> Prop) : Prop := {
  is_refl :> IsRefl R;
  is_sym :> IsSym R;
  is_trans :> IsTrans R;
}.

(** ** Equivalence *)

Notation IsEq := Equivalence.
