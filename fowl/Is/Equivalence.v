(** * Equivalence *)

From DEZ.Is Require Export
  Reflexive Symmetric Transitive.

Fail Fail Class IsEq (A : Type) (X : A -> A -> Prop) : Prop := {
  is_refl :> IsRefl X;
  is_sym :> IsSym X;
  is_trans :> IsTrans X;
}.

(** ** Equivalence *)

Notation IsEq := Equivalence.
