(** * Equivalences *)

From DEZ.Is Require Export
  Reflexive Symmetric Transitive.

(** ** Equivalence Relation *)

Fail Fail Class IsEquiv (A : Type) (X : A -> A -> Prop) : Prop := {
  equiv_is_refl :> IsRefl X;
  equiv_is_sym :> IsSym X;
  equiv_is_trans :> IsTrans X;
}.

Notation IsEquiv := Equivalence.
