(** * Partial Equivalences *)

From DEZ.Is Require Export
  Symmetric Transitive.

(** ** Partial Equivalence Relation *)

Fail Fail Class IsPartEquiv (A : Type) (X : A -> A -> Prop) : Prop := {
  part_equiv_is_sym :> IsSym X;
  part_equiv_is_trans :> IsTrans X;
}.

Notation IsPartEquiv := PER.
