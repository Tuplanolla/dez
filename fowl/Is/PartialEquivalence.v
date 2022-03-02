(** * Partial Equivalence *)

From DEZ.Is Require Export
  Symmetric Transitive.

(** ** Partial Equivalence Relation *)

Fail Fail Class IsPartEquiv (A : Type) (X : A -> A -> Prop) : Prop := {
  part_equiv_is_sym :> IsSym X;
  part_equiv_is_trans :> IsTrans X;
}.

Notation IsPartEquiv := PER.
Notation part_equiv_is_sym := PER_Symmetric.
Notation part_equiv_is_trans := PER_Transitive.
