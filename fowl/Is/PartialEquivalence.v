(** * Partial Equivalence *)

From DEZ.Is Require Export
  Symmetric Transitive.

(** ** Partial Equivalence *)

Fail Fail Class IsPartEq (A : Type) (X : A -> A -> Prop) : Prop := {
  is_sym :> IsSym X;
  is_trans :> IsTrans X;
}.

Notation IsPartEq := PER.
