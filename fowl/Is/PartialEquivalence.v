(** * Partial Equivalence *)

From DEZ.Is Require Export
  Symmetric Transitive.

(** ** Partial Equivalence *)

Fail Fail Class IsPartEq (A : Type) (R : A -> A -> Prop) : Prop := {
  is_sym :> IsSym R;
  is_trans :> IsTrans R;
}.

Notation IsPartEq := PER.
