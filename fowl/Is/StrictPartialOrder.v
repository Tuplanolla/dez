(** * Strict Partial Ordering *)

From DEZ.Is Require Export
  Irreflexive Transitive.

(** ** Strict Partial Order *)

Fail Fail Class IsStrPartOrd (A : Type) (X : A -> A -> Prop) : Prop := {
  is_irrefl :> IsIrrefl X;
  is_trans :> IsTrans X;
}.

Notation IsStrPartOrd := StrictOrder.
