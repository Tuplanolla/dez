(** * Equivalences *)

From DEZ.Is Require Export
  Reflexive Symmetric Transitive PartialEquivalence.

(** ** Equivalence Relation *)

Fail Fail Class IsEquiv (A : Type) (X : A -> A -> Prop) : Prop := {
  equiv_is_refl :> IsRefl X;
  equiv_is_sym :> IsSym X;
  equiv_is_trans :> IsTrans X;
}.

Notation IsEquiv := Equivalence.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** An equivalence relation is a partial equivalence relation. *)

#[local] Instance equiv_is_part_equiv
  `{!IsEquiv X} : IsPartEquiv X.
Proof. typeclasses eauto. Qed.

End Context.
