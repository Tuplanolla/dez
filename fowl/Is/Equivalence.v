(** * Equivalence *)

From DEZ.Is Require Export
  Reflexive Symmetric Transitive Preorder PartialEquivalence.

(** ** Equivalence Relation *)

Fail Fail Class IsEquiv (A : Type) (X : A -> A -> Prop) : Prop := {
  equiv_is_refl :> IsRefl X;
  equiv_is_sym :> IsSym X;
  equiv_is_trans :> IsTrans X;
}.

Notation IsEquiv := Equivalence.
Notation equiv_is_refl := Equivalence_Reflexive.
Notation equiv_is_sym := Equivalence_Symmetric.
Notation equiv_is_trans := Equivalence_Transitive.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** An equivalence relation is a preorder. *)

#[local] Instance equiv_is_preord
  `{!IsEquiv X} : IsPreord X.
Proof. typeclasses eauto. Qed.

(** An equivalence relation is a partial equivalence relation. *)

#[local] Instance equiv_is_part_equiv
  `{!IsEquiv X} : IsPartEquiv X.
Proof. typeclasses eauto. Qed.

End Context.
