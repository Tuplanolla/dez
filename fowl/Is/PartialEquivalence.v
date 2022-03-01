(** * Partial Equivalences *)

From DEZ.Is Require Export
  Symmetric Transitive Proper.

(** ** Partial Equivalence Relation *)

Fail Fail Class IsPartEquiv (A : Type) (X : A -> A -> Prop) : Prop := {
  part_equiv_is_sym :> IsSym X;
  part_equiv_is_trans :> IsTrans X;
}.

Notation IsPartEquiv := PER.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** A partial equivalence relation is transitive. *)

#[local] Instance part_equiv_is_proper
  `{!IsPartEquiv X} : IsProper (X ==> X ==> _<->_) X.
Proof. typeclasses eauto. Qed.

End Context.
