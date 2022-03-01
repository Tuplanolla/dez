(** * Strict Partial Ordering *)

From DEZ.Is Require Export
  Irreflexive Transitive Asymmetric.

(** ** Strict Partial Order *)

Fail Fail Class IsStrPartOrd (A : Type) (X : A -> A -> Prop) : Prop := {
  str_part_ord_is_irrefl :> IsIrrefl X;
  str_part_ord_is_trans :> IsTrans X;
}.

Notation IsStrPartOrd := StrictOrder.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** A strict partial order is asymmetric. *)

#[local] Instance str_part_ord_is_asym
  `{!IsStrPartOrd X} : IsAsym X.
Proof. typeclasses eauto. Qed.

End Context.

