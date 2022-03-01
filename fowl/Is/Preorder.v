(** * Preordering *)

From DEZ.Is Require Export
  Reflexive Transitive.

(** ** Preorder *)

Fail Fail Class IsPreord (A : Type) (X : A -> A -> Prop) : Prop := {
  preord_is_refl :> IsRefl X;
  preord_is_trans :> IsTrans X;
}.

Notation IsPreord := PreOrder.
