(** * Preordering *)

From DEZ.Is Require Export
  Reflexive Transitive.

(** ** Preorder *)

Fail Fail Class IsPreord (A : Type) (X : A -> A -> Prop) : Prop := {
  is_refl :> IsRefl X;
  is_trans :> IsTrans X;
}.

Notation IsPreord := PreOrder.
