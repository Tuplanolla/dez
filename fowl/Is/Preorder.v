(** * Preordering *)

From DEZ.Is Require Export
  Reflexive Transitive Irreflexive.

(** ** Preorder *)
(** ** Quasiorder *)

Fail Fail Class IsPreord (A : Type) (X : A -> A -> Prop) : Prop := {
  preord_is_refl :> IsRefl X;
  preord_is_trans :> IsTrans X;
}.

Notation IsPreord := PreOrder.
Notation preord_is_refl := PreOrder_Reflexive.
Notation preord_is_trans := PreOrder_Transitive.

(** ** Strict Preorder *)
(** ** Strict Quasiorder *)

Class IsStrPreord (A : Type) (X : A -> A -> Prop) : Prop := {
  str_preord_is_irrefl :> IsIrrefl X;
  str_preord_is_trans :> IsTrans X;
}.
