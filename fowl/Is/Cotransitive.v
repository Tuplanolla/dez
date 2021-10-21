(** * Cotransitivity *)

From DEZ Require Export
  Init.

Class IsCotransGen (A B : Type) (P : B -> Prop) (X : B -> B -> Prop)
  (k : A -> A -> B) : Prop :=
  cotrans_gen (x y z : A) (a : P (k x z)) : X (k x y) (k y z).

(** ** Cotransitive Binary Relation *)

Class IsCotrans (A : Type) (X : A -> A -> Prop) : Prop :=
  cotrans (x y z : A) (a : X x z) : X x y \/ X y z.

Section Context.

Context (A : Type) (X : A -> A -> Prop) `(!IsCotrans X).

#[local] Instance is_cotrans_gen : IsCotransGen id _\/_ X.
Proof. exact cotrans. Qed.

End Context.

#[export] Hint Resolve is_cotrans_gen : typeclass_instances.
