(** * Cotransitivity *)

From DEZ Require Export
  Init.

Class IsCotransGen (A B : Type) (P : B -> Prop) (R : B -> B -> Prop)
  (k : A -> A -> B) : Prop :=
  cotrans_gen (x y z : A) (a : P (k x z)) : R (k x y) (k y z).

(** ** Cotransitive Binary Relation *)

Class IsCotrans (A : Type) (R : A -> A -> Prop) : Prop :=
  cotrans (x y z : A) (a : R x z) : R x y \/ R y z.

Section Context.

Context (A : Type) (R : A -> A -> Prop) `(!IsCotrans R).

#[local] Instance is_cotrans_gen : IsCotransGen id _\/_ R.
Proof. exact cotrans. Qed.

End Context.

#[export] Hint Resolve is_cotrans_gen : typeclass_instances.
