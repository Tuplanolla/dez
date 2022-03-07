From DEZ.Is Require Export
  Injective.

(** TODO Untangle this mess. *)

(** This has the same shape as [Z.mul_reg_l]. *)

Class IsNonzeroCancelL (A : Type) (X : A -> A -> Prop)
  (w : A) (k : A -> A -> A) : Prop :=
  nonzero_cancel_l (x y z : A) (f : ~ X z w) (a : X (k z x) (k z y)) : X x y.

(** This has the same shape as [Z.mul_reg_r]. *)

Class IsNonzeroCancelR (A : Type) (X : A -> A -> Prop)
  (w : A) (k : A -> A -> A) : Prop :=
  nonzero_cancel_r (x y z : A) (f : ~ X z w) (a : X (k x z) (k y z)) : X x y.

Class IsNonzeroCancelLR (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  is_nonzero_cancel_l :> IsNonzeroCancelL X x k;
  is_nonzero_cancel_r :> IsNonzeroCancelR X x k;
}.
