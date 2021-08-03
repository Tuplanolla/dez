(** * Cancellativity of a Binary Operation *)

From Coq Require Import
  Logic.FunctionalExtensionality.
From Maniunfold.Has Require Export
  NullaryOperation BinaryOperation.
From Maniunfold.Is Require Export
  Injective.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsCancelL (A : Type) (Hk : HasBinOp A) : Prop :=
  cancel_l (x y z : A) (a : z + x = z + y) : x = y.

(** This has the same shape as [add_reg_l]. *)

Class IsCancelR (A : Type) (Hk : HasBinOp A) : Prop :=
  cancel_r (x y z : A) (a : x + z = y + z) : x = y.

Class IsCancelLR (A : Type) (Hk : HasBinOp A) : Prop := {
  is_cancel_l :> IsCancelL _+_;
  is_cancel_r :> IsCancelR _+_;
}.

(** This has the same shape as [mul_reg_l]. *)

Class IsNonzeroCancelL (A : Type)
  (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop :=
  nonzero_cancel_l (x y z : A) (f : z <> 0) (a : z + x = z + y) : x = y.

(** This has the same shape as [mul_reg_r]. *)

Class IsNonzeroCancelR (A : Type)
  (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop :=
  nonzero_cancel_r (x y z : A) (f : z <> 0) (a : x + z = y + z) : x = y.

Class IsNonzeroCancelLR (A : Type)
  (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_nonzero_cancel_l :> IsNonzeroCancelL 0 _+_;
  is_nonzero_cancel_r :> IsNonzeroCancelR 0 _+_;
}.

Module LFromR.

Section Context.

Context (A : Type) (Hk : HasBinOp A) `(!IsCancelL _+_).

(** Flipped right cancellation is a left cancellation. *)

#[local] Instance is_cancel_r : IsCancelR (flip _+_).
Proof.
  intros x y z a.
  (** This is really stupid. *)
  change _+_ with (flip _+_) in a.
  unfold flip in a.
  apply cancel_l in a.
  apply a. Qed.

End Context.

#[export] Hint Resolve is_cancel_r : typeclass_instances.

End LFromR.

Module RFromL.

Section Context.

Context (A : Type) (Hk : HasBinOp A) `(!IsCancelR _+_).

(** Flipped left cancellation is a right cancellation. *)

#[local] Instance is_cancel_l : IsCancelL (flip _+_).
Proof.
  intros x y z a.
  (** This is really stupid. *)
  change _+_ with (flip _+_) in a.
  unfold flip in a.
  apply cancel_r in a.
  apply a. Qed.

End Context.

#[export] Hint Resolve is_cancel_l : typeclass_instances.

End RFromL.

Section Context.

Context (A : Type) (Hk : HasBinOp A).

(** Cancellativity is just injectivity of partial applications. *)

#[local] Instance cancel_r_is_inj `(!IsCancelR _+_) : IsInj _+_.
Proof.
  intros x y a.
  assert (z : A) by assumption.
  pose proof equal_f a z as a'.
  apply cancel_r in a'.
  apply a'. Qed.

#[local] Instance cancel_l_is_inj `(!IsCancelL _+_) : IsInj (flip _+_).
Proof.
  intros x y a.
  assert (z : A) by assumption.
  pose proof equal_f a z as a'.
  unfold flip in a'.
  apply cancel_l in a'.
  apply a'. Qed.

End Context.

#[export] Hint Resolve cancel_r_is_inj cancel_l_is_inj : typeclass_instances.
