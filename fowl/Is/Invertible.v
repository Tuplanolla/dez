(** * Invertibility of a Unary Operation over a Binary Operation *)

From DEZ.Has Require Export
  NullaryOperation UnaryOperation BinaryOperation.
From DEZ.ShouldHave Require Import
  AdditiveNotations.

Class IsInvL (A : Type)
  (Hx : HasNullOp A) (Hf : HasUnOp A) (Hk : HasBinOp A) : Prop :=
  inv_l (x : A) : (- x) + x = 0.

Class IsInvR (A : Type)
  (Hx : HasNullOp A) (Hf : HasUnOp A) (Hk : HasBinOp A) : Prop :=
  inv_r (x : A) : x + (- x) = 0.

Class IsInvLR (A : Type)
  (Hx : HasNullOp A) (Hf : HasUnOp A) (Hk : HasBinOp A) : Prop := {
  is_inv_l :> IsInvL 0 -_ _+_;
  is_inv_r :> IsInvR 0 -_ _+_;
}.
