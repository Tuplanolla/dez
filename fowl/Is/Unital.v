(** * Unitality of a Binary Operation *)

From Maniunfold.Has Require Export
  NullaryOperation BinaryOperation Action.
From Maniunfold.ShouldHave Require Import
  MultiplicativeNotations.

(** This has the same shape as [add_0_l]. *)

Class IsUnlBinOpL (A : Type) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop :=
  unl_bin_op_l (x : A) : 1 * x = x.

Class IsUnlActL (A B : Type) (Hx : HasNullOp A) (Hl : HasActL A B) : Prop :=
  unl_act_l (x : B) : 1 ,* x = x.

(** This has the same shape as [add_0_r]. *)

Class IsUnlBinOpR (A : Type) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop :=
  unl_bin_op_r (x : A) : x * 1 = x.

Class IsUnlActR (A B : Type) (Hx : HasNullOp A) (Hr : HasActR A B) : Prop :=
  unl_act_r (x : B) : x *, 1 = x.

Class IsUnlBinOp (A : Type) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_unl_bin_op_l :> IsUnlBinOpL 1 _*_;
  is_unl_bin_op_r :> IsUnlBinOpR 1 _*_;
}.

Class IsUnlActLR (A B : Type) (Hx : HasNullOp A)
  (Hl : HasActL A B) (Hr : HasActR A B) : Prop := {
  is_unl_act_l :> IsUnlActL 1 _,*_;
  is_unl_act_r :> IsUnlActR 1 _*,_;
}.

From Maniunfold.Is Require Export
  OneSortedLeftUnital OneSortedRightUnital TwoSortedUnital.

Class IsUnl (A : Type) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_l_unl :> IsLUnl Hk Hx;
  is_r_unl :> IsRUnl Hk Hx;
}.

Section Context.

Context (A : Type) (Hx : HasNullOp A) (Hk : HasBinOp A) `(!IsUnl Hx Hk).

Global Instance A_A_bin_op_bin_op_null_op_is_two_unl :
  IsTwoUnl bin_op bin_op null_op.
Proof. split; typeclasses eauto. Qed.

End Context.
