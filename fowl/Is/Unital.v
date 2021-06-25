(** * Unitality of a Binary Operation *)

From Maniunfold.Has Require Export
  NullaryOperation BinaryOperation Action.
From Maniunfold.ShouldHave Require Import
  MultiplicativeNotations.

(** This has the same shape as [add_0_l]. *)

Class IsUnlBinOpL (A : Type) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop :=
  unl_bin_op_l (x : A) : 1 * x = x.

Section Context.

#[local] Open Scope left_action_scope.

Class IsUnlActL (A B : Type) (Hx : HasNullOp A) (Hl : HasActL A B) : Prop :=
  unl_act_l (x : B) : 1 * x = x.

End Context.

(** This has the same shape as [add_0_r]. *)

Class IsUnlBinOpR (A : Type) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop :=
  unl_bin_op_r (x : A) : x * 1 = x.

Section Context.

#[local] Open Scope right_action_scope.

Class IsUnlActR (A B : Type) (Hx : HasNullOp A) (Hr : HasActR A B) : Prop :=
  unl_act_r (x : B) : x * 1 = x.

End Context.

Class IsUnlBinOpLR (A : Type) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_unl_bin_op_l :> IsUnlBinOpL 1 _*_;
  is_unl_bin_op_r :> IsUnlBinOpR 1 _*_;
}.

Class IsUnlActLR (A B : Type) (Hx : HasNullOp A)
  (Hl : HasActL A B) (Hr : HasActR A B) : Prop := {
  is_unl_act_l :> IsUnlActL 1 _*<_;
  is_unl_act_r :> IsUnlActR 1 _>*_;
}.

Section Context.

Context (A : Type) (Hx : HasNullOp A) (Hk : HasBinOp A).

#[local] Instance bin_op_is_unl_act_l
  `(!IsUnlBinOpL Hx Hk) : IsUnlActL Hx Hk.
Proof. intros x. apply unl_bin_op_l. Qed.

#[local] Instance bin_op_is_unl_act_r
  `(!IsUnlBinOpR Hx Hk) : IsUnlActR Hx Hk.
Proof. intros x. apply unl_bin_op_r. Qed.

#[local] Instance bin_op_is_unl_act_l_r
  `(!IsUnlBinOpLR Hx Hk) : IsUnlActLR Hx Hk Hk.
Proof. split; typeclasses eauto. Qed.

End Context.

#[export] Hint Resolve bin_op_is_unl_act_l bin_op_is_unl_act_r
  bin_op_is_unl_act_l_r : typeclass_instances.
