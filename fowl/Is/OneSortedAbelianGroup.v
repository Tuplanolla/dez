From DEZ.Has Require Export
  BinaryOperation NullaryOperation
  UnaryOperation.
From DEZ.Is Require Export
  Commutative Group Distributive.
From DEZ.ShouldHave Require Import
  AdditiveNotations.

(** Abelian group, commutative group. *)

Class IsAbGrp (A : Type) `(HasBinOp A)
  `(HasNullOp A) `(HasUnOp A) : Prop := {
  A_bin_op_is_comm :> IsCommBinOp (bin_op (A := A));
  A_bin_op_null_op_un_op_is_grp :> IsGrp null_op un_op bin_op;
}.

Section Context.

Context (A : Type) `{IsAbGrp A}.

#[local] Instance is_distr : IsDistr -_ _+_ _+_.
Proof.
  intros x y.
  rewrite (comm_bin_op x y).
  apply (antidistr y x). Qed.

End Context.

#[export] Hint Resolve is_distr : typeclass_instances.
