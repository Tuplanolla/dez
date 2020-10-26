From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.UnaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Monoid OneSorted.Invertible
  OneSorted.Cancellative OneSorted.UnaryAntidistributive OneSorted.Injective
  OneSorted.Involutive OneSorted.UnaryAbsorbing.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Group, invertible monoid. *)

Class IsGrp (A : Type) `(HasBinOp A) `(HasNullOp A) `(HasUnOp A) : Prop := {
  bin_op_null_op_is_mon :> IsMon bin_op null_op;
  bin_op_null_op_un_op_is_inv :> IsInv bin_op null_op un_op;
}.

Section Context.

Context (A : Type) `(IsGrp A).

Let bin_op : HasBinOp A := bin_op (A := A).

Theorem bin_op_l_cancel (x y z : A) (e : z + x = z + y) : x = y.
Proof.
  rewrite <- (l_unl x).
  rewrite <- (l_inv z).
  rewrite <- (assoc (- z) z x).
  rewrite e.
  rewrite (assoc (- z) z y).
  rewrite (l_inv z).
  rewrite (l_unl y).
  reflexivity. Defined.

Global Instance bin_op_is_l_cancel : IsLCancel bin_op.
Proof. exact @bin_op_l_cancel. Defined.

Theorem bin_op_r_cancel (x y z : A) (e : x + z = y + z) : x = y.
Proof.
  rewrite <- (r_unl x).
  rewrite <- (r_inv z).
  rewrite (assoc x z (- z)).
  rewrite e.
  rewrite <- (assoc y z (- z)).
  rewrite (r_inv z).
  rewrite (r_unl y).
  reflexivity. Defined.

Global Instance bin_op_is_r_cancel : IsRCancel bin_op.
Proof. exact @bin_op_r_cancel. Defined.

Global Instance bin_op_is_cancel : IsCancel bin_op.
Proof. split; typeclasses eauto. Defined.

Theorem bin_op_un_op_un_antidistr (x y : A) : - (x + y) = (- y) + (- x).
Proof.
  apply (l_cancel (- (x + y)) ((- y) + (- x)) (x + y)).
  rewrite (r_inv (x + y)).
  rewrite (assoc (x + y) (- y) (- x)).
  rewrite <- (assoc x y (- y)).
  rewrite (r_inv y).
  rewrite (r_unl x).
  rewrite (r_inv x).
  reflexivity. Defined.

Global Instance bin_op_un_op_is_un_antidistr : IsUnAntidistr bin_op un_op.
Proof. exact @bin_op_un_op_un_antidistr. Defined.

Theorem un_op_inj (x y : A) (e : - x = - y) : x = y.
Proof.
  rewrite <- (l_unl y).
  rewrite <- (r_inv x).
  rewrite e.
  rewrite <- (assoc x (- y) y).
  rewrite (l_inv y).
  rewrite (r_unl x).
  reflexivity. Defined.

Global Instance un_op_is_inj : IsInj un_op.
Proof. exact @un_op_inj. Defined.

Theorem un_op_invol (x : A) : - - x = x.
Proof.
  rewrite <- (r_unl (- (- x))).
  rewrite <- (l_inv x).
  rewrite (assoc (- (- x)) (- x) x).
  rewrite (l_inv (- x)).
  rewrite (l_unl x).
  reflexivity. Defined.

Global Instance un_op_is_invol : IsInvol un_op.
Proof. exact @un_op_invol. Defined.

Theorem null_op_un_op_un_absorb : - 0 = 0.
Proof.
  rewrite <- (r_unl (- 0)).
  rewrite (l_inv 0).
  reflexivity. Defined.

Global Instance null_op_un_op_is_un_absorb : IsUnAbsorb null_op un_op.
Proof. exact @null_op_un_op_un_absorb. Defined.

End Context.
