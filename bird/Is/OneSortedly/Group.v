From Maniunfold.Has.OneSorted Require Export
  BinaryOperation Unit UnaryOperation.
From Maniunfold.Is.OneSortedly Require Export
  Monoid Invertible
  LeftCancellative RightCancellative Cancellative
  UnaryAntidistributive Injective Involutive UnaryAbsorbing.
From Maniunfold.ShouldHave.OneSorted Require Import
  AdditiveNotations.

(** TODO What happens with
    group (using [a b c ...]) actions over a type (using [x y z ...])?

    - [(a + b) L+ x = a L+ (b L+ x)]
    - [x R+ (a + b) = (x R+ a) R+ b]
    - [0 L+ x = x]
    - [x R+ 0 = x]
    - [- a L+ x = y -> x = a L+ x]?
    - [x R+ - a = y -> x = y R+ a]?
    - [- a L+ x = x R+ a]?
    - [x R+ - a = a L+ x]? *)

Class IsGrp {A : Type} (has_bin_op : HasBinOp A)
  (has_un : HasUn A) (has_un_op : HasUnOp A) : Prop := {
  bin_op_un_is_mon :> IsMon bin_op un;
  bin_op_un_un_op_is_inv :> IsInv bin_op un un_op;
}.

Section Context.

Context {A : Type} `{is_grp : IsGrp A}.

Theorem bin_op_l_cancel : forall x y z : A,
  z + x = z + y -> x = y.
Proof.
  intros x y z H.
  rewrite <- (l_unl x).
  rewrite <- (l_inv z).
  rewrite <- (assoc (- z) z x).
  rewrite H.
  rewrite (assoc (- z) z y).
  rewrite (l_inv z).
  rewrite (l_unl y).
  reflexivity. Qed.

Global Instance bin_op_is_l_cancel : IsLCancel bin_op.
Proof. intros x y z. apply bin_op_l_cancel. Qed.

Theorem bin_op_r_cancel : forall x y z : A,
  x + z = y + z -> x = y.
Proof.
  intros x y z H.
  rewrite <- (r_unl x).
  rewrite <- (r_inv z).
  rewrite (assoc x z (- z)).
  rewrite H.
  rewrite <- (assoc y z (- z)).
  rewrite (r_inv z).
  rewrite (r_unl y).
  reflexivity. Qed.

Global Instance bin_op_is_r_cancel : IsRCancel bin_op.
Proof. intros x y z. apply bin_op_r_cancel. Qed.

Global Instance bin_op_is_cancel : IsCancel bin_op.
Proof. constructor; typeclasses eauto. Qed.

Theorem bin_op_un_op_un_antidistr : forall x y : A,
  - (x + y) = - y + - x.
Proof.
  intros x y.
  apply (bin_op_l_cancel (- (x + y)) (- y + - x) (x + y)).
  rewrite (r_inv (x + y)).
  rewrite (assoc (x + y) (- y) (- x)).
  rewrite <- (assoc x y (- y)).
  rewrite (r_inv y).
  rewrite (r_unl x).
  rewrite (r_inv x).
  reflexivity. Qed.

Global Instance bin_op_un_op_is_un_antidistr : IsUnAntidistr bin_op un_op.
Proof. intros x y. apply bin_op_un_op_un_antidistr. Qed.

Theorem un_op_inj : forall x y : A,
  - x = - y -> x = y.
Proof.
  intros x y H.
  rewrite <- (l_unl y).
  rewrite <- (r_inv x).
  rewrite H.
  rewrite <- (assoc x (- y) y).
  rewrite (l_inv y).
  rewrite (r_unl x).
  reflexivity. Qed.

Global Instance un_op_is_inj : IsInj un_op.
Proof. intros x y. apply un_op_inj. Qed.

Theorem un_op_invol : forall x : A,
  - - x = x.
Proof.
  intros x.
  rewrite <- (r_unl (- - x)).
  rewrite <- (l_inv x).
  rewrite (assoc (- - x) (- x) x).
  rewrite (l_inv (- x)).
  rewrite (l_unl x).
  reflexivity. Qed.

Global Instance un_op_is_invol : IsInvol un_op.
Proof. intros x. apply un_op_invol. Qed.

Theorem un_un_op_un_absorb : - 0 = 0.
Proof.
  rewrite <- (r_unl (- 0)).
  rewrite (l_inv 0).
  reflexivity. Qed.

Global Instance un_un_op_is_un_absorb : IsUnAbsorb un un_op.
Proof. apply un_un_op_un_absorb. Qed.

End Context.
