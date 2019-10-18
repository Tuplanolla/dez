From Coq Require Import
  List NArith.
From Maniunfold.Is Require Import
  NontrivialRing FinitelyEnumerable.
From Maniunfold.Justifies Require Import
  OptionTheorems ZTheorems FiniteTheorems.

Import ListNotations.

(** TODO This representation is garbage. *)

Inductive poly {A : Type} `{is_nontrivial_ring : IsNontrivialRing A} : Type :=
  | poly_list (xs : list A) (H : hd_error xs =/= Some 0) : poly.

Arguments poly _ {_ _ _ _ _ _ _}.

Section Suffering.

Context {A : Type} `{is_nontrivial_ring : IsNontrivialRing A}.

Definition poly_eqv (xs ys : poly A) : Prop := xs = ys.

Global Instance : HasEqv (poly A) := poly_eqv.

Global Instance : IsReflexive poly_eqv := {}.
Proof. intros xs. reflexivity. Qed.

Global Instance : IsSymmetric poly_eqv := {}.
Proof. intros xs ys H. symmetry; auto. Qed.

Global Instance : IsTransitive poly_eqv := {}.
Proof. intros xs ys zs Hxy Hyz. etransitivity; eauto. Qed.

Global Instance : IsSetoid poly_eqv := {}.

Program Definition poly_add (xs ys : poly A) : poly A.
Proof.
  destruct xs as [xs Hx], ys as [ys Hy].
  induction xs as [| x xs IHx].
  - apply (poly_list ys). apply Hy.
  - induction ys as [| y ys IHy].
    + apply (poly_list (x :: xs)). apply Hx.
    + cbn in *. apply (poly_list ((x + y) :: xs)). cbn in *.
      (** TODO This would require a decision procedure for zero. *) Admitted.

Global Instance : HasAdd (poly A) :=
  poly_add.

Program Definition poly_zero : poly A :=
  poly_list [] _.

Global Instance : HasZero (poly A) := poly_zero.

Definition poly_neg (x : poly A) : poly A.
Proof. Admitted.

Global Instance : HasNeg (poly A) := poly_neg.

Definition poly_mul (x y : poly A) : poly A.
Proof. Admitted.

Global Instance : HasMul (poly A) := poly_mul.

(** TODO It is impossible to construct a polynomial ring
    over a trivial ring, so this does not hold in this case. *)

Program Definition poly_one : poly A :=
  poly_list [one] _.
Next Obligation. cbn. apply nontrivial_ring_nontrivial. Qed.

Global Instance : HasOne (poly A) := poly_one.

Global Instance :
  IsRing poly_add poly_zero poly_neg poly_mul poly_zero := {}.
Proof. Admitted.

End Suffering.
