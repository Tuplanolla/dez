From Coq Require Import List NArith.
From Maniunfold.Is Require Import
  Ring FinitelyEnumerable.
From Maniunfold.Justifies Require Import
  OptionTheorems NTheorems FiniteTheorems.

(** TODO This whole thing is total and complete nonsense. *)

Import ListNotations.

Inductive poly (A : Type) `{is_ring : IsRing A} : Type :=
  | lift : forall xs : list A, ~ hd_error xs == Some 0 -> poly A.

Section Suffering.

Context {A : Type} `{is_ring : IsRing A}.

Global Instance poly_has_eqv : HasEqv (poly A) := fun xs ys : poly A =>
  xs = ys.

Global Instance poly_is_reflexive : IsReflexive (poly A) := {}.
Proof. intros xs. reflexivity. Qed.

Global Instance poly_is_symmetric : IsSymmetric (poly A) := {}.
Proof. intros xs ys H. symmetry; auto. Qed.

Global Instance poly_is_transitive : IsTransitive (poly A) := {}.
Proof. intros xs ys zs H0 H1. etransitivity; eauto. Qed.

Global Instance poly_is_setoid : IsSetoid (poly A) := {}.

Program Fixpoint poly_add (xs ys : poly A) : poly A :=
  match xs, ys with
  | lift _ xs _, lift _ ys _ =>
    lift _ (map (fun p : A * A => add (fst p) (snd p)) (combine xs ys)) _
  end.
Next Obligation.
  intros H. clear wildcard' wildcard'0.
  induction xs as [| x xs IHxs]; destruct ys as [| y ys];
    try (cbn in *; congruence). Admitted.

Instance poly_has_add : HasAdd (poly A) :=
  poly_add.

Instance poly_has_zero : HasZero (poly A) :=
  lift _ nil _.
Proof. intros H. cbv in H. inversion H. Qed.

Instance poly_has_neg : HasNeg (poly A) := {}.
Proof. Admitted.

Instance poly_has_mul : HasMul (poly A) := {}.
Proof. Admitted.

(** TODO In a trivial ring, we have [0 == 1] and this condition is unique. *)

Instance poly_has_one : HasOne (poly A) :=
  lift _ [one] _.
Proof. cbn. intros H. idtac "uh oh". Admitted.

Instance poly_is_ring : IsRing (poly A) := {}.
Proof. Admitted.

End Suffering.
