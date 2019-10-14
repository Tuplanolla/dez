From Coq Require Import NArith.
From Maniunfold.Is Require Import
  Ring FinitelyEnumerable.
From Maniunfold.Justifies Require Import
  NTheorems FiniteTheorems.

Section Suffering.

(** TODO Use this nice thing more. *)

Context {A : Type} `{is_setoid : IsSetoid A}.

Global Instance list_has_eqv : HasEqv (list A) := fun xs ys : list A =>
  List.Forall2 (fun x y : A => x == y) xs ys.

Global Instance list_is_reflexive : IsReflexive (list A) := {}.
Proof. Admitted.

Global Instance list_is_symmetric : IsSymmetric (list A) := {}.
Proof. Admitted.

Global Instance list_is_transitive : IsTransitive (list A) := {}.
Proof. Admitted.

Global Instance list_is_setoid : IsSetoid (list A) := {}.

End Suffering.

Instance list_has_add {A : Type} `{is_ring : IsRing A} : HasAdd (list A) :=
  fun xs ys : list A =>
  List.map (fun p : A * A => add (fst p) (snd p)) (List.combine xs ys).

Instance list_has_zero {A : Type} `{is_ring : IsRing A} : HasZero (list A) :=
  nil.

Instance list_has_neg {A : Type} `{is_ring : IsRing A} : HasNeg (list A) :=
  fun xs : list A => List.map (fun x : A => neg x) xs.

Instance list_has_mul {A : Type} `{is_ring : IsRing A} : HasMul (list A) :=
  fun xs ys : list A =>
  List.map (fun p : A * A => mul (fst p) (snd p)) (List.combine xs ys).

(** TODO This is complete nonsense. *)

Instance list_has_one {A : Type} `{is_ring : IsRing A} : HasOne (list A) :=
  nil.

Instance list_is_ring {A : Type} `{is_ring : IsRing A} : IsRing (list A) := {}.
Proof. Abort.
