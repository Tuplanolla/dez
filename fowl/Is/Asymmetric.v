(** * Asymmetry *)

From Coq Require Import
  Classes.RelationClasses.
From DEZ Require Export
  Init.

(** ** Asymmetric Binary Relation *)

Fail Fail Class IsAsym (A : Type) (X : A -> A -> Prop) : Prop :=
  asym (x y : A) (a : X x y) (b : X y x) : 0.

Arguments Asymmetric {_} _.
Arguments asymmetry {_ _ _} _ _ _ _.

Notation IsAsym := Asymmetric.
Notation asym := asymmetry.
