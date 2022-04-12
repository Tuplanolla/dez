(** * Antisymmetry *)

From Coq Require Import
  Classes.RelationClasses.
From DEZ.Is Require Export
  Equivalence.

(** ** Antisymmetric Binary Relation *)

(** We cannot define [IsAntisym] as a notation for [Antisymmetric],
    because [Antisymmetric] is constrained by [Equivalence]. *)

Fail Fail Notation IsAntisym := (Antisymmetric _).

Class IsAntisym (A : Type) (Xeq Xle : A -> A -> Prop) : Prop :=
  antisym (x y : A) (a : Xle x y) (b : Xle y x) : Xeq x y.

Section Context.

Context (A : Type) (Xeq Xle : A -> A -> Prop).

(** Our antisymmetry implies standard library antisymmetry. *)

#[local] Instance antisym_antisymmetric
  `{!IsEquiv Xeq} `{!IsAntisym Xeq Xle} : Antisymmetric A Xeq Xle.
Proof. auto. Qed.

(** Standard library antisymmetry implies our antisymmetry. *)

#[local] Instance antisymmetric_is_antisym
  `{!Equivalence Xeq} `{!Antisymmetric A Xeq Xle} : IsAntisym Xeq Xle.
Proof. auto. Qed.

End Context.
