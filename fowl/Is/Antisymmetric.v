(** * Antisymmetry *)

From DEZ.Is Require Export
  Equivalence.

(** ** Antisymmetric Binary Relation *)

(** We cannot define [IsAntisym] as a notation for [Antisymmetric],
    because [Antisymmetric] is constrained by [Equivalence]. *)

Fail Fail Notation IsAntisym := (Antisymmetric _).

Class IsAntisym (A : Type) (X Y : A -> A -> Prop) : Prop :=
  antisym (x y : A) (a : Y x y) (b : Y y x) : X x y.

Section Context.

Context (A : Type) (X Y : A -> A -> Prop) `{!IsEquiv X}.

(** Our antisymmetry implies standard library antisymmetry. *)

#[local] Instance antisym_antisymmetric
  `{!IsAntisym X Y} : Antisymmetric A X Y.
Proof. auto. Qed.

(** Standard library antisymmetry implies our antisymmetry. *)

#[local] Instance antisymmetric_is_antisym
  `{Antisymmetric A X Y} : IsAntisym X Y.
Proof. auto. Qed.

End Context.
