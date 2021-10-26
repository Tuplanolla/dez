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

Context (A : Type) (X Y : A -> A -> Prop) `(!IsEq X).

(** Our definition is equivalent to the one in the standard library. *)

#[local] Instance is_antisym `(!Antisymmetric A X Y) : IsAntisym X Y.
Proof. auto. Qed.

#[local] Instance antisymmetric `(!IsAntisym X Y) : Antisymmetric A X Y.
Proof. auto. Qed.

End Context.

#[export] Hint Resolve is_antisym : typeclass_instances.
