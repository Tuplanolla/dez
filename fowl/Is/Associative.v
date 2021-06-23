(** * Associativity of a Binary Operation and an Action *)

From Maniunfold.Has Require Export
  BinaryOperation Action.
From Maniunfold.Is Require Export
  Compatible.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsAssoc (A : Type) (Hk : HasBinOp A) : Prop :=
  assoc (x y z : A) : x + (y + z) = (x + y) + z.

Class IsCompat (A B C : Type) (Hl : HasActL A C) (Hr : HasActR B C) : Prop :=
  compat (a : A) (x : C) (b : B) : a ,+ (x +, b) = (a ,+ x) +, b.

Section Context.

Context (A : Type) (Hk : HasBinOp A) `(!IsAssoc _+_).

#[local] Instance is_compat : IsCompat _+_ _+_.
Proof. intros a x b. apply assoc. Qed.

#[local] Instance is_compat_l : IsCompatL _+_ _+_.
Proof. intros a b x. apply assoc. Qed.

#[local] Instance is_compat_r : IsCompatR _+_ _+_.
Proof. intros x a b. apply assoc. Qed.

End Context.

#[export] Hint Resolve is_compat is_compat_l is_compat_r : typeclass_instances.
