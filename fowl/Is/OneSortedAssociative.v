(** * Associativity and Compatibility of a Binary Operation *)

From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsAssoc (A : Type) (f : HasBinOp A) : Prop :=
  assoc (x y z : A) : x + (y + z) = (x + y) + z.

Class IsCompatL (A B : Type) (f : HasBinOp A) (l : HasActL A B) : Prop :=
  compat_l (a b : A) (x : B) : l a (l b x) = l (f a b) x.
  (* compat_l (a b : A) (x : B) : a * (b * x) = (a * b) * x. *)

Class IsCompatR (A B : Type) (f : HasBinOp A) (r : HasActR A B) : Prop :=
  compat_r (x : B) (a b : A) : r x (f a b) = r (r x a) b.
  (* compat_r (x : B) (a b : A) : x * (a * b) = (x * a) * b. *)

Class IsBicompat (A B C : Type) (l : HasActL A C) (r : HasActR B C) : Prop :=
  bicompat (a : A) (x : C) (b : B) : l a (r x b) = r (l a x) b.
  (* bicompat (a : A) (x : C) (b : B) : a * (x * b) = (a * x) * b. *)

Section Context.

Context (A : Type) (f : HasBinOp A) `(!IsAssoc f).

#[local] Instance is_bicompat : IsBicompat f f.
Proof. intros x y z. apply assoc. Qed.

End Context.

#[export] Hint Resolve is_bicompat : typeclass_instances.
