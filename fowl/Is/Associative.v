(** * Associativity of a Binary Operation and Compatibility of an Action *)

From Maniunfold.Has Require Export
  BinaryOperation Action.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsAssoc (A : Type) (Hk : HasBinOp A) : Prop :=
  assoc (x y z : A) : x + (y + z) = (x + y) + z.

Class IsCompatL (A B : Type) (Hk : HasBinOp A) (Hl : HasActL A B) : Prop :=
  compat_l (a b : A) (x : B) : act_l a (act_l b x) = act_l (a + b) x.
  (* compat_l (a b : A) (x : B) : a * (b * x) = (a * b) * x. *)

Class IsCompatR (A B : Type) (Hk : HasBinOp A) (Hr : HasActR A B) : Prop :=
  compat_r (x : B) (a b : A) : act_r x (a + b) = act_r (act_r x a) b.
  (* compat_r (x : B) (a b : A) : x * (a * b) = (x * a) * b. *)

Class IsBicompat (A B C : Type) (Hl : HasActL A C) (Hr : HasActR B C) : Prop :=
  bicompat (a : A) (x : C) (b : B) : act_l a (act_r x b) = act_r (act_l a x) b.
  (* bicompat (a : A) (x : C) (b : B) : a * (x * b) = (a * x) * b. *)

Section Context.

Context (A : Type) (Hk : HasBinOp A) `(!IsAssoc _+_).

#[local] Instance is_bicompat : IsBicompat _+_ _+_.
Proof. intros x y z. apply assoc. Qed.

End Context.

#[export] Hint Resolve is_bicompat : typeclass_instances.
