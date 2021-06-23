(** * Compatibility of a Binary Operation and an Action *)

From Maniunfold.Has Require Export
  BinaryOperation Action.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsCompatL (A B : Type) (Hl : HasActL A B) (Hk : HasBinOp A) : Prop :=
  compat_l (a b : A) (x : B) : a ,+ (b ,+ x) = (a + b) ,+ x.

Class IsCompatR (A B : Type) (Hk : HasBinOp A) (Hr : HasActR A B) : Prop :=
  compat_r (x : B) (a b : A) : x +, (a + b) = (x +, a) +, b.
