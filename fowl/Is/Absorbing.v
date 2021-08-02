(** * Absorptivity of a Nullary Operation over a Binary Operation *)

From Maniunfold.Has Require Export
  Zero Multiplication.
From Maniunfold.ShouldHave Require Import
  ArithmeticNotations.

Class IsAbsorbElemL (A : Type) (Hx : HasZero A) (Hk : HasMul A) : Prop :=
  absorb_elem_l (x : A) : 0 * x = 0.

Class IsAbsorbElemR (A : Type) (Hx : HasZero A) (Hk : HasMul A) : Prop :=
  absorb_elem_r (x : A) : x * 0 = 0.

Class IsAbsorbElemLR (A : Type) (Hx : HasZero A) (Hk : HasMul A) : Prop := {
  is_absorb_elem_l :> IsAbsorbElemL 0 _*_;
  is_absorb_elem_r :> IsAbsorbElemR 0 _*_;
}.

(** TODO Unary absorptivity is just a fixed point of a unary operation! *)
