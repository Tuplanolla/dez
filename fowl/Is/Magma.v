(** * Magma or Groupoid *)

From DEZ.Has Require Export
  BinaryOperation.

(** This class would have some fields if we used the setoid model. *)

Class IsMag (A : Type) (Hk : HasBinOp A) : Prop := {}.
