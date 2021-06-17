(** * Magma or Groupoid *)

From Maniunfold.Has Require Export
  BinaryOperation.

(** This class would have some fields in the setoid model. *)

Class IsMag (A : Type) (Hk : HasBinOp A) : Prop := {}.
