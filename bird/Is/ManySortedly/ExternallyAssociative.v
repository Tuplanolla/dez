From Maniunfold.Has Require Export
  BinaryRelation LeftExternalBinaryOperation RightExternalBinaryOperation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

(** TODO In literature, external associativity may be different.
    Some say that it should be [(a × b) ⋅ x = a ⋅ (b ⋅ x)].
    Others say that is called (semigroup) action compatibility. *)

Class IsExtAssoc {A B C : Type} {has_bin_rel : HasBinRel C}
  (has_l_ext_bin_op : HasLExtBinOp A C)
  (has_r_ext_bin_op : HasRExtBinOp B C) : Prop :=
  ext_assoc : forall (x : A) (y : C) (z : B), x L+ (y R+ z) ~~ (x L+ y) R+ z.
