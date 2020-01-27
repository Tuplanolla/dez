From Maniunfold.Has Require Export
  BinaryRelation BinaryFunction Unit Function.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsLExtInv {A B C : Type} {has_bin_rel : HasBinRel C}
  (has_bin_fn : HasBinFn B A C) (has_un : HasUn C)
  (has_fn : HasFn A B) : Prop :=
  l_ext_inv : forall x : A, >-< x >+< x ~~ 0.

(** TODO Chiral functions? *)
(*
Class IsLExtInv {A B C : Type} {has_bin_rel : HasBinRel C}
  (has_bin_fn : HasBinFn B A C) (has_l_un : HasLUn C)
  (has_l_fn : HasLFn A B) : Prop :=
  l_ext_inv : forall x : A, bin_fn (l_fn x) x ~~ l_un.

Class IsRExtInv {A B C : Type} {has_bin_rel : HasBinRel C}
  (has_bin_fn : HasBinFn B A C) (has_r_un : HasRUn C)
  (has_r_fn : HasRFn A B) : Prop :=
  r_ext_inv : forall x : A, bin_fn x (r_fn x) ~~ r_un.
*)
