From Coq Require
  Extraction.
From Coq Require Import
  ZArith.
From Maniunfold.Offers Require Export
  NaturalPowers.
From Maniunfold.Provides Require Export
  ZTheorems.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.
From Maniunfold.ShouldOffer Require Import
  MoreAdditiveNotations.

(** This works, but we want to do something complicated for its own sake. *)
(* Definition monkey_saddle (x y : Z) : Z := x * (x ^ 2 - 3 * y ^ 2). *)
Definition monkey_saddle (x y : Z) : Z :=
  bin_op (HasBinOp := Multiplicative.Z_mul_has_bin_op) x
  (Z.sub (nat_op 2 x)
    (bin_op (HasBinOp := Multiplicative.Z_mul_has_bin_op) 3%Z (nat_op 2 y))).

Extraction Language OCaml.
Extraction "extraction.ml" monkey_saddle.
