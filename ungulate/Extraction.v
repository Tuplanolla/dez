From Coq Require
  extraction.Extraction.
From Coq Require Import
  ZArith.ZArith.
From Maniunfold.Offers Require Export
  IntegerOperations.
From Maniunfold.Provides Require Export
  ZTheorems.
From Maniunfold.ShouldOffer Require Import
  OneSorted.ArithmeticNotations OneSorted.ArithmeticOperationNotations.

(** This works, but we want to do something complicated for its own sake. *)

(* Definition monkey_saddle (x y : Z) : Z := x * (x ^ 2 - 3 * y ^ 2). *)

Definition monkey_saddle (x y : Z) : Z :=
  (x * ((x ^ 2)%N - (1 + 1 + 1) * (y ^ 2)%N))%ring.

Extraction Language OCaml.
Extraction "extraction.ml" monkey_saddle.

(** We want to eventually do this.
    However, currently this creates a mess of files. *)

(* Recursive Extraction Library ZTheorems. *)
