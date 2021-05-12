From Coq Require
  Extraction.
From Coq Require Import
  ZArith.ZArith.
From Maniunfold.Offers Require Export
  OneSortedIntegerOperations.
From Maniunfold.Provides Require Export
  ZTheorems PolynomialTheorems.
From Maniunfold.ShouldOffer Require Import
  OneSortedArithmeticNotations OneSortedArithmeticOperationNotations.

(** It may not be a good idea to expand all types,
    but it does make exploring the extracted code less tedious. *)

Set Extraction TypeExpand.

Extraction Language OCaml.
Cd "gen-ocaml".
Extraction Blacklist Nat.
Recursive Extraction Library ZTheorems.
Recursive Extraction Library PolynomialTheorems.
