From Coq Require
  Extraction.
From Coq Require Import
  ZArith.ZArith.
From DEZ.Offers Require Export
  OneSortedIntegerOperations.
From DEZ.Provides Require Export
  ZTheorems PolynomialTheorems.
From DEZ.ShouldOffer Require Import
  OneSortedArithmeticNotations OneSortedArithmeticOperationNotations.

(** It may not be a good idea to expand all types,
    but it does make exploring the extracted code less tedious. *)

Set Extraction TypeExpand.

Extraction Language OCaml.
Cd "gen-ocaml".
Extraction Blacklist Nat.
Recursive Extraction Library ZTheorems.
Recursive Extraction Library PolynomialTheorems.
