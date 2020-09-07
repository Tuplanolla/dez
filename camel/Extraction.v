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

Extraction Language OCaml.
Cd "gen-ocaml".
Extraction Blacklist Nat.
Recursive Extraction Library ZTheorems.
