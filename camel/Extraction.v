From Coq Require
  extraction.Extraction.
From Coq Require Import
  PArith.PArith.
From Maniunfold.Provides Require Export
  PositiveTheorems.

Extraction Language OCaml.
Cd "gen-ocaml".
Recursive Extraction Library PositiveTheorems.
