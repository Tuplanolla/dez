(* bad *)
From Coq Require Import
  NArith.NArith.
From Maniunfold.Has Require Export
  OneSorted.Cardinality TwoSorted.Isomorphism.
From Maniunfold.Is Require Export
  TwoSorted.Isomorphism.
From Maniunfold.Offers Require Export
  TwoSorted.IsomorphismMappings.

Local Open Scope N_scope.

(** TODO Perhaps define another notation for [HasIso A {n : N | ...}]. *)

Class IsFin (A : Type) {A_has_card : HasCard A}
  {A_has_iso : HasIso A {n : N | n < card A}} : Prop :=
  A_iso_is_iso :> IsIso A {n : N | n < card A} iso.
