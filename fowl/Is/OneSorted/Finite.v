(* bad *)
From Coq Require Import
  NArith.NArith.
From Coq Require Import
  Lists.List Logic.FinFun.
From Maniunfold.Has Require Export
  OneSorted.Enumeration OneSorted.Cardinality TwoSorted.Isomorphism.
From Maniunfold.Is Require Export
  TwoSorted.Isomorphism.
From Maniunfold.Offers Require Export
  TwoSorted.IsomorphismMappings.

Local Open Scope N_scope.

(** TODO Perhaps define another notation for [HasIso A {n : N | ...}]. *)

Class IsFin (A : Type) `{HasCard A}
  `{HasIso A {n : N | n < card A}} : Prop :=
  A_iso_is_iso :> IsIso A {n : N | n < card A} iso.

Module Export Bishop.

Class IsBFin (A : Type) `{HasEnum A} : Prop := {
  full : Full enum;
  no_dup : NoDup enum;
}.

End Bishop.

Module Export Kuratowski.

Class IsKFin (A : Type) `{HasEnum A} : Prop := {
  full : Full enum;
}.

End Kuratowski.
