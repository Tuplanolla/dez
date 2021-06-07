(* bad *)
From Coq Require Import
  NArith.NArith.
From Coq Require Import
  Lists.List Logic.FinFun.
From Maniunfold.Has Require Export
  OneSortedEnumeration OneSortedCardinality.
From Maniunfold.Is Require Export
  Isomorphism.

Local Open Scope N_scope.

(** TODO Perhaps define another notation for [HasIso A {n : N | ...}]. *)

Class IsFin (A : Type) `(HasCard A)
  (f : A -> {n : N | n < card A})
  (g : {n : N | n < card A} -> A) : Prop :=
  A_iso_is_iso :> IsIso f g.

Module Export Bishop.

Class IsBFin (A : Type) `(HasEnum A) : Prop := {
  full : Full enum;
  no_dup : NoDup enum;
}.

End Bishop.

Module Export Kuratowski.

Class IsKFin (A : Type) `(HasEnum A) : Prop := {
  full : Full enum;
}.

End Kuratowski.
