From Coq Require Import
  List.
From DEZ.Has Require Export
  EquivalenceRelation Enum.
From DEZ.Is Require Export
  Setoid.
From DEZ.ShouldHave Require Import
  EquivalenceNotations.

(** TODO Prove that this is isomorphic to an initial segment of [N]. *)

Class IsFinite (A : Type) {has_eqv : HasEqv A}
  {has_enum : HasEnum A} : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  covering : forall x : A, Exists (fun y : A => x == y) enum;
  disjoint : NoDup enum;
}.
