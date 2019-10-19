From Coq Require Import
  List.
From Maniunfold.Has Require Export
  EquivalenceRelation Enum.
From Maniunfold.Is Require Export
  Setoid.

(** TODO Prove that this is isomorphic to an initial segment of [N]. *)

Class IsFinite (A : Type) {has_eqv : HasEqv A}
  {has_enum : HasEnum A} : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  covering : forall x : A, Exists (fun y : A => x == y) enum;
  disjoint : NoDup enum;
}.
