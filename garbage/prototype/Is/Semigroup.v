From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation.
From Maniunfold.Is Require Export
  Proper Setoid Associative.
From Maniunfold.ShouldHave Require Import
  AdditiveGroupNotations.

Class IsSemigroup {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) : Prop := {
  opr_is_proper :> IsProper (eqv ==> eqv ==> eqv) opr;
  opr_is_associative :> IsAssociative opr;
}.
