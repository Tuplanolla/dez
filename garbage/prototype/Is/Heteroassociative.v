From DEZ.Has Require Export
  EquivalenceRelation ScalarOperations.
From DEZ.Is Require Export
  Setoid.
From DEZ.ShouldHave Require Import
  EquivalenceNotations.

Import AdditiveNotations.

Class IsHeteroassociative {LS RS A : Type} {has_eqv : HasEqv A}
  (has_lopr : HasLOpr LS A) (has_ropr : HasROpr RS A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  heteroassociative : forall (a : LS) (x : A) (b : RS),
    a <+ (x +> b) == (a <+ x) +> b;
}.
