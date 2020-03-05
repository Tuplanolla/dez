From Maniunfold.Has Require Export
  EquivalenceRelation Negation Multiplication One.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsRSgnAbsorb {A : Type} {has_eq_rel : HasEqRel A}
  (has_neg : HasNeg A) (has_mul : HasMul A) (has_one : HasOne A) : Prop :=
  r_sgn_absorb : forall x : A, x * (- (1)) == - x.
