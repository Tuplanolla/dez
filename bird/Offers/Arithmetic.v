From Maniunfold.Has Require Export
  Addition Negation Multiplication Reciprocation.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Definition sub {A : Type} {has_add : HasAdd A} {has_neg : HasNeg A}
  (x y : A) : A := add x (neg y).

Definition div {A : Type} {has_mul : HasMul A} {has_recip : HasRecip A}
  (x y : A) : A := mul x (recip y).
