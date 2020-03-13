From Maniunfold.Has Require Export
  BinaryOperation Unit GradedBinaryOperation GradedUnit.
From Maniunfold.Is Require Export
  LeftModule AbelianGroup RightCompatible.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations ArithmeticNotations.

Class IsLAlg {A B : Type}
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (B_has_mul : HasMul B) (has_l_act : HasLAct A B) : Prop := {
  this_is_l_mod :>
    IsLMod (A := A) (B := B) add zero neg mul one add zero neg l_act;
  (* z * (x + y) = z * x + z * y /\
     (x + y) * z = x * z + y * z *)
  the_distr :> IsDistr (A := B) add mul;
  (* a * (x * y) = (a * x) * y *)
  the_l_wtf : forall (a : A) (x y : B),
    a L* (x * y) = (a L* x) * y;
  (* x * (b * y) = b * (x * y) *)
  the_r_wtf : forall (a : A) (x y : B),
    x * (a L* y) = a L* (x * y);
  (** These two are equivalent to the following. *)
  (* (a * b) * (x * y) = (a * x) * (b * y) *)
}.
