From Maniunfold.Has Require Export
  GradedBinaryOperation GradedNullaryOperation GradedUnaryOperation.
From Maniunfold.Offers Require Export
  PositivePowers NaturalPowers IntegerPowers.
From Maniunfold.ShouldHave Require Export
  AdditiveNotations.

Notation "n '*' x" := (positive_op n x) : positive_scope.
Notation "n '*' x" := (nat_op n x) : nat_scope.
Notation "n '*' x" := (n_op n x) : N_scope.
Notation "n '*' x" := (z_op n x) : Z_scope.

(** TODO Move into [ShouldHave.Graded.AdditiveNotations]. *)

Reserved Notation "x 'G+' y" (at level 50, left associativity).
Reserved Notation "'G0'" (at level 0, no associativity).
Reserved Notation "'G-' x" (at level 35, right associativity).

Notation "x 'G+' y" := (grd_bin_op _ _ x y) : algebra_scope.
Notation "'G0'" := grd_un : algebra_scope.
Notation "'G-' x" := (grd_un_op _ x) : algebra_scope.

(** TODO Move into [ShouldHave.Graded.MultiplicativeNotations]. *)

Reserved Notation "x 'G*' y" (at level 40, left associativity).
Reserved Notation "'G1'" (at level 0, no associativity).
Reserved Notation "'G/' x" (at level 35, right associativity).

Notation "x 'G*' y" := (grd_bin_op _ _ x y) : algebra_scope.
Notation "'G1'" := grd_un_op : algebra_scope.
Notation "'G/' x" := (grd_un_op _ x) : algebra_scope.
