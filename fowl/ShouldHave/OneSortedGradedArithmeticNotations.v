From Maniunfold.Has Require Export
  OneSortedGradedAddition OneSortedGradedZero OneSortedGradedNegation
  OneSortedGradedMultiplication OneSortedGradedOne
  OneSortedGradedReciprocation.

Declare Scope grd_ring_scope.

Delimit Scope grd_ring_scope with grd_ring.

Open Scope grd_ring_scope.

Notation "x '+' y" := (grd_add _ _ x y) : grd_ring_scope.
Notation "'0'" := grd_zero : grd_ring_scope.
Notation "'-' x" := (grd_neg _ x) : grd_ring_scope.
Notation "x '*' y" := (grd_mul _ _ x y) : grd_ring_scope.
Notation "'1'" := grd_one : grd_ring_scope.
Notation "'/' x" := (grd_recip _ x) : grd_ring_scope.

Notation "'_+_'" := (grd_add _ _) (only parsing) : grd_ring_scope.
Notation "'-_'" := (grd_neg _) (only parsing) : grd_ring_scope.
Notation "'_*_'" := (grd_mul _ _) (only parsing) : grd_ring_scope.
Notation "'/_'" := (grd_recip _) (only parsing) : grd_ring_scope.
