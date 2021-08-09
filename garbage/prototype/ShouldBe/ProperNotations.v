From Coq Require Export
  Morphisms.
From DEZ.Is Require Export
  Proper.

Delimit Scope signature_scope with signature.

Open Scope signature_scope.

Notation "R '==>' S" := (respectful R S)
  (right associativity, at level 55) : signature_scope.
