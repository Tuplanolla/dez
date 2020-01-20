From Coq Require Export
  Setoid Morphisms.
From Maniunfold.Is Require Export
  Proper.

Delimit Scope signature_scope with signature.

Open Scope signature_scope.

Notation "x '==>' y" := (respectful x y)
  (right associativity, at level 55) : signature_scope.
