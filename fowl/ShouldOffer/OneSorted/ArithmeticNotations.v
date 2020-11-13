From Maniunfold.Offers Require Export
  OneSorted.Arithmetic.
From Maniunfold.ShouldHave Require Export
  OneSorted.ArithmeticNotations.

Notation "x '-' y" := (sub _ _ x y) : ring_scope.
Notation "x '/' y" := (div _ _ x y) : ring_scope.

Notation "'_-_'" := (sub _ _) (only parsing) : ring_scope.
Notation "'_/_'" := (div _ _) (only parsing) : ring_scope.
