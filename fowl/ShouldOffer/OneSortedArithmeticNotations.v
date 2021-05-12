From Maniunfold.Offers Require Export
  OneSortedArithmetic.
From Maniunfold.ShouldHave Require Export
  OneSortedArithmeticNotations.

Notation "x '-' y" := (sub _ _ x y) : ring_scope.
Notation "x '/' y" := (div _ _ x y) : ring_scope.

Notation "'_-_'" := (sub _ _) (only parsing) : ring_scope.
Notation "'_/_'" := (div _ _) (only parsing) : ring_scope.
