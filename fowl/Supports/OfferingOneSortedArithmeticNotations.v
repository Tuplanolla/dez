From DEZ.Provides Require Import
  OneSortedArithmetic.
From DEZ.Supports Require Export
  OneSortedArithmeticNotations.

Notation "'_-_'" := (sub _ _) : ring_scope.
Notation "x '-' y" := (sub _ _ x y) : ring_scope.
Notation "'_/_'" := (div _ _) : ring_scope.
Notation "x '/' y" := (div _ _ x y) : ring_scope.
