From Maniunfold.Has Require Export
  OneSorted.UnaryOperation
  TwoSorted.LeftAction TwoSorted.RightAction
  TwoSorted.LeftTorsion TwoSorted.RightTorsion.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '*' y" (at level 40, left associativity).
Reserved Notation "x '/' y" (at level 40, left associativity).

(** We do not open [l_mod_scope] or [r_mod_scope],
    because we do not want to favor one over the other.
    The same applies to [l_subgrp_scope] and [r_subgrp_scope]. *)

Declare Scope l_mod_scope.

Delimit Scope l_mod_scope with l_mod.

Notation "a '*' x" := (l_act a x) : l_mod_scope.
Notation "a '/' x" := (l_act a (un_op x)) : l_mod_scope.

Declare Scope r_mod_scope.

Delimit Scope r_mod_scope with r_mod.

Notation "x '*' a" := (r_act x a) : r_mod_scope.
Notation "x '/' a" := (r_act x (un_op a)) : r_mod_scope.

Declare Scope l_subgrp_scope.

Delimit Scope l_subgrp_scope with l_subgrp.

Notation "x '/' y" := (l_tor x y) : l_subgrp_scope.

Declare Scope r_subgrp_scope.

Delimit Scope r_subgrp_scope with r_subgrp.

Notation "x '/' y" := (r_tor x y) : r_subgrp_scope.
