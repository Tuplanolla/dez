From Maniunfold.Has Require Export
  OneSortedUnaryOperation
  TwoSortedLeftAction TwoSortedRightAction
  TwoSortedLeftTorsion TwoSortedRightTorsion.

(** We do not open [l_mod_scope] or [r_mod_scope],
    because we do not want to favor one over the other.
    The same applies to [l_subgrp_scope] and [r_subgrp_scope]. *)

Declare Scope l_mod_scope.

Delimit Scope l_mod_scope with l_mod.

Notation "a '*' x" := (l_act a x) : l_mod_scope.
Notation "a '/' x" := (l_act a (un_op x)) : l_mod_scope.

Notation "'_*_'" := l_act (only parsing) : l_mod_scope.
Notation "'_/_'" := (fun a x : _ => l_act a (un_op x))
  (only parsing) : l_mod_scope.

Declare Scope r_mod_scope.

Delimit Scope r_mod_scope with r_mod.

Notation "x '*' a" := (r_act x a) : r_mod_scope.
Notation "x '/' a" := (r_act x (un_op a)) : r_mod_scope.

Notation "'_*_'" := r_act (only parsing) : r_mod_scope.
Notation "'_/_'" := (fun x a : _ => r_act x (un_op a))
  (only parsing) : r_mod_scope.

Declare Scope l_subgrp_scope.

Delimit Scope l_subgrp_scope with l_subgrp.

Notation "x '/' y" := (l_tor x y) : l_subgrp_scope.

Notation "'_/_'" := l_tor (only parsing) : l_subgrp_scope.

Declare Scope r_subgrp_scope.

Delimit Scope r_subgrp_scope with r_subgrp.

Notation "x '/' y" := (r_tor x y) : r_subgrp_scope.

Notation "'_/_'" := r_tor (only parsing) : r_subgrp_scope.
